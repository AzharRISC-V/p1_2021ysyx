# coding=utf-8

import os
import re
from sys import byteorder
import pin
import assembly as ASM

dirname = os.path.dirname(__file__)

inputfile = os.path.join(dirname, "program.asm")
outputfile = os.path.join(dirname, "program.bin")

# 注释的正则表达式
annotation = re.compile(r"(.*?);.*")

codes = []
marks = {}  # 字典，记录标记所对应的那行代码

# 二地址指令
OP2 = {
    "MOV" : ASM.MOV,
    "ADD" : ASM.ADD,
    "SUB" : ASM.SUB,
    "CMP" : ASM.CMP,
    "AND" : ASM.AND,
    "OR" : ASM.OR,
    "XOR" : ASM.XOR,
}

OP1 = {
    "INC" : ASM.INC,
    "DEC" : ASM.DEC,
    "NOT" : ASM.NOT,
    "JMP" : ASM.JMP,
    "JO" : ASM.JO,
    "JNO" : ASM.JNO,
    "JZ" : ASM.JZ,
    "JNZ" : ASM.JNZ,
    "JP" : ASM.JP,
    "JNP" : ASM.JNP,
    "PUSH" : ASM.PUSH,
    "POP" : ASM.POP,
    "CALL" : ASM.CALL,
}
OP0 = {
    "NOP" : ASM.NOP,
    "RET" : ASM.RET,
    "HLT" : ASM.HLT
}

OP2SET = set(OP2.values())
OP1SET = set(OP1.values())
OP0SET = set(OP0.values())

REGISTERS = {
    "A": pin.A,
    "B": pin.B,
    "C": pin.C,
    "D": pin.D,
    "SS": pin.SS,
    "SP": pin.SP,
    "CS": pin.CS,
}

class Code(object):

    # 代码类型：代码、标签
    TYPE_CODE = 1
    TYPE_LABEL = 2

    def __init__(self, number, source: str):
        self.number = number    # 行号
        self.source = source.upper()    # 源代码
        self.op = None      # 操作码
        self.dst = None     # 目的操作数
        self.src = None     # 源操作数
        self.type = self.TYPE_CODE  # 代码类型
        self.name:str = None    # 标签名称
        self.index = 0      # 代码所在的序号，去掉空行和标记以后的按顺序递增的编号，eg: 0, 1, ...
        self.prepare_source()

    def __repr__(self):
        return f"[{self.number}] - {self.source}"
    
    # 返回操纵码
    def get_op(self):
        if self.op in OP2:
            return OP2[self.op]
        if self.op in OP1:
            return OP1[self.op]
        if self.op in OP0:
            return OP0[self.op]
        raise SyntaxError(self)
    
    # 返回：寻址方式, 寄存器编号或立即数
    def get_am(self, addr):
        global marks

        if not addr:
            return None, None       # None 是空值，判断： if a is None, if a is not None
        
        if addr in marks:
            return pin.AM_INS, marks[addr].index * 3    # 取出标签所在的代码的序号，汇编指令的顺序编号。乘3是因为3条一条汇编指令占3个字节

        if addr in REGISTERS:
            return pin.AM_REG, REGISTERS[addr]
        # 如果是 十进制数，则返回立即数
        if re.match(r'^[0-9]+$', addr):
            return pin.AM_INS, int(addr)
        # 如果是 十六进制数
        if re.match(r'^0X[0-9A-F]+$', addr):
            return pin.AM_INS, int(addr, 16)
        # [xx] 直接寻址 - 十进制
        match = re.match(r'^\[([0-9]+)\]$', addr)
        if match:
            return pin.AM_DIR, int(match.group(1))
        # [xx] 直接寻址 - 十六进制
        match = re.match(r'^\[(0X[0-9A-F]+)\]$', addr)
        if match:
            return pin.AM_DIR, int(match.group(1), 16)
        # [r] 间接寻址
        match = re.match(r'^\[(.+)\]$', addr)
        if match and match.group(1) in REGISTERS:
            return pin.AM_IND, REGISTERS[match.group(1)]

        raise SyntaxError(self)

    # 源码预处理
    def prepare_source(self):
        # 处理标签
        if self.source.endswith(":"):
            self.type = self.TYPE_LABEL
            self.name = self.source.strip(":")
            return

        # 用逗号分隔，最多有两部分，否则错误
        tup = self.source.split(",")
        if len(tup) > 2:
            raise SyntaxError(self)
        
        # 二地址指令
        if len(tup) == 2:
            self.src = tup[1].strip()
        
        # 按空格来分隔
        tup = re.split(r" +", tup[0])
        if len(tup) > 2:
            raise SyntaxError(self)
        elif len(tup) == 2:
            self.dst = tup[1].strip()
            self.op = tup[0].strip()
        elif len(tup) == 1:
            self.op = tup[0].strip()
        else:
            raise SyntaxError(self)
        
        # 一地址或零地址指令

    # 返回编译后的数据
    def compile_code(self):
        op = self.get_op()
        amd,dst = self.get_am(self.dst)
        ams,src = self.get_am(self.src)

        # 如果是二地址指令，但寻址方式不支持时，报错
        if src is not None and (amd, ams) not in ASM.INSTRUCTIONS[2][op]:
            raise SyntaxError(self)
        # 如果是一地址指令，也判断寻址方式是否支持
        if src is None and dst is not None and amd not in ASM.INSTRUCTIONS[1][op]:
            raise SyntaxError(self)
        # 如果是一地址指令，判断op是否支持
        if src is None and dst is None and op not in ASM.INSTRUCTIONS[0]:
            raise SyntaxError(self)

        # 如果是 None，则处理成 0
        # or：从左到右计算表达式，返回第一个为真的值
        # and：从左到右计算表达式，返回第一个为假的值
        # dst or 0 : 当 dst 是 None 时，返回 0; 当 dst 不是 None 时，返回 dst 的值
        amd = amd or 0
        ams = ams or 0
        dst = dst or 0
        src = src or 0

        if op in OP2SET:
            ir = op | (amd << 2) | ams
        elif op in OP1SET:
            ir = op | amd
        else:
            ir = op
        
        return [ir, dst, src]

class SyntaxError(Exception):

    def __init__(self, code: Code, *args: object, **kwargs):
        super().__init__(*args, **kwargs)
        self.code = code


def compile_program():
    global codes
    global marks        # 字典，<name,code>，记录了<标签名称字符串，代码数据>
    
    with open(inputfile, encoding="utf8") as file:
        lines = file.readlines()
    
    for index, line in enumerate(lines):
        # 去掉两端空格
        source = line.strip()
        # 去掉注释
        if ";" in source:
            match = annotation.match(source)
            source = match.group(1)
            source = source.strip() # 继续去掉空格

        # 如果内容为空，则跳过这一行
        if not source:
            continue

        code = Code(index + 1, source)
        codes.append(code)

    # 手动在末尾添加一行代码，是为了处理末尾有一个标签的问题。
    code = Code(index + 2, "HLT")
    codes.append(code)
    
    # 从后往前重新处理
    result = []
    current = None  # 当前行置空
    for var in range(len(codes) - 1, -1, -1):   # 从 [n-1, n-2, ..., 0], -1)
        code = codes[var]
        if code.type == Code.TYPE_CODE:
            current = code
            result.insert(0, code)  # 插入头部
            continue
        if code.type == Code.TYPE_LABEL:
             marks[code.name] = current # 记录的是标签后的指令内容
             continue
        # 否则是语法错误
        raise SyntaxError(code)

    # 更新代码索引
    for index, var in enumerate(result):
        var.index = index
    
    with open(outputfile, "wb") as file:
        for code in result:
            values = code.compile_code()
            for value in values:
                result = value.to_bytes(1, byteorder = "little")
                file.write(result)

def main():
    # compile_program()
    try:
        compile_program()
    except SyntaxError as e:
        print(f"Syntax error at {e.code}")
        return
    
    print("User program compile finished!")

if __name__ == "__main__":
    main()