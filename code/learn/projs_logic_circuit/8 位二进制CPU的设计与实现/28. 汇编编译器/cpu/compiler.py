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

# 二地址指令
OP2 = {
    "MOV" : ASM.MOV
}

OP1 = {
}
OP0 = {
    "NOP" : ASM.NOP,
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
}

class Code(object):

    def __init__(self, number, source):
        self.number = number    # 行号
        self.source = source.upper()    # 源代码
        self.op = None      # 操作码
        self.dst = None     # 目的操作数
        self.src = None     # 源操作数
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
        if not addr:
            return 0,0
        if addr in REGISTERS:
            return pin.AM_REG, REGISTERS[addr]
        # 如果是 十进制数，则返回立即数
        if re.match(r'^[0-9]+$', addr):
            return pin.AM_INS, int(addr)
        # 如果是 十六进制数
        if re.match(r'^0X[0-9A-F]+$', addr):
            return pin.AM_INS, int(addr, 16)
        # 其他寻址方式暂不支持
        raise SyntaxError(self)

    def prepare_source(self):
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
    
    with open(outputfile, "wb") as file:
        for code in codes:
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
    
    print("Compile finished!")

if __name__ == "__main__":
    main()