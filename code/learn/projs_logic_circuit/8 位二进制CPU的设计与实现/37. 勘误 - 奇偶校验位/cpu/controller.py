# coding=utf-8

# 微控制器

import os
import pin
import assembly as ASM

dirname = os.path.dirname(__file__)
filename = os.path.join(dirname, "micro.bin")

# ROM 中存放微指令
# ROM 大小：2^16 = 64K，单位是 32bit。

# 填充 HLT 指令
micro = [pin.HLT for _ in range(0x10000)]

# 所有的条件转移指令
CJMPS = {ASM.JO, ASM.JNO, ASM.JZ, ASM.JNZ, ASM.JP, ASM.JNP}

def compile_addr2(addr, ir, psw, index):
    global micro

    op = ir & 0xF0
    amd = (ir >> 2) & 3     # 目的操作数寻址方式
    ams = ir & 3            # 源操作数寻址方式

    # 查找指令是否存在？
    INST = ASM.INSTRUCTIONS[2]
    if op not in INST:
        micro[addr] = pin.CYC
        return
    
    # 查找该指令的寻址方式是否存在？
    am = (amd, ams)
    if am not in INST[op]:
        micro[addr] = pin.CYC
        return
    
    # 得到具体执行的指令
    EXEC = INST[op][am]
    if index < len(EXEC):
        micro[addr] = EXEC[index]
    else:
        micro[addr] = pin.CYC

# 处理条件转移指令
# exec: 微控制程序
# op: 具体JMP类型
# psw: 程序状态字（bit0:溢出，bit1:零，bit2:奇偶，bit3:保留
# 返回值：若满足条件则返回传入的微控制程序，若不满足，则返回一个 CYC 程序，执行下一条用户指令。
def get_condition_jump(exec, op, psw):
    overflow = psw & 1
    zero = psw & 2
    parity = psw & 4

    if op == ASM.JO and overflow:
        return exec
    if op == ASM.JNO and not overflow:
        return exec
    if op == ASM.JZ and zero:
        return exec
    if op == ASM.JNZ and not zero:
        return exec
    if op == ASM.JP and parity:
        return exec
    if op == ASM.JNP and not parity:
        return exec
    return [pin.CYC]    # 相当于 ASM.NOP

# 处理中断跳转请求
def get_interrupt(exec, op, psw):
    interrupt = psw & 8     # 1000
    if interrupt:   # 如果中断允许，则执行跳转请求
        return exec
    return [pin.CYC]    # 否则，清零，执行下一条指令

def compile_addr1(addr, ir, psw, index):

    global micro
    global CJMPS

    op = ir & 0xFC
    amd = ir & 3     # 目的操作数寻址方式
    
    # 查找指令是否存在？
    INST = ASM.INSTRUCTIONS[1]
    if op not in INST:
        micro[addr] = pin.CYC
        return
    
    # 查找该指令的寻址方式是否存在？
    if amd not in INST[op]:
        micro[addr] = pin.CYC
        return
    
    # 得到具体执行的指令
    EXEC = INST[op][amd]

    # 处理条件转移指令
    if op in CJMPS:
        EXEC = get_condition_jump(EXEC, op, psw)

    # 处理中断转移请求
    if op == ASM.INT:
        EXEC = get_interrupt(EXEC, op, psw)
    
    if index < len(EXEC):
        micro[addr] = EXEC[index]
    else:
        micro[addr] = pin.CYC
    
def compile_addr0(addr, ir, psw, index):
    global micro

    op = ir

    # 查找指令是否存在？
    INST = ASM.INSTRUCTIONS[0]
    if op not in INST:
        micro[addr] = pin.CYC
        return
    
    # 得到具体执行的指令
    EXEC = INST[op]
    if index < len(EXEC):
        micro[addr] = EXEC[index]
    else:
        micro[addr] = pin.CYC

# 用 ASM.FETCH 来填充
for addr in range(0x10000):

    # 16bit: 8bit IR | 4bit PSW | 4bit CYC

    ir = addr >> 8              # bit[15:8]，汇编指令
    psw = (addr >> 4) & 0xF     # bit[7:4]，程序状态字
    cyc = addr & 0xF            # bit[3:0]，微程序周期

    # 取值阶段，6个微操作
    if cyc < len(ASM.FETCH):
        micro[addr] = ASM.FETCH[cyc]
        continue

    # 译码阶段，根据 二地址、一地址、零地址的不同类型分别译码，产生 CU 信号
    addr2 = ir & pin.ADDR2   # 二地址指令
    addr1 = ir & pin.ADDR1

    index = cyc - len(ASM.FETCH)

    if addr2:
        compile_addr2(addr, ir, psw, index)
    elif addr1:
        compile_addr1(addr, ir, psw, index)
    else:
        compile_addr0(addr, ir, psw, index)


# 写入文件
with open(filename, "wb") as file:
    for var in micro:
        value = var.to_bytes(4, byteorder="little")
        file.write(value)

print("Compile micro instruction finished!")