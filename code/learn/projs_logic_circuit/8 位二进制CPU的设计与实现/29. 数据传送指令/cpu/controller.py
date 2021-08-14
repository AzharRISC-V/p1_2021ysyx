# coding=utf-8

import os
import pin
import assembly as ASM

dirname = os.path.dirname(__file__)
filename = os.path.join(dirname, "micro.bin")

# ROM 中存放微指令
# ROM 大小：2^16 = 64K，单位是 32bit。

# 填充 HLT 指令
micro = [pin.HLT for _ in range(0x10000)]


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

def compile_addr1(addr, ir, psw, index):
    pass
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
    ir = addr >> 8              # bit[15:8]
    psw = (addr >> 4) & 0xF     # bit[7:4]
    cyc = addr & 0xF            # bit[3:0]

    # 取值阶段，6个微操作
    if cyc < len(ASM.FETCH):
        micro[addr] = ASM.FETCH[cyc]
        continue

    # 译码阶段，根据 二地址、一地址、零地址的不同类型分别译码，产生 CU 信号
    addr2 = ir & (1 << 7)   # 二地址指令
    addr1 = ir & (1 << 6)

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