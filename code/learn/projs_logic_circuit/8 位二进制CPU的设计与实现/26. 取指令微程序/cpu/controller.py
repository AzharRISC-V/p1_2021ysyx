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

# 用 ASM.FETCH 来填充
for addr in range(0x10000):
    ir = addr >> 8              # bit[15:8]
    psw = (addr >> 4) & 0xF     # bit[7:4]
    cyc = addr & 0xF            # bit[3:0]

    if cyc < len(ASM.FETCH):
        micro[addr] = ASM.FETCH[cyc]

# 写入文件
with open(filename, "wb") as file:
    for var in micro:
        value = var.to_bytes(4, byteorder="little")
        file.write(value)

print("Compile micro instruction finished!")