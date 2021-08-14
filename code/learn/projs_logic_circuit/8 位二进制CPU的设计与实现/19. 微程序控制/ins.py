import os
from sys import byteorder

dirname = os.path.dirname(__file__)
filename = os.path.join(dirname, "ins.bin")

WE_A = 2 ** 0   # 1
CS_A = 2 ** 1   # 1x

WE_B = 2 ** 2   # 1xx
CS_B = 2 ** 3   # 1xxx

WE_C = 2 ** 4
CS_C = 2 ** 5

ALU_ADD = 0
ALU_SUB = 2 ** 6
ALU_OUT = 2 ** 7

WE_M = 2 ** 8
CS_M = 2 ** 9

WE_PC = 2 ** 10
EN_PC = 2 ** 11
CS_PC = 2 ** 12

HLT = 2 ** 15

# 微程序
micro = [
    # 将内存数据存入regA，PC+1
    CS_M | CS_A | WE_A | WE_PC | EN_PC | CS_PC,
    # 将内存数据存入regB，PC+1
    CS_M | CS_B | WE_B | WE_PC | EN_PC | CS_PC,
    # 将 ALU 结果存入regC
    ALU_SUB | ALU_OUT | CS_C | WE_C,
    # 将regC数据存入内存
    CS_C | WE_M | CS_M | WE_PC | EN_PC | CS_PC,
    HLT
]

with open(filename, "wb") as file:
    for value in micro:
        result = value.to_bytes(2, byteorder="little")
        file.write(result)
        print(value, result)
print("Finish compile!!")
# 将内存的数据存入 RegA: CS_M | CS_A | WE_A
# 将内存的数据存入 RegA, 并 PC+1 : CS_M | CS_A | WE_A | WE_PC
# print((CS_M | CS_A | WE_A).to_bytes(2, byteorder="big"))

# 注意，Logical Circuit 中读入文件都是按照 小端模式
# 我们设计的ROM是16bit，有大小端之分。

