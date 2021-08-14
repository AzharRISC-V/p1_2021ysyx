# coding=utf-8

MSR = 1
MAR = 2
MDR = 3
RAM = 4
IR = 5
DST = 6
SRC = 7
A = 8
B = 9
C = 10
D = 11
DI = 12
SI = 13
SP = 14
BP = 15
CS = 16
DS = 17
SS = 18
ES = 19
VEC = 20
T1 = 21
T2 = 22

MSR_OUT = MSR
MAR_OUT = MAR
MDR_OUT = MDR
RAM_OUT = RAM
IR_OUT = IR
DST_OUT = DST       # 将DST数据送入总线上
SRC_OUT = SRC       # 将SRC数据送到总线上，常用于立即数寻址。
A_OUT = A           # 将A数据送入总线上
B_OUT = B
C_OUT = C
D_OUT = D
DI_OUT = DI
SI_OUT = SI
SP_OUT = SP
BP_OUT = BP
CS_OUT = CS
DS_OUT = DS
SS_OUT = SS
ES_OUT = ES
VEC_OUT = VEC
T1_OUT = T1
T2_OUT = T2

_DST_SHIFT = 5

MSR_IN = MSR << _DST_SHIFT
MAR_IN = MAR << _DST_SHIFT
MDR_IN = MDR << _DST_SHIFT
RAM_IN = RAM << _DST_SHIFT
IR_IN = IR << _DST_SHIFT
DST_IN = DST << _DST_SHIFT
SRC_IN = SRC << _DST_SHIFT
A_IN = A << _DST_SHIFT
B_IN = B << _DST_SHIFT
C_IN = C << _DST_SHIFT
D_IN = D << _DST_SHIFT
DI_IN = DI << _DST_SHIFT
SI_IN = SI << _DST_SHIFT
SP_IN = SP << _DST_SHIFT
BP_IN = BP << _DST_SHIFT
CS_IN = CS << _DST_SHIFT
DS_IN = DS << _DST_SHIFT
SS_IN = SS << _DST_SHIFT
ES_IN = ES << _DST_SHIFT
VEC_IN = VEC << _DST_SHIFT
T1_IN = T1 << _DST_SHIFT
T2_IN = T2 << _DST_SHIFT

SRC_R = 2 ** 10         # 将SRC表示的那个寄存器的数送到总线，常用于寄存器寻址
SRC_W = 2 ** 11         # 将总线数据写入SRC表示的那个寄存器
DST_R = 2 ** 12         # 将DST表示的那个寄存器的数据送到总线
DST_W = 2 ** 13         # 将总线数据写入DST表示的那个寄存器

PC_WE = 2 ** 14
PC_CS = 2 ** 15
PC_EN = 2 ** 16

PC_OUT = PC_CS
PC_IN = PC_CS | PC_WE
PC_INC = PC_CS | PC_WE | PC_EN

_OP_SHIFT = 17

OP_ADD = 0 << _OP_SHIFT
OP_SUB = 1 << _OP_SHIFT
OP_INC = 2 << _OP_SHIFT
OP_DEC = 3 << _OP_SHIFT
OP_AND = 4 << _OP_SHIFT
OP_OR = 5 << _OP_SHIFT
OP_XOR = 6 << _OP_SHIFT
OP_NOT = 7 << _OP_SHIFT

ALU_OUT = 1 << 20       # ALU 结果送入总线
ALU_PSW = 1 << 21       # ALU 的 PSW 送出
ALU_INT_W = 1 << 22     # ALU 的 INT 写入位，置 1 则允许 设置或清除 中断， 置 0 则不允许修改
ALU_INT = 1 << 23       # ALU 的 INT 位，当 INT_W 为 1 时，允许修改。当 INT 为 0，表示允许中断发生，INT 为 1，表示不允许中断发生。

ALU_STI = ALU_INT_W                 # 开中断
ALU_CLI = ALU_INT_W | ALU_INT       # 关中断

CYC = 2 ** 30       # 使 微程序 的 指令周期 清零，相当于 NOP
HLT = 2 ** 31


# 二地址指令(2 Address)
ADDR2 = 1 << 7
ADDR2_SHIFT = 4     # 左移4位

# 一地址指令(1 Address)
ADDR1 = 1 << 6
ADDR1_SHIFT = 2     # 左移2位

# 四种寻址方式（AM：Address Mode)
AM_INS = 0
AM_REG = 1
AM_DIR = 2  # 直接寻址
AM_IND = 3  # 寄存器间接寻址
