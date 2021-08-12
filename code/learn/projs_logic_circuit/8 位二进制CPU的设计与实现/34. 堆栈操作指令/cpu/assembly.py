# coding=utf-8

import pin

# 取指令微程序
FETCH = [
    pin.PC_OUT | pin.MAR_IN,                # PC 数据送入 MAR，给出 RAM地址
    pin.RAM_OUT | pin.IR_IN | pin.PC_INC,   # 取 RAM 数据并存入 IR， PC + 1
    
    pin.PC_OUT | pin.MAR_IN,                # PC 数据送入 MAR，给出 RAM地址
    pin.RAM_OUT | pin.DST_IN | pin.PC_INC,  # 取 RAM 数据并存入 DST， PC + 1
    
    pin.PC_OUT | pin.MAR_IN,                # PC 数据送入 MAR，给出 RAM地址
    pin.RAM_OUT | pin.SRC_IN | pin.PC_INC,  # 取 RAM 数据并存入 SRC， PC + 1
]

# 汇编指令(是一个 8bit 的数)

## 二地址，有3bit可编码，最多8种指令
MOV = (0 << pin.ADDR2_SHIFT) | pin.ADDR2
ADD = (1 << pin.ADDR2_SHIFT) | pin.ADDR2
SUB = (2 << pin.ADDR2_SHIFT) | pin.ADDR2

CMP = (3 << pin.ADDR2_SHIFT) | pin.ADDR2        # 与 SUB 类似，只更新状态字，不输出结果
AND = (4 << pin.ADDR2_SHIFT) | pin.ADDR2 
OR = (5 << pin.ADDR2_SHIFT) | pin.ADDR2 
XOR = (6 << pin.ADDR2_SHIFT) | pin.ADDR2 

## 一地址，有4bit可编码，最多16种指令
INC = (0 << pin.ADDR1_SHIFT) | pin.ADDR1
DEC = (1 << pin.ADDR1_SHIFT) | pin.ADDR1

NOT = (2 << pin.ADDR1_SHIFT) | pin.ADDR1

JMP = (3 << pin.ADDR1_SHIFT) | pin.ADDR1
JO = (4 << pin.ADDR1_SHIFT) | pin.ADDR1
JNO = (5 << pin.ADDR1_SHIFT) | pin.ADDR1
JZ = (6 << pin.ADDR1_SHIFT) | pin.ADDR1
JNZ = (7 << pin.ADDR1_SHIFT) | pin.ADDR1
JP = (8 << pin.ADDR1_SHIFT) | pin.ADDR1
JNP = (9 << pin.ADDR1_SHIFT) | pin.ADDR1

PUSH = (10 << pin.ADDR1_SHIFT) | pin.ADDR1
POP = (11 << pin.ADDR1_SHIFT) | pin.ADDR1


NOP = 0
HLT = 0x3F

# 支持的指令微程序
INSTRUCTIONS = {
    # 以 操作数作为 key
    2 : {
        # 以指令作为 key
        MOV: {
            # 以（目的操作数、源操作数的寻址方式）作为 key
            # 1. MOV A, 3
            (pin.AM_REG, pin.AM_INS) : [
                pin.DST_W | pin.SRC_OUT,        # SRC_OUT: 将SRC数据送到总线上，常用于立即数寻址。
            ],
            # 2. MOV A, B
            (pin.AM_REG, pin.AM_REG) : [
                pin.DST_W | pin.SRC_R           # SRC_R: 将SRC表示的那个寄存器的数送到总线，常用于寄存器寻址
            ],
            # 3. MOV A, [3]
            (pin.AM_REG, pin.AM_DIR) : [
                pin.SRC_OUT | pin.MAR_IN,       # 源数据是立即数，该数送入内存地址寄存器
                pin.DST_W | pin.RAM_OUT,        # 将内存数据送入总线，目的操作数写入
            ],
            # 4. MOV A, [B]
            (pin.AM_REG, pin.AM_IND) : [
                pin.SRC_R | pin.MAR_IN,         # 源数据是寄存器，该寄存器内容送入内存地址寄存器
                pin.DST_W | pin.RAM_OUT,        # 将内存数据送入总线，目的操作数写入
            ],
            # 5. MOV [3], 4
            (pin.AM_DIR, pin.AM_INS): [
                pin.DST_OUT | pin.MAR_IN,       # 将 DST 中立即数，送入 MAR
                pin.RAM_IN | pin.SRC_OUT        # 将 SRC 中立即数，写入 RAM
            ],
            # 6. MOV [3], A
            (pin.AM_DIR, pin.AM_REG): [
                pin.DST_OUT | pin.MAR_IN,       # 将 DST 中立即数，送入 MAR
                pin.RAM_IN | pin.SRC_R          # 将 SRC 中寄存器值，写入 RAM
            ],
            # 7. MOV [3], [4]
            (pin.AM_DIR, pin.AM_DIR): [
                pin.SRC_OUT | pin.MAR_IN,       # 将 SRC 中立即数，送入MAR
                pin.RAM_OUT | pin.T1_IN,        # 将 RAM 中数据，送入 T1
                pin.DST_OUT | pin.MAR_IN,       # 将 DST 中立即数，送入MAR
                pin.RAM_IN | pin.T1_OUT,        # 将 T1 送入 RAM
            ],
            # 8. MOV [3], [A]
            (pin.AM_DIR, pin.AM_IND): [
                pin.SRC_R | pin.MAR_IN,         # 将 SRC 中寄存器的值，送入MAR
                pin.RAM_OUT | pin.T1_IN,        # 将 RAM 中数据，送入 T1
                pin.DST_OUT | pin.MAR_IN,       # 将 DST 中立即数，送入MAR
                pin.RAM_IN | pin.T1_OUT,        # 将 T1 送入 RAM
            ],
            # 9. MOV [A], 3
            (pin.AM_IND, pin.AM_INS): [
                pin.DST_R | pin.MAR_IN,         # 将 DST 所在寄存器的值，送入 MAR
                pin.RAM_IN | pin.SRC_OUT        # 将 SRC中立即数，送入 RAM
            ],
            # 10. MOV [A], B
            (pin.AM_IND, pin.AM_REG): [
                pin.DST_R | pin.MAR_IN,         # 将 DST 所在寄存器的值，送入 MAR
                pin.RAM_IN | pin.SRC_R          # 将 SRC 所在寄存器的值，送入 RAM
            ],
            # 11. MOV [A], [4]
            (pin.AM_IND, pin.AM_DIR): [
                pin.SRC_OUT | pin.MAR_IN,       # 将 SRC 中立即数，送入MAR
                pin.RAM_OUT | pin.T1_IN,        # 将 RAM 中数据，送入 T1
                pin.DST_R | pin.MAR_IN,         # 将 DST 所在寄存器的值，送入MAR
                pin.RAM_IN | pin.T1_OUT,        # 将 T1 送入 RAM
            ],
            # 12. MOV [A], [B]
            (pin.AM_IND, pin.AM_IND): [
                pin.SRC_R | pin.MAR_IN,         # 将 SRC 中寄存器的值，送入MAR
                pin.RAM_OUT | pin.T1_IN,        # 将 RAM 中数据，送入 T1
                pin.DST_R | pin.MAR_IN,         # 将 DST 所在寄存器的值，送入MAR
                pin.RAM_IN | pin.T1_OUT,        # 将 T1 送入 RAM
            ],
        },
        ADD: {
            # 以（目的操作数、源操作数的寻址方式）作为 key
            # 1. ADD A, 3
            (pin.AM_REG, pin.AM_INS) : [
                pin.DST_R | pin.A_IN,           # 目的操作数（寄存器的值）送入 A
                pin.SRC_OUT | pin.B_IN,         # 源操作数（立即数）送入 B
                pin.OP_ADD | pin.ALU_OUT | pin.DST_W | pin.ALU_PSW,
            ],
            # 2. ADD A, B
            (pin.AM_REG, pin.AM_REG) : [
                pin.DST_R | pin.A_IN,           # 目的操作数（寄存器的值）送入 A
                pin.SRC_R | pin.B_IN,           # 源操作数（寄存器的值）送入 B
                pin.OP_ADD | pin.ALU_OUT | pin.DST_W | pin.ALU_PSW,
            ],
        },
        SUB: {
            # 以（目的操作数、源操作数的寻址方式）作为 key
            # 1. ADD A, 3
            (pin.AM_REG, pin.AM_INS) : [
                pin.DST_R | pin.A_IN,           # 目的操作数（寄存器的值）送入 A
                pin.SRC_OUT | pin.B_IN,         # 源操作数（立即数）送入 B
                pin.OP_SUB | pin.ALU_OUT | pin.DST_W | pin.ALU_PSW,
            ],
            # 2. ADD A, B
            (pin.AM_REG, pin.AM_REG) : [
                pin.DST_R | pin.A_IN,           # 目的操作数（寄存器的值）送入 A
                pin.SRC_R | pin.B_IN,           # 源操作数（寄存器的值）送入 B
                pin.OP_SUB | pin.ALU_OUT | pin.DST_W | pin.ALU_PSW,
            ],
        },
        CMP: {
            # 1. CMP A, 3
            (pin.AM_REG, pin.AM_INS) : [
                pin.DST_R | pin.A_IN,           # 目的操作数（寄存器的值）送入 A
                pin.SRC_OUT | pin.B_IN,         # 源操作数（立即数）送入 B
                pin.OP_SUB | pin.ALU_PSW,
            ],
            # 2. CMP A, B
            (pin.AM_REG, pin.AM_REG) : [
                pin.DST_R | pin.A_IN,           # 目的操作数（寄存器的值）送入 A
                pin.SRC_R | pin.B_IN,           # 源操作数（寄存器的值）送入 B
                pin.OP_SUB | pin.ALU_PSW,
            ],
        },
        AND: {
            # 1. AND A, 3
            (pin.AM_REG, pin.AM_INS) : [
                pin.DST_R | pin.A_IN,           # 目的操作数（寄存器的值）送入 A
                pin.SRC_OUT | pin.B_IN,         # 源操作数（立即数）送入 B
                pin.OP_AND | pin.ALU_OUT | pin.DST_W | pin.ALU_PSW,
            ],
            # 2. AND A, B
            (pin.AM_REG, pin.AM_REG) : [
                pin.DST_R | pin.A_IN,           # 目的操作数（寄存器的值）送入 A
                pin.SRC_R | pin.B_IN,           # 源操作数（寄存器的值）送入 B
                pin.OP_AND | pin.ALU_OUT | pin.DST_W | pin.ALU_PSW,
            ],
        },
        OR: {
            # 1. OR A, 3
            (pin.AM_REG, pin.AM_INS) : [
                pin.DST_R | pin.A_IN,           # 目的操作数（寄存器的值）送入 A
                pin.SRC_OUT | pin.B_IN,         # 源操作数（立即数）送入 B
                pin.OP_OR | pin.ALU_OUT | pin.DST_W | pin.ALU_PSW,
            ],
            # 2. OR A, B
            (pin.AM_REG, pin.AM_REG) : [
                pin.DST_R | pin.A_IN,           # 目的操作数（寄存器的值）送入 A
                pin.SRC_R | pin.B_IN,           # 源操作数（寄存器的值）送入 B
                pin.OP_OR | pin.ALU_OUT | pin.DST_W | pin.ALU_PSW,
            ],
        },
        XOR: {
            # 1. XOR A, 3
            (pin.AM_REG, pin.AM_INS) : [
                pin.DST_R | pin.A_IN,           # 目的操作数（寄存器的值）送入 A
                pin.SRC_OUT | pin.B_IN,         # 源操作数（立即数）送入 B
                pin.OP_XOR | pin.ALU_OUT | pin.DST_W | pin.ALU_PSW,
            ],
            # 2. XOR A, B
            (pin.AM_REG, pin.AM_REG) : [
                pin.DST_R | pin.A_IN,           # 目的操作数（寄存器的值）送入 A
                pin.SRC_R | pin.B_IN,           # 源操作数（寄存器的值）送入 B
                pin.OP_XOR | pin.ALU_OUT | pin.DST_W | pin.ALU_PSW,
            ],
        },
    },
    1 : {
        INC: {
            # 1. INC A
            (pin.AM_REG) : [
                pin.DST_R | pin.A_IN,
                pin.OP_INC | pin.ALU_OUT | pin.DST_W | pin.ALU_PSW,
            ],
        },
        DEC: {
            # 1. DEC A
            (pin.AM_REG) : [
                pin.DST_R | pin.A_IN,
                pin.OP_DEC | pin.ALU_OUT | pin.DST_W | pin.ALU_PSW,
            ],
        },
        NOT: {
            # 1. NOT A
            (pin.AM_REG) : [
                pin.DST_R | pin.A_IN,
                pin.OP_NOT | pin.ALU_OUT | pin.DST_W | pin.ALU_PSW,
            ],
        },
        JMP: {
            # 1. JMP 3
            (pin.AM_INS) : [
                pin.DST_OUT | pin.PC_IN,
            ],
        },
        JO: {
            # 1. JO 3
            (pin.AM_INS) : [
                pin.DST_OUT | pin.PC_IN,
            ],
        },
        JNO: {
            # 1. JO 3
            (pin.AM_INS) : [
                pin.DST_OUT | pin.PC_IN,
            ],
        },
        JZ: {
            # 1. JO 3
            (pin.AM_INS) : [
                pin.DST_OUT | pin.PC_IN,
            ],
        },
        JNZ: {
            # 1. JO 3
            (pin.AM_INS) : [
                pin.DST_OUT | pin.PC_IN,
            ],
        },
        JP: {
            # 1. JO 3
            (pin.AM_INS) : [
                pin.DST_OUT | pin.PC_IN,
            ],
        },
        JNP: {
            # 1. JO 3
            (pin.AM_INS) : [
                pin.DST_OUT | pin.PC_IN,
            ],
        },
        PUSH: {
            # 1. PUSH 3
            (pin.AM_INS) : [
                pin.SP_OUT | pin.A_IN,                  # A = SP
                pin.OP_DEC | pin.SP_IN | pin.ALU_OUT,   # SP = SP - 1
                pin.SP_OUT | pin.MAR_IN,                # MAR = SP
                pin.SS_OUT | pin.MSR_IN,                # MSR = 栈段寄存器的值，确定了栈段
                pin.DST_OUT | pin.RAM_IN,               # 目的立即数读取，并写入内存
                pin.CS_OUT | pin.MSR_IN,                # 段寄存器还原为代码段
            ],
            # 2. PUSH R
            (pin.AM_REG) : [
                pin.SP_OUT | pin.A_IN,                  # A = SP
                pin.OP_DEC | pin.SP_IN | pin.ALU_OUT,   # SP = SP - 1
                pin.SP_OUT | pin.MAR_IN,                # MAR = SP
                pin.SS_OUT | pin.MSR_IN,                # MSR = 栈段寄存器的值，确定了栈段
                pin.DST_R | pin.RAM_IN,                 # 目的寄存器读取，并写入内存
                pin.CS_OUT | pin.MSR_IN,                # 段寄存器还原为代码段
            ],
        },
        POP: {
            # 1. POP R
            (pin.AM_REG) : [
                pin.SP_OUT | pin.MAR_IN,                # MAR = SP
                pin.SS_OUT | pin.MSR_IN,                # MSR = 栈段寄存器的值，确定了栈段
                pin.DST_W | pin.RAM_OUT,                # 读取内存，写入目的寄存器读取。注意，目的寄存器不能是 A，因为下面会用到 A
                pin.SP_OUT | pin.A_IN,                  # A = SP
                pin.OP_INC | pin.SP_IN | pin.ALU_OUT,   # SP = SP + 1
                pin.CS_OUT | pin.MSR_IN,                # 段寄存器还原为代码段
            ],
        },
    },
    0 : {
        NOP : [
            pin.CYC,
        ],
        HLT : [
            pin.HLT,
        ]
    }
}