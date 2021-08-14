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

MOV = (0 << pin.ADDR2_SHIFT) | pin.ADDR2
ADD = (1 << pin.ADDR2_SHIFT) | pin.ADDR2

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
        }
    },
    1 : {},
    0 : {
        NOP : [
            pin.CYC,
        ],
        HLT : [
            pin.HLT,
        ]
    }
}