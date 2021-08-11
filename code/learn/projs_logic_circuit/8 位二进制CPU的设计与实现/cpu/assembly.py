# coding=utf-8

import pin

# 取指令，也就是我们的程序
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

# 支持的指令系统
INSTRUCTIONS = {
    # 以 操作数作为 key
    2 : {
        # 以指令作为 key
        MOV: {
            # 以（目的操作数、源操作数的寻址方式）作为 key
            (pin.AM_REG, pin.AM_INS) : [
                pin.DST_W | pin.SRC_OUT,
            ]
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

print(MOV)
print(bin(MOV))