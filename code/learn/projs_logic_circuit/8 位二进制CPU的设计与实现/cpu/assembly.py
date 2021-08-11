# coding=utf-8

import pin

FETCH = [
    pin.PC_OUT | pin.MAR_IN,                # PC 数据送入 MAR，给出 RAM地址
    pin.RAM_OUT | pin.IR_IN | pin.PC_INC,   # 取 RAM 数据并存入 IR， PC + 1
    
    pin.PC_OUT | pin.MAR_IN,                # PC 数据送入 MAR，给出 RAM地址
    pin.RAM_OUT | pin.DST_IN | pin.PC_INC,  # 取 RAM 数据并存入 DST， PC + 1
    
    pin.PC_OUT | pin.MAR_IN,                # PC 数据送入 MAR，给出 RAM地址
    pin.RAM_OUT | pin.SRC_IN | pin.PC_INC,  # 取 RAM 数据并存入 SRC， PC + 1

    pin.HLT
]