
`timescale 1ns / 1ps

// 各种数据类型的总线
`define BYTE_BUS     7:0
`define HALF_BUS     15:0
`define WORD_BUS     31:0
`define DWORD_BUS    63:0

// 各种数据类型的0,z
`define DWORD_ZERO  64'd0
`define DWORD_HZ    64'hz
`define WORD_ZERO   32'd0
`define WORD_HZ     32'hz

// 零散定义
`define REG_BUS      63 : 0

// 内存布局：数据单元32bit，共64k个地址
`define RAM_DATA_ZERO   `WORD_ZERO
`define RAM_DATA_HZ     `WORD_HZ
`define RAM_DATA_BUS     31:0
`define RAM_ADDR_BUS     15:0
`define RAM_SIZE_BUS     65535:0
`define RAM_SIZE        65536

// 指令定义
`define INST_ADDI   8'h11
