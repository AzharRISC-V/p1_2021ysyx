
`timescale 1ns / 1ps

// 常用的常数

// 寄存器配置
`define ERG_BITS            64              // 寄存器位数
`define REG_BUS             63:0            // 寄存器总线
`define REG_ADDR_BITS       5               // 寄存器地址位数
`define REG_ADDR_BUS        4:0             // 寄存器地址总线
`define REG_NUM             32              // 寄存器个数
`define REG_ZERO            64'd0           // 寄存器数值0

// 指令配置
`define INST_BITS           32              // 指令位数
`define INST_BUS            31:0            // 指令总线

// RAM配置(4KB)
`define RAM_DATA_BITS       32              // RAM数据位数
`define RAM_DATA_BUS        31:0            // RAM数据总线
`define RAM_ADDR_BITS       12              // RAM地址位数
`define RAM_ADDR_BUS        11:0            // RAM地址总线
`define RAM_DATA_ZERO       32'd0           // RAM数据0
`define RAM_SIZE_BUS        4095:0          // RAM单元数总线

// ROM配置(4KB)
`define ROM_DATA_BITS       32              // ROM数据位数
`define ROM_DATA_BUS        31:0            // ROM数据总线
`define ROM_ADDR_BITS       12              // ROM地址位数
`define ROM_ADDR_BUS        11:0            // ROM地址总线
`define ROM_DATA_ZERO       32'd0           // ROM数据0

// 给定的指令
`define INST_ECALL          32'h0000_0073   // ecall 指令
`define INST_EBREAK         32'h0010_0073   // ebreak 指令

// opcode，用于指令译码
`define OPCODE_LUI          7'b0110111
`define OPCODE_AUIPC        7'b0010111
`define OPCODE_JAL          7'b1101111
`define OPCODE_JALR         7'b1100111
`define OPCODE_B            7'b1100011
`define OPCODE_L            7'b0000011
`define OPCODE_S            7'b0100011
`define OPCODE_I            7'b0010011
`define OPCODE_R            7'b0110011
`define OPCODE_FENCE        7'b0001111      // 同步
`define OPCODE_ENV          7'b1110011      // 环境
`define OPCODE_CSR          7'b1110011

// 某个opcode对应的 funct3，用于指令译码
// 若还不能区分，手动判断 funct7
`define FUNCT3_B_BEQ        3'b000
`define FUNCT3_B_BNE        3'b001
`define FUNCT3_B_BLT        3'b100
`define FUNCT3_B_BGE        3'b101
`define FUNCT3_B_BLTU       3'b110
`define FUNCT3_B_BGEU       3'b111
`define FUNCT3_L_LB         3'b000
`define FUNCT3_L_LH         3'b001
`define FUNCT3_L_LW         3'b010
`define FUNCT3_L_LBU        3'b100
`define FUNCT3_L_LHU        3'b101
`define FUNCT3_I_ADDI       3'b000
`define FUNCT3_I_SLTI       3'b010
`define FUNCT3_I_SLTIU      3'b011
`define FUNCT3_I_XORI       3'b100
`define FUNCT3_I_ORI        3'b110
`define FUNCT3_I_ANDI       3'b111
`define FUNCT3_I_SLLI       3'b001
`define FUNCT3_I_SRLI       3'b101
`define FUNCT3_I_SRAI       3'b101
`define FUNCT3_R_ADD        3'b000
`define FUNCT3_R_SUB        3'b000
`define FUNCT3_R_SLL        3'b001
`define FUNCT3_R_SLT        3'b010
`define FUNCT3_R_SLTU       3'b011
`define FUNCT3_R_XOR        3'b100
`define FUNCT3_R_SRL        3'b101
`define FUNCT3_R_SRA        3'b101
`define FUNCT3_R_OR         3'b110
`define FUNCT3_R_AND        3'b111
`define FUNCT3_FENCE_FENCE  3'b000
`define FUNCT3_FENCE_FENCEI 3'b001
`define FUNCT3_CSR_RW       3'b001
`define FUNCT3_CSR_RS       3'b010
`define FUNCT3_CSR_RC       3'b011
`define FUNCT3_CSR_RWI      3'b101
`define FUNCT3_CSR_RSI      3'b110
`define FUNCT3_CSR_RCI      3'b111
