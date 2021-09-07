
`timescale 1ns / 1ps

`define ZERO_WORD  64'h00000000_00000000
`define PC_START   64'h00000000_80000000  
// `define REG_BUS    63 : 0     
// `define INST_ADD   8'h11

`define AXI_ADDR_WIDTH      64
`define AXI_DATA_WIDTH      64
`define AXI_ID_WIDTH        4
`define AXI_USER_WIDTH      1

`define SIZE_B              2'b00
`define SIZE_H              2'b01
`define SIZE_W              2'b10
`define SIZE_D              2'b11

`define REQ_READ            1'b0
`define REQ_WRITE           1'b1

`define RISCV_PRIV_MODE_U   0
`define RISCV_PRIV_MODE_S   1
`define RISCV_PRIV_MODE_M   3


`define CLOCKS_PER_SECOND   64'd240_0000        // 每秒的clock数，约240万

`define BUS_8               7:0
`define BUS_16              15:0
`define BUS_32              31:0
`define BUS_64              63:0

// 指令状态机
`define STATE_BUS           3:0
`define STATE_NONE          4'd0
`define STATE_IF            4'd1
`define STATE_ID            4'd2
`define STATE_EX            4'd3
`define STATE_MEM           4'd4
`define STATE_WB            4'd5
`define STATE_CMT           4'd6

// CSR
`define BUS_CSR_ADDR        11 : 0          // CSR存储器地址

// CSR index in local memory
`define CSR_IDX_NONE        0
`define CSR_IDX_MSTATUS     1
`define CSR_IDX_MCYCLE      2

// 寄存器配置
`define REG_BITS            64              // 寄存器位数
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
`define ROM_SIZE_BUS        4095:0          // ROM单元数总线

// 已编码的指令
`define INST_ECALL          32'h0000_0073   // ecall 指令
`define INST_EBREAK         32'h0010_0073   // ebreak 指令

// 自定义的指令码
`define INST_ADD            8'h11

// inst-type
`define INST_R_TYPE         3'b001
`define INST_I_TYPE         3'b010
`define INST_S_TYPE         3'b011
`define INST_B_TYPE         3'b100
`define INST_U_TYPE         3'b101
`define INST_J_TYPE         3'b110


// opcode，用于指令译码
// RV32I
`define OPCODE_LUI          7'b0110111
`define OPCODE_AUIPC        7'b0010111
`define OPCODE_JAL          7'b1101111
`define OPCODE_JALR         7'b1100111
`define OPCODE_BEQ          7'b1100011
`define OPCODE_LB           7'b0000011
`define OPCODE_SB           7'b0100011
`define OPCODE_ADDI         7'b0010011
`define OPCODE_ADD          7'b0110011
`define OPCODE_FENCE        7'b0001111      // 同步
`define OPCODE_ENV          7'b1110011      // 环境
`define OPCODE_CSR          7'b1110011
// RV64I
`define OPCODE_ADDIW        7'b0011011
`define OPCODE_ADDW         7'b0111011

// 某个opcode对应的 funct3，用于指令译码
// 若还不能区分，手动判断 funct7

// RV32I
`define FUNCT3_BEQ          3'b000
`define FUNCT3_BNE          3'b001
`define FUNCT3_BLT          3'b100
`define FUNCT3_BGE          3'b101
`define FUNCT3_BLTU         3'b110
`define FUNCT3_BGEU         3'b111
`define FUNCT3_LB           3'b000
`define FUNCT3_LH           3'b001
`define FUNCT3_LW           3'b010
`define FUNCT3_LBU          3'b100
`define FUNCT3_LHU          3'b101
`define FUNCT3_SB           3'b000
`define FUNCT3_SH           3'b001
`define FUNCT3_SW           3'b010
`define FUNCT3_ADDI         3'b000
`define FUNCT3_SLTI         3'b010
`define FUNCT3_SLTIU        3'b011
`define FUNCT3_XORI         3'b100
`define FUNCT3_ORI          3'b110
`define FUNCT3_ANDI         3'b111
`define FUNCT3_SLLI         3'b001
`define FUNCT3_SRLI         3'b101
`define FUNCT3_SRAI         3'b101
`define FUNCT3_ADD          3'b000
`define FUNCT3_SUB          3'b000
`define FUNCT3_SLL          3'b001
`define FUNCT3_SLT          3'b010
`define FUNCT3_SLTU         3'b011
`define FUNCT3_XOR          3'b100
`define FUNCT3_SRL          3'b101
`define FUNCT3_SRA          3'b101
`define FUNCT3_OR           3'b110
`define FUNCT3_AND          3'b111
`define FUNCT3_FENCE        3'b000
`define FUNCT3_FENCEI       3'b001
`define FUNCT3_CSRRW        3'b001
`define FUNCT3_CSRRS        3'b010
`define FUNCT3_CSRRC        3'b011
`define FUNCT3_CSRRWI       3'b101
`define FUNCT3_CSRRSI       3'b110
`define FUNCT3_CSRRCI       3'b111
// RV64I
`define FUNCT3_LWU          3'b110
`define FUNCT3_LD           3'b011
`define FUNCT3_SD           3'b011
`define FUNCT3_ADDIW        3'b000
`define FUNCT3_SLLIW        3'b001
`define FUNCT3_SRLIW        3'b101
`define FUNCT3_SRAIW        3'b101
`define FUNCT3_ADDW         3'b000
`define FUNCT3_SUBW         3'b000
`define FUNCT3_SLLW         3'b001
`define FUNCT3_SRLW         3'b101
`define FUNCT3_SRAW         3'b101


// Devices
`define DEV_BASEADDR        64'h00000000_20000000
`define DEV_RTC_OFFSET      64'h100
`define DEV_RTC             (`DEV_BASEADDR + `DEV_RTC_OFFSET)