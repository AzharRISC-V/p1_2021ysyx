
`timescale 1ns / 1ps

// 常用的常数
`define ZERO_WORD           64'h00000000_00000000       // 值位0的值
`define PC_START            64'h00000000_80000000  
`define RISCV_PRIV_MODE_U   0
`define RISCV_PRIV_MODE_S   1
`define RISCV_PRIV_MODE_M   3

`define BUS_8               7:0
`define BUS_16              15:0
`define BUS_32              31:0
`define BUS_64              63:0

// 当前指令的状态机
`define BUS_STATE           2:0             // 指令状态的总线
`define STATE_IDLE          3'b000          // 空闲状态，可以开始取指
`define STATE_MEMREAD       3'b001          // Load指令，等待内存读取完成
`define STATE_MEMWRITE      3'b010          // Store指令，等待内存写入完成
`define STATE_WB            3'b011          // 所有指令，等待WB完成


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
`define INST_R_TYPE         3'b000
`define INST_I_TYPE         3'b001
`define INST_S_TYPE         3'b010
`define INST_B_TYPE         3'b011
`define INST_U_TYPE         3'b100
`define INST_J_TYPE         3'b101


// opcode，用于指令译码
`define OPCODE_LUI          5'b01101
`define OPCODE_AUIPC        5'b00101
`define OPCODE_JAL          5'b11011
`define OPCODE_JALR         5'b11001
`define OPCODE_BEQ          5'b11000
`define OPCODE_LB           5'b00000
`define OPCODE_SB           5'b01000
`define OPCODE_ADDI         5'b00100
`define OPCODE_ADD          5'b01100
`define OPCODE_FENCE        5'b00011      // 同步
`define OPCODE_ENV          5'b11100      // 环境

// 某个opcode对应的 funct3，用于指令译码
// 若还不能区分，手动判断 funct7
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
`define FUNCT3_SD           3'b011
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
