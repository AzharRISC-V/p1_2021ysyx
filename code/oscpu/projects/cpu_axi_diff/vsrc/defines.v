
// ZhengpuShi

// Definitions

`timescale 1ns / 1ps

`define YSYX210544_ZERO_WORD           64'h00000000_00000000

`ifdef YSYX210544_DIFFTEST_FLAG
`define YSYX210544_PC_START            64'h00000000_80000000
`else
`define YSYX210544_PC_START            64'h00000000_30000000
`endif

`define YSYX210544_SIZE_B              3'b000
`define YSYX210544_SIZE_H              3'b001
`define YSYX210544_SIZE_W              3'b010
`define YSYX210544_SIZE_D              3'b011

`define YSYX210544_REQ_READ            1'b0
`define YSYX210544_REQ_WRITE           1'b1

`define YSYX210544_RW_DATA_WIDTH       512

`define YSYX210544_RISCV_PRIV_MODE_U   0
`define YSYX210544_RISCV_PRIV_MODE_S   1
`define YSYX210544_RISCV_PRIV_MODE_M   3


`define YSYX210544_CLOCKS_PER_SECOND   64'd240_0000        // 每秒的clock数，约240万

`define YSYX210544_BUS_8               7:0
`define YSYX210544_BUS_16              15:0
`define YSYX210544_BUS_32              31:0
`define YSYX210544_BUS_64              63:0
`define YSYX210544_BUS_RIDX            4:0                 // 寄存器索引的总线

// CSR

// CSR addr
`define YSYX210544_CSR_ADR_MCYCLE      12'hB00
`define YSYX210544_CSR_ADR_MSTATUS     12'h300         // machine status register
`define YSYX210544_CSR_ADR_MIE         12'h304         // machine interrupt-enable register
`define YSYX210544_CSR_ADR_MTVEC       12'h305         // machine trap-handler base address
`define YSYX210544_CSR_ADR_MSCRATCH    12'h340         // scratch register for machine trap handlers.
`define YSYX210544_CSR_ADR_MEPC        12'h341         // machine exception program counter
`define YSYX210544_CSR_ADR_MCAUSE      12'h342         // machine trap cause
`define YSYX210544_CSR_ADR_MIP         12'h344         // machine interrupt pending

// 已编码的指令
`define YSYX210544_INST_NOP            32'h0000_0013   // addi x0,x0,0

// 自定义的指令码
`define YSYX210544_INST_LUI            8'b0000_0001    // d1
`define YSYX210544_INST_AUIPC          8'b0000_0010    //
`define YSYX210544_INST_JAL            8'b0000_0011    //
`define YSYX210544_INST_JALR           8'b0000_0100    //
`define YSYX210544_INST_BEQ            8'b0000_0101    //
`define YSYX210544_INST_BNE            8'b0000_0110    //
`define YSYX210544_INST_BLT            8'b0000_0111    //
`define YSYX210544_INST_BGE            8'b0000_1000    //
`define YSYX210544_INST_BLTU           8'b0000_1001    //
`define YSYX210544_INST_BGEU           8'b0000_1010    //
`define YSYX210544_INST_LB             8'b0000_1011    //
`define YSYX210544_INST_LH             8'b0000_1100    //
`define YSYX210544_INST_LW             8'b0000_1101    //
`define YSYX210544_INST_LBU            8'b0000_1110    //
`define YSYX210544_INST_LHU            8'b0000_1111    //
`define YSYX210544_INST_SB             8'b0001_0000    //
`define YSYX210544_INST_SH             8'b0001_0001    //
`define YSYX210544_INST_SW             8'b0001_0010    //
`define YSYX210544_INST_ADDI           8'b0001_0011    //
`define YSYX210544_INST_SLTI           8'b0001_0100    //
`define YSYX210544_INST_SLTIU          8'b0001_0101    //
`define YSYX210544_INST_XORI           8'b0001_0110    //
`define YSYX210544_INST_ORI            8'b0001_0111    //
`define YSYX210544_INST_ANDI           8'b0001_1000    //
`define YSYX210544_INST_SLLI           8'b0001_1001    //
`define YSYX210544_INST_SRLI           8'b0001_1010    //
`define YSYX210544_INST_SRAI           8'b0001_1011    //
`define YSYX210544_INST_ADD            8'b0001_1100    //
`define YSYX210544_INST_SUB            8'b0001_1101    //
`define YSYX210544_INST_SLL            8'b0001_1110    //
`define YSYX210544_INST_SLT            8'b0001_1111    //
`define YSYX210544_INST_SLTU           8'b0010_0000    //
`define YSYX210544_INST_XOR            8'b0010_0001    //
`define YSYX210544_INST_SRL            8'b0010_0010    //
`define YSYX210544_INST_SRA            8'b0010_0011    //
`define YSYX210544_INST_OR             8'b0010_0100    //
`define YSYX210544_INST_AND            8'b0010_0101    //
`define YSYX210544_INST_FENCE          8'b0010_0110    //
`define YSYX210544_INST_FENCEI         8'b0010_0111    //
`define YSYX210544_INST_ECALL          8'b0010_1000    //
`define YSYX210544_INST_EBREAK         8'b0010_1001    //
`define YSYX210544_INST_CSRRW          8'b0010_1010    //
`define YSYX210544_INST_CSRRS          8'b0010_1011    //
`define YSYX210544_INST_CSRRC          8'b0010_1100    //
`define YSYX210544_INST_CSRRWI         8'b0010_1101    //
`define YSYX210544_INST_CSRRSI         8'b0010_1110    //
`define YSYX210544_INST_CSRRCI         8'b0010_1111    // d47 = h2F

`define YSYX210544_INST_LWU            8'b0011_0000    //
`define YSYX210544_INST_LD             8'b0011_0001    //
`define YSYX210544_INST_SD             8'b0011_0010    //
`define YSYX210544_INST_ADDIW          8'b0011_0011    //
`define YSYX210544_INST_SLLIW          8'b0011_0100    //
`define YSYX210544_INST_SRLIW          8'b0011_0101    //
`define YSYX210544_INST_SRAIW          8'b0011_0110    //
`define YSYX210544_INST_ADDW           8'b0011_0111    //
`define YSYX210544_INST_SUBW           8'b0011_1000    //
`define YSYX210544_INST_SLLW           8'b0011_1001    //
`define YSYX210544_INST_SRLW           8'b0011_1010    //
`define YSYX210544_INST_SRAW           8'b0011_1011    //
`define YSYX210544_INST_MRET           8'b0011_1100    //

// ==  = Devices

`define YSYX210544_DEV_BASEADDR        64'h0200_0000

// RTC
`define YSYX210544_DEV_RTC_OFFSET      64'h0100
`define YSYX210544_DEV_RTC             (`YSYX210544_DEV_BASEADDR + `YSYX210544_DEV_RTC_OFFSET)

// Machine time register，以恒定频率增加，廉价的RTC软件方案
// mcycle与mtime的区别：
// 1. mcycle可随外接时钟而变化
// 2. mtime必须以恒定的频率增加（估计是因指令执行耗费的clock数不同而引起，这里需要封装差异吗）
`define YSYX210544_DEV_MTIME_OFFSET    64'hbff8
`define YSYX210544_DEV_MTIME           (`YSYX210544_DEV_BASEADDR + `YSYX210544_DEV_MTIME_OFFSET)
// Machien time compare register
// 当 mtime > = mtimecmp 时，产生计时器中断
// mip的MTIP位置1。
`define YSYX210544_DEV_MTIMECMP_OFFSET 64'h4000
`define YSYX210544_DEV_MTIMECMP        (`YSYX210544_DEV_BASEADDR + `YSYX210544_DEV_MTIMECMP_OFFSET)

