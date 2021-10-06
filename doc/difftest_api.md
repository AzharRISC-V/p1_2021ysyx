# difftest接口说明

`香山difftest框架`使用`verilator`提供的[DPI-C](https://verilator.org/guide/latest/connecting.html#direct-programming-interface-dpi)功能实现指令执行结果提交至`difftest`。用法可参考`cpu_diff`和`chisel_cpu_diff`例程。以下对`一生一芯`[基础任务](https://oscpu.github.io/ysyx/wiki/tasks/basic.html)中用到的`verilog difftest`接口进行说明，`chisel difftest`接口用法类似，可参考[chisel_difftest.md](./chisel_difftest.md)。

```verilog
// 触发异常
module DifftestArchEvent (
    input        clock,			// 时钟
    input [ 7:0] coreid,		// cpu id，单核时固定为0
    input [31:0] intrNO,		// 中断号，非0时产生中断。产生中断的时钟周期中，DifftestInstrCommit提交的valid需为0
    input [31:0] cause,			// 异常号，ecall时不需要考虑
    input [63:0] exceptionPC,	// 产生异常时的PC
    input [31:0] exceptionInst	// 产生异常时的指令
);

// 提交指令
module DifftestInstrCommit (
    input        clock,
    input [ 7:0] coreid,
    input [ 7:0] index,
    input        valid,			// 是否提交指令
    input [63:0] pc,			// 当前PC
    input [31:0] instr,			// 当前指令
    input        skip,			// 跳过当前指令的对比
    input        isRVC,			// 压缩指令
    input        scFailed,		// SC指令执行失败
    input        wen,			// 写回
    input [ 7:0] wdest,			// 写回寄存器堆索引
    input [63:0] wdata			// 写回值
);

// Trap事件，用于告知difftest程序执行结束
module DifftestTrapEvent (
    input        clock,
    input [ 7:0] coreid,
    input        valid,			// 执行结束
    input [ 2:0] code,			// 执行结果
    input [63:0] pc,			// 当前PC
    input [63:0] cycleCnt,		// 时钟周期数
    input [63:0] instrCnt		// 指令数
);

// 提交CSR寄存器
module DifftestCSRState (
    input        clock,
    input [ 7:0] coreid,
    input [ 1:0] priviledgeMode,// 特权模式
    input [63:0] mstatus,
    input [63:0] sstatus,
    input [63:0] mepc,
    input [63:0] sepc,
    input [63:0] mtval,
    input [63:0] stval,
    input [63:0] mtvec,
    input [63:0] stvec,
    input [63:0] mcause,
    input [63:0] scause,
    input [63:0] satp,
    input [63:0] mip,
    input [63:0] mie,
    input [63:0] mscratch,
    input [63:0] sscratch,
    input [63:0] mideleg,
    input [63:0] medeleg
);

// 提交通用寄存器
module DifftestArchFpRegState (
    input         clock,
    input [ 7:0]  coreid,
    input [63:0]  gpr_0,
    input [63:0]  gpr_1,
    input [63:0]  gpr_2,
    input [63:0]  gpr_3,
    input [63:0]  gpr_4,
    input [63:0]  gpr_5,
    input [63:0]  gpr_6,
    input [63:0]  gpr_7,
    input [63:0]  gpr_8,
    input [63:0]  gpr_9,
    input [63:0]  gpr_10,
    input [63:0]  gpr_11,
    input [63:0]  gpr_12,
    input [63:0]  gpr_13,
    input [63:0]  gpr_14,
    input [63:0]  gpr_15,
    input [63:0]  gpr_16,
    input [63:0]  gpr_17,
    input [63:0]  gpr_18,
    input [63:0]  gpr_19,
    input [63:0]  gpr_20,
    input [63:0]  gpr_21,
    input [63:0]  gpr_22,
    input [63:0]  gpr_23,
    input [63:0]  gpr_24,
    input [63:0]  gpr_25,
    input [63:0]  gpr_26,
    input [63:0]  gpr_27,
    input [63:0]  gpr_28,
    input [63:0]  gpr_29,
    input [63:0]  gpr_30,
    input [63:0]  gpr_31
);
```

