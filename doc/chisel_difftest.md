# Difftest 使用指南

## 编写顶层模块 `TopMain.scala`

`TopMain` 是Scala程序的入口，类似于C/C++中的main函数，可以直接参考本框架中的代码，不需要做任何修改。

```scala
object TopMain extends App {
  (new chisel3.stage.ChiselStage).execute(args, Seq(chisel3.stage.ChiselGeneratorAnnotation(() => new SimTop())))
}
```

## 修改 `SimTop.scala`

此文件是处理器的仿真顶层。按照Difftest框架的要求，CPU的顶层模块必须命名为 `SimTop`。在这一模块中，添加上Difftest需要的IO接口，如下所示。所有非必要的接口直接留空或者赋值为0或false即可。

```scala
import chisel3._
import difftest._

class SimTop extends Module {
  val io = IO(new Bundle {
    val logCtrl = new LogCtrlIO
    val perfInfo = new PerfInfoIO
    val uart = new UARTIO
  })

  ...

  io.uart.out.valid := false.B
  io.uart.out.ch := 0.U
  io.uart.in.valid := false.B
}
```

## 修改 `Core.scala`

此文件是处理器本体的顶层。在我们给出的框架中，在 `Core.scala` 中包含了四个Difftest模块（`DifftestInstrCommit`, `DifftestArchEvent`, `DifftestTrapEvent`, `DifftestCSRState`），但是在进一步完善处理器时，可能需要将其中一些模块迁移到其他部分（如：把 `DifftestCSRState` 迁移到单独编写的CSR处理单元）。同上，没有完善的部分如CSR寄存器的值，可以暂时全部赋值为0。

```scala
import chisel3._
import chisel3.util.experimental._
...
import difftest._

class Core extends Module {
  val io = IO(new Bundle {
    ...
  })

  ...

  val dt_ic = Module(new DifftestInstrCommit)
  dt_ic.io.clock    := clock
  dt_ic.io.coreid   := 0.U
  dt_ic.io.index    := 0.U
  dt_ic.io.valid    := true.B         // 提交指令是否有效
  dt_ic.io.pc       := fetch.io.pc
  dt_ic.io.instr    := fetch.io.inst
  dt_ic.io.skip     := false.B        // 是否需要跳过本条指令，按需设置
  dt_ic.io.isRVC    := false.B        // 是否是C扩展16位指令，设为false即可
  dt_ic.io.scFailed := false.B        // A扩展sc指令是否失败，设为false即可
  dt_ic.io.wen      := decode.io.rd_en
  dt_ic.io.wdata    := execution.io.out
  dt_ic.io.wdest    := decode.io.rd_addr

  val dt_ae = Module(new DifftestArchEvent)
  dt_ae.io.clock        := clock
  dt_ae.io.coreid       := 0.U
  dt_ae.io.intrNO       := 0.U        // 外部中断使用
  dt_ae.io.cause        := 0.U
  dt_ae.io.exceptionPC  := 0.U

  val cycle_cnt = RegInit(0.U(64.W))
  val instr_cnt = RegInit(0.U(64.W))

  cycle_cnt := cycle_cnt + 1.U
  instr_cnt := instr_cnt + 1.U

  val rf_a0 = WireInit(0.U(64.W))
  BoringUtils.addSink(rf_a0, "rf_a0")

  val dt_te = Module(new DifftestTrapEvent)
  dt_te.io.clock    := clock
  dt_te.io.coreid   := 0.U
  dt_te.io.valid    := (fetch.io.inst === "h0000006b".U)
                                      // 0x6b是NEMU中定义的HALT指令
  dt_te.io.code     := rf_a0(2, 0)    // 读取a0的值判断程序是否正确执行并退出
  dt_te.io.pc       := fetch.io.pc
  dt_te.io.cycleCnt := cycle_cnt      // cycle计数器
  dt_te.io.instrCnt := instr_cnt      // 指令计数器

  val dt_cs = Module(new DifftestCSRState)
  dt_cs.io.clock          := clock
  dt_cs.io.coreid         := 0.U
  dt_cs.io.priviledgeMode := 3.U  // Machine mode
  dt_cs.io.mstatus        := 0.U
  dt_cs.io.sstatus        := 0.U
  dt_cs.io.mepc           := 0.U
  dt_cs.io.sepc           := 0.U
  dt_cs.io.mtval          := 0.U
  dt_cs.io.stval          := 0.U
  dt_cs.io.mtvec          := 0.U
  dt_cs.io.stvec          := 0.U
  dt_cs.io.mcause         := 0.U
  dt_cs.io.scause         := 0.U
  dt_cs.io.satp           := 0.U
  dt_cs.io.mip            := 0.U
  dt_cs.io.mie            := 0.U
  dt_cs.io.mscratch       := 0.U
  dt_cs.io.sscratch       := 0.U
  dt_cs.io.mideleg        := 0.U
  dt_cs.io.medeleg        := 0.U
}
```

## 修改 `RegFile.scala`

在 `RegFile.scala` 中包含了 `DifftestArchIntRegState` 模块。

```scala
import chisel3._
import chisel3.util.experimental._
import difftest._

class RegFile extends Module {
  val io = IO(new Bundle {
    ...
  })

  // 如果用Mem类型，则需要手动转换成Vec类型后提交给Difftest
  val rf = RegInit(VecInit(Seq.fill(32)(0.U(64.W))))

  ...

  val dt_ar = Module(new DifftestArchIntRegState)
  dt_ar.io.clock  := clock
  dt_ar.io.coreid := 0.U
  dt_ar.io.gpr    := rf

  BoringUtils.addSource(rf(10), "rf_a0")
}
```
