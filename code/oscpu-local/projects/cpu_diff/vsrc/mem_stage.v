// Zhengpu Shi

`include "defines.v";

module mem_stage(
  input wire clk,
  input wire rst,

  input wire ren,
  input wire [`BUS_64]  raddr,
  input wire wen,
  input wire [`BUS_64]  waddr,
  input wire [`BUS_64]  wdata,
  input wire [`BUS_64]  wdatamask,    // 数据掩码，比如0x00F0，则仅写入[7:4]位

  output reg [`BUS_64]  rdata
);

// Access memory
RAMHelper RAMHelper(
  .clk              (clk),
  .en               (ren),
  .rIdx             (raddr >> 3),  // 按照64位(8字节)来访问
  .rdata            (rdata),
  .wIdx             (waddr >> 3),
  .wdata            (wdata),
  .wmask            (wdatamask),
  .wen              (wen)
);

endmodule
