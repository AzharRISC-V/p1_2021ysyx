// Zhengpu Shi

`include "defines.v";
`include "mem_access.v"

module mem_stage(
  input   wire              clk,
  input   wire              rst,

  output  wire              sig_memread_ok,
  output  wire              sig_memwrite_ok,

  input   wire              ren,
  input   wire  [`BUS_64]   raddr,
  output  wire  [`BUS_64]   rdata,

  input   wire              wen,
  input   wire  [`BUS_64]   waddr,
  input   wire  [`BUS_64]   wdata,
  input   wire  [`BUS_64]   wmask,     // 数据掩码，比如0x00F0，则仅写入[7:4]位

  // rd写回
  input   wire              rd_wen_i,
  output  wire              rd_wen_o
);

always@(*) begin
  if (ren)
    $displayh("  MEM: raddr=", raddr);
  if (wen)
    $displayh("  MEM: waddr=", waddr, " wdata=", wdata, " wmask=", wmask);
end

// 访问内存，将1字节访问转换为8字节对齐的一次或两次访问
mem_access u1_mem_access(
  .clk      (clk    ),
  .ren      (ren    ),
  .sig_memread_ok   (sig_memread_ok),
  .sig_memwrite_ok  (sig_memwrite_ok),
  .addr     (raddr  ),
  .rdata    (rdata  ),
  .wdata    (wdata  ),
  .wmask    (wmask  ),
  .wen      (wen    )
);

// rd写使能信号。需要确保 mem访问结束后才能置位，这里简化了。
reg rd_wen_o_0;
always @(*) begin
  if (rd_wen_i & ren)
    rd_wen_o_0 = 1;
  else
    rd_wen_o_0 = 0;
end
assign rd_wen_o = rd_wen_o_0;

endmodule
