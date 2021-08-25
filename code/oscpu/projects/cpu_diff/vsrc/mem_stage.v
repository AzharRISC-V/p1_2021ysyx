// Zhengpu Shi

`include "defines.v";
`include "mem_access.v"

module mem_stage(
  input   wire              clk,
  input   wire              rst,

  input   wire              ren,
  input   wire  [`BUS_64]   raddr,
  input   wire              wen,
  input   wire  [`BUS_64]   waddr,
  input   wire  [`BUS_64]   wdata,
  input   wire  [`BUS_64]   wmask,    // 数据掩码，比如0x00F0，则仅写入[7:4]位

  output  reg   [`BUS_64]   rdata
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
  .addr     (raddr  ),
  .rdata    (rdata  ),
  .wdata    (wdata  ),
  .wmask    (wmask  ),
  .wen      (wen    )
);


endmodule
