// Zhengpu Shi

`include "defines.v";
`include "mem_access.v"

module mem_stage(
  input   wire  [`BUS_64]       clk_cnt,
  input   wire                  clk,
  input   wire                  rst,
  input   wire [`BUS_8]         instcycle_cnt_val,

  output  wire                  sig_memread_ok,
  output  wire                  sig_memwrite_ok,

  input   wire                  ren,
  input   wire  [`BUS_64]       raddr,
  input   wire  [2 : 0]         funct3,
  output  wire  [`BUS_64]       rdata,

  input   wire                  wen,
  input   wire  [`BUS_64]       waddr,
  input   wire  [`BUS_64]       wdata
);

// always@(*) begin
//   if (ren && (clk_cnt >= `CLK_CNT_VAL))
//     $displayh("  MEM: raddr=", raddr);
// end
// always@(*) begin
//   if (wen && (clk_cnt >= `CLK_CNT_VAL))
//     $displayh("  MEM: waddr=", waddr, " wdata=", wdata, " wmask=", wmask);
// end

wire            en        = ren | wen;
wire  [`BUS_64] raddr_0   = (!en) ? 0 : raddr;
wire  [2 : 0]   funct3_0  = (!en) ? 0 : funct3;
// 访问内存，将1字节访问转换为8字节对齐的一次或两次访问
mem_access Mem_access(
  .clk_cnt            (clk_cnt          ),
  .clk                (clk              ),
  .ren                (ren              ),
  .sig_memread_ok     (sig_memread_ok   ),
  .sig_memwrite_ok    (sig_memwrite_ok  ),
  .addr               (raddr_0          ),
  .funct3             (funct3_0         ),
  .rdata              (rdata            ),
  .wdata              (wdata            ),
  .wen                (wen              )
);

endmodule
