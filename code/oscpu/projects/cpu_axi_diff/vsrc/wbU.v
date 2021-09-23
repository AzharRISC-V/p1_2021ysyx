
// Zhengpu Shi

// Writeback Unit, 组合逻辑电路

`include "defines.v"

module wbU(
  input   wire                i_ena,
  input   wire                clk,
  input   wire                rst,
  input   wire  [`BUS_RIDX]   i_rd,
  input   wire                i_rd_wen,
  input   wire  [`BUS_64]     i_rd_wdata,
  output  reg   [`BUS_RIDX]   o_rd,
  output  reg                 o_rd_wen,
  output  wire  [`BUS_64]     o_rd_wdata
);


wire i_disable = !i_ena;

assign o_rd = i_disable ? 0 : i_rd;
assign o_rd_wen = i_disable ? 0 : i_rd_wen;
assign o_rd_wdata = i_disable ? 0 : i_rd_wdata;

endmodule
