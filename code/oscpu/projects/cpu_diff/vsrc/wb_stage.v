// Zhengpu Shi

`include "defines.v"

module wb_stage(
  input   wire              clk,
  input   wire              rst,

  input   wire              rd_wen_i,
  input   wire  [4 : 0]     rd_waddr_i,     // 寄存器编号
  input   wire  [`BUS_64]   rd_wdata_i,

  output  wire              rd_wen_o,
  output  wire  [4 : 0]     rd_waddr_o,
  output  wire  [`BUS_64]   rd_wdata_o
);

assign rd_wen_o = (rst == 1'b1) ? 0 : rd_wen_i;
assign rd_waddr_o = (rst == 1'b1) ? 0 : rd_waddr_i;
assign rd_wdata_o = (rst == 1'b1) ? 0 : rd_wdata_i;
    
endmodule
