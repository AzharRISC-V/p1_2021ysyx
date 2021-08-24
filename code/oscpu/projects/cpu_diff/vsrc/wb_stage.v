// Zhengpu Shi

`include "defines.v"

module wb_stage(
  input   wire              clk,
  input   wire              rst,

  input   wire              rd_wen_i,
  input   wire  [4 : 0]     rd_waddr_i,
  input   reg   [`BUS_64]   rd_data_i,

  output  reg               rd_wen_o,
  output  reg   [4 : 0]     rd_waddr_o,
  output  reg   [`REG_BUS ] rd_data_o
);

always@(posedge clk) begin
  if (rst == 1'b1) begin
    rd_wen_o    = 0;
    rd_waddr_o  = 0;
    rd_data_o   = 0;
  end
  else begin
    rd_wen_o    = rd_wen_i;
    rd_waddr_o  = rd_waddr_i;
    rd_data_o   = rd_data_i;
  end
end
    
endmodule
