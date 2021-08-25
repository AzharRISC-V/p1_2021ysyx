// ZhengpuShi

/*
  rd 有两处写入，这里做一个简单的处理
  目前还不是流水线，而一个指令不可能同时在EX/WB阶段访问rd，所以两个不会同时发生
*/

`include "defines.v" 

module rd_write(
  input   wire              clk               ,
  input   wire              rst               ,
  input   wire              ex_rd_wen_i       ,
  input   wire  [`BUS_64]   ex_rd_wdata_i     ,
  input   wire              wb_rd_wen_i       ,
  input   wire  [`BUS_64]   wb_rd_wdata_i     ,
  output  wire              rd_wen_o          ,
  output  wire  [`BUS_64]   rd_wdata_o        
);


assign  rd_wen_o    = ex_rd_wen_i | wb_rd_wen_i;

// 通道，0:EX, 1:WB
wire    ch = ex_rd_wen_i ? 0 : 1;

assign  rd_wdata_o  = ch ? wb_rd_wdata_i : ex_rd_wdata_i;

endmodule