// Zhengpu Shi

`include "defines.v"

/*
  rd 有两处写入，这里做一个简单的处理
  目前还不是流水线，而一个指令不可能同时在EX/MEM后访问rd，所以没有冲突
*/

module wb_stage(
  input   wire                  clk,
  input   wire                  rst,
  input   wire [`BUS_8]         instcycle_cnt_val,
  // input   wire  [`BUS_STAGE]    stage_i,
  // output  reg   [`BUS_STAGE]    stage_o,

  input   wire                  ex_wen_i      ,   // EX后的写回
  input   wire  [`BUS_64]       ex_wdata_i    ,   
  input   wire                  mem_wen_i     ,   // MEM后的写回
  input   wire  [`BUS_64]       mem_wdata_i   ,

  output  wire                  wen_o,
  output  wire  [`BUS_64]       wdata_o
);

// stage
// always @(posedge clk) begin
//   if (rst)
//     stage_o = `STAGE_EMPTY;
//   else
//     if (stage_i == `STAGE_EX)
//       stage_o = `STAGE_WB;
// end

wire stage_wb = 0;
// single_pulse u1 (
//   .clk(clk), 
//   .rst(rst), 
//   .signal_in((stage_o == `STAGE_WB)), 
//   .pluse_out(stage_wb)
// );

// 写使能
assign wen_o = (instcycle_cnt_val == 6) ? (ex_wen_i | mem_wen_i) : 0;

// 写入数据的来源，0：EX, 1:MEM
wire ch = ex_wen_i ? 0 : 1;


// 写数据
assign wdata_o = wen_o ? (ch ? mem_wdata_i : ex_wdata_i) : 0;

endmodule
