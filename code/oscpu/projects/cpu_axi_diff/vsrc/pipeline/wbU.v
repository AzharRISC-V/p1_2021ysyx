
// Zhengpu Shi

// Writeback Unit, 组合逻辑电路

`include "defines.v"

/*
  rd 有两处写入，这里做一个简单的处理
  目前还不是流水线，而一个指令不可能同时在EX/MEM后访问rd，所以没有冲突
*/

// module wbU(
//   input   wire                  clk,
//   input   wire                  rst,

//   input   wire                  ex_wen_i      ,   // EX后的写回
//   input   wire  [`BUS_64]       ex_wdata_i    ,   
//   input   wire                  mem_wen_i     ,   // MEM后的写回
//   input   wire  [`BUS_64]       mem_wdata_i   ,
//   input   wire                  csr_wen_i     ,   // CSR后的写回
//   input   wire  [`BUS_64]       csr_wdata_i   ,
//   output  reg                   wen_o,
//   output  wire  [`BUS_64]       wdata_o
// );

// // 写使能
// always @(*) begin
//   wen_o = ex_wen_i | mem_wen_i | csr_wen_i;
// end

// // 写数据
// always @(*) begin
//   if (csr_wen_i) begin
//     wdata_o = csr_wdata_i;
//   end
//   else if (mem_wen_i) begin
//     wdata_o = mem_wdata_i;
//   end
//   else if (ex_wen_i) begin
//     wdata_o = ex_wdata_i;
//   end
//   else begin
//     wdata_o = 0;
//   end
// end


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
