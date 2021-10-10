
// ZhengpuShi

// Writeback Interface

`include "defines.v"

module ysyx_210544_wb_stage(
  input   wire                clk,
  input   wire                rst,
  input   wire                i_wb_memoryed_req,
  output  wire                o_wb_memoryed_ack,
  output  reg                 o_wb_writebacked_req,
  input   wire                i_wb_writebacked_ack,
  input   wire  [`BUS_64]     i_wb_pc,
  input   wire  [`BUS_32]     i_wb_inst,
  input   wire  [`BUS_RIDX]   i_wb_rd,
  input   wire                i_wb_rd_wen,
  input   wire  [`BUS_64]     i_wb_rd_wdata,
  input   wire                i_wb_skipcmt,
  output  wire  [`BUS_64]     o_wb_pc,
  output  wire  [`BUS_32]     o_wb_inst,
  output  wire  [`BUS_RIDX]   o_wb_rd,
  output  wire                o_wb_rd_wen,
  output  wire  [`BUS_64]     o_wb_rd_wdata,
  output  wire                o_wb_skipcmt,
  input   wire  [`BUS_32]     i_wb_intrNo,
  output  reg   [`BUS_32]     o_wb_intrNo
);

reg                           i_ena;    // 是否使能组合逻辑单元部件
wire                          i_disable = !i_ena;

// 保存输入信息
reg   [`BUS_64]               tmp_i_wb_pc;
reg   [`BUS_32]               tmp_i_wb_inst;
reg   [4 : 0]                 tmp_i_wb_rd;
reg                           tmp_i_wb_rd_wen;
reg   [`BUS_64]               tmp_i_wb_rd_wdata;
reg                           tmp_i_wb_skipcmt;

wire memoryed_hs;



assign o_wb_memoryed_ack = 1'b1;
assign memoryed_hs = i_wb_memoryed_req & o_wb_memoryed_ack;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_wb_pc,
      tmp_i_wb_inst,
      tmp_i_wb_rd, 
      tmp_i_wb_rd_wen, 
      tmp_i_wb_rd_wdata,
      tmp_i_wb_skipcmt
    } <= 0;

    o_wb_writebacked_req    <= 0;
    i_ena                   <= 0;
    o_wb_intrNo             <= 0;
  end
  else begin
    if (memoryed_hs) begin
      tmp_i_wb_pc             <= i_wb_pc;
      tmp_i_wb_inst           <= i_wb_inst;
      tmp_i_wb_rd             <= i_wb_rd; 
      tmp_i_wb_rd_wen         <= i_wb_rd_wen;
      tmp_i_wb_rd_wdata       <= i_wb_rd_wdata;
      tmp_i_wb_skipcmt        <= i_wb_skipcmt;

      o_wb_writebacked_req  <= 1;
      i_ena                 <= 1;
      o_wb_intrNo           <= i_wb_intrNo;
    end
    else if (i_wb_writebacked_ack) begin
      o_wb_writebacked_req  <= 0;
      i_ena                 <= 0;
      o_wb_intrNo           <= 0;
    end
  end
end

assign o_wb_pc        = i_disable ? 64'd0 : tmp_i_wb_pc;
assign o_wb_inst      = i_disable ? 32'd0 : tmp_i_wb_inst;
assign o_wb_skipcmt   = i_disable ?  1'd0 : tmp_i_wb_skipcmt;
assign o_wb_rd        = i_disable ?  5'd0 : tmp_i_wb_rd;
assign o_wb_rd_wen    = i_disable ?  1'd0 : tmp_i_wb_rd_wen;
assign o_wb_rd_wdata  = i_disable ? 64'd0 : tmp_i_wb_rd_wdata;

endmodule
