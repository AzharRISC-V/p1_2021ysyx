
// ZhengpuShi

// Writeback Interface

`include "defines.v"

module ysyx_210544_wb_stage(
  input   wire                clk,
  input   wire                rst,
  input   reg                 i_wb_memoryed_req,
  output  reg                 o_wb_memoryed_ack,
  output  reg                 o_wb_writebacked_req,
  input   reg                 i_wb_writebacked_ack,
  input   wire  [`BUS_64]     i_wb_pc,
  input   wire  [`BUS_32]     i_wb_inst,
  input   wire  [`BUS_RIDX]   i_wb_rd,
  input   wire                i_wb_rd_wen,
  input   wire  [`BUS_64]     i_wb_rd_wdata,
  input   wire                i_wb_nocmt,
  input   wire                i_wb_skipcmt,
  input   reg   [`BUS_64]     i_wb_clint_mip,
  output  reg   [`BUS_64]     o_wb_clint_mip,
  output  wire  [`BUS_64]     o_wb_pc,
  output  wire  [`BUS_32]     o_wb_inst,
  output  reg   [`BUS_RIDX]   o_wb_rd,
  output  reg                 o_wb_rd_wen,
  output  wire  [`BUS_64]     o_wb_rd_wdata,
  output  reg                 o_wb_nocmt,
  output  reg                 o_wb_skipcmt,
  input   wire  [`BUS_32]     i_wb_intrNo,
  output  reg   [`BUS_32]     o_wb_intrNo
);


assign o_wb_memoryed_ack = 1'b1;

wire memoryed_hs = i_wb_memoryed_req & o_wb_memoryed_ack;

// 是否使能组合逻辑单元部件
reg                           i_ena;
wire                          i_disable = !i_ena;

// 保存输入信息
reg   [`BUS_64]               tmp_i_wb_pc;
reg   [`BUS_32]               tmp_i_wb_inst;
reg   [4 : 0]                 tmp_i_wb_rd;
reg                           tmp_i_wb_rd_wen;
reg   [`BUS_64]               tmp_i_wb_rd_wdata;
reg                           tmp_i_wb_nocmt;
reg                           tmp_i_wb_skipcmt;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_wb_pc,
      tmp_i_wb_inst,
      tmp_i_wb_rd, 
      tmp_i_wb_rd_wen, 
      tmp_i_wb_rd_wdata,
      tmp_i_wb_nocmt,
      tmp_i_wb_skipcmt
    } <= 0;

    o_wb_writebacked_req  <= 0;
    i_ena                 <= 0;

    o_wb_clint_mip  <= 0;
    o_wb_intrNo <= 0;
  end
  else begin
    if (memoryed_hs) begin
      tmp_i_wb_pc             <= i_wb_pc;
      tmp_i_wb_inst           <= i_wb_inst;
      tmp_i_wb_rd             <= i_wb_rd; 
      tmp_i_wb_rd_wen         <= i_wb_rd_wen;
      tmp_i_wb_rd_wdata       <= i_wb_rd_wdata;
      tmp_i_wb_nocmt          <= i_wb_nocmt;
      tmp_i_wb_skipcmt        <= i_wb_skipcmt;

      o_wb_writebacked_req  <= 1;
      i_ena                 <= 1;

      o_wb_clint_mip   <= i_wb_clint_mip;
      o_wb_intrNo <= i_wb_intrNo;
    end
    else if (i_wb_writebacked_ack) begin
      o_wb_writebacked_req  <= 0;
      i_ena                 <= 0;
      o_wb_intrNo <= 0;
    end
  end
end

assign o_wb_pc        = i_disable ? 0 : tmp_i_wb_pc;
assign o_wb_inst      = i_disable ? 0 : tmp_i_wb_inst;
assign o_wb_nocmt     = i_disable ? 0 : tmp_i_wb_nocmt;
assign o_wb_skipcmt   = i_disable ? 0 : tmp_i_wb_skipcmt;
assign o_wb_rd        = i_disable ? 0 : tmp_i_wb_rd;
assign o_wb_rd_wen    = i_disable ? 0 : tmp_i_wb_rd_wen;
assign o_wb_rd_wdata  = i_disable ? 0 : tmp_i_wb_rd_wdata;

ysyx_210544_wbU WbU(
  .i_ena                      (i_ena                      ),
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_rd                       (tmp_i_wb_rd                ),
  .i_rd_wen                   (tmp_i_wb_rd_wen            ),
  .i_rd_wdata                 (tmp_i_wb_rd_wdata          ),
  .o_rd                       (                     ),
  .o_rd_wen                   (                 ),
  .o_rd_wdata                 (               )
);

endmodule
