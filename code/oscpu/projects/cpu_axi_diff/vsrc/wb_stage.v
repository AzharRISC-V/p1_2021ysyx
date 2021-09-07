
// Zhengpu Shi

// Writeback Interface

`include "defines.v"

module wb_stage(
  input   wire                clk,
  input   wire                rst,
  input   reg                 i_wb_memoryed_req,
  output  reg                 o_wb_memoryed_ack,
  output  reg                 o_wb_writebacked_req,
  input   reg                 i_wb_writebacked_ack,
  input   wire  [`BUS_64]     i_wb_pc,
  input   wire  [`BUS_32]     i_wb_inst,
  input   wire  [4 : 0]       i_wb_rd,
  input   wire                i_wb_rd_wen,
  input   wire  [`BUS_64]     i_wb_rd_wdata,
  output  wire  [`BUS_64]     o_wb_pc,
  output  wire  [`BUS_32]     o_wb_inst,
  output  reg   [4 : 0]       o_wb_rd,
  output  reg                 o_wb_rd_wen,
  output  wire  [`BUS_64]     o_wb_rd_wdata
  // input   wire                  csr_wen_i     ,   // CSR后的写回
  // input   wire  [`BUS_64]       csr_wdata_i   ,
);


assign o_wb_memoryed_ack = 1'b1;

wire memoryed_hs = i_wb_memoryed_req & o_wb_memoryed_ack;

// 保存输入信息
reg   [`BUS_64]               tmp_i_wb_pc;
reg   [`BUS_32]               tmp_i_wb_inst;
reg   [4 : 0]                 tmp_i_wb_rd;
reg                           tmp_i_wb_rd_wen;
reg   [`BUS_64]               tmp_i_wb_rd_wdata;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_wb_pc,
      tmp_i_wb_inst,
      tmp_i_wb_rd, 
      tmp_i_wb_rd_wen, 
      tmp_i_wb_rd_wdata
    } <= 0;

    o_wb_writebacked_req <= 0;
  end
  else begin
    if (memoryed_hs) begin
      tmp_i_wb_pc           <= i_wb_pc;
      tmp_i_wb_inst         <= i_wb_inst;
      tmp_i_wb_rd           <= i_wb_rd; 
      tmp_i_wb_rd_wen       <= i_wb_rd_wen;
      tmp_i_wb_rd_wdata     <= i_wb_rd_wdata;

      o_wb_writebacked_req <= 1;
    end
    else if (i_wb_writebacked_ack) begin
      o_wb_writebacked_req <= 0;
    end
  end
end

assign o_wb_pc = tmp_i_wb_pc;
assign o_wb_inst = tmp_i_wb_inst;

wbU WbU(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_rd                       (tmp_i_wb_rd                ),
  .i_rd_wen                   (tmp_i_wb_rd_wen            ),
  .i_rd_wdata                 (tmp_i_wb_rd_wdata          ),
  .o_rd                       (o_wb_rd                    ),
  .o_rd_wen                   (o_wb_rd_wen                ),
  .o_rd_wdata                 (o_wb_rd_wdata              )
);

endmodule
