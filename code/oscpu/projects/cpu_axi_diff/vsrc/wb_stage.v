
// Zhengpu Shi

// Writeback Interface

`include "defines.v"

module wb_stage(
  input   wire                  clk,
  input   wire                  rst,
  input   reg                   wb_memoryed_req_i,
  output  reg                   wb_memoryed_ack_o,
  output  reg                   wb_writebacked_req_o,
  input   reg                   wb_writebacked_ack_i,

  input   wire  [4 : 0]         wb_rd_i,
  input   wire                  wb_rd_wen_i,
  input   wire  [`BUS_64]       wb_rd_wdata_i,
  output  reg   [4 : 0]         wb_rd_o,
  output  reg                   wb_rd_wen_o,
  output  wire  [`BUS_64]       wb_rd_wdata_o
  // input   wire                  csr_wen_i     ,   // CSR后的写回
  // input   wire  [`BUS_64]       csr_wdata_i   ,
);


assign wb_memoryed_ack_o = 1'b1;

wire memoryed_hs = wb_memoryed_req_i & wb_memoryed_ack_o;

// 保存输入信息
reg   [4 : 0]         tmp_wb_rd_i;
reg                   tmp_wb_rd_wen_i;
reg   [`BUS_64]       tmp_wb_rd_wdata_i;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_wb_rd_i, 
      tmp_wb_rd_wen_i, 
      tmp_wb_rd_wdata_i
    } <= 0;

    wb_writebacked_req_o <= 0;
  end
  else begin
    if (memoryed_hs) begin
      tmp_wb_rd_i           <= wb_rd_i; 
      tmp_wb_rd_wen_i       <= wb_rd_wen_i;
      tmp_wb_rd_wdata_i     <= wb_rd_wdata_i;

      wb_writebacked_req_o <= 1;
    end
    else if (wb_writebacked_ack_i) begin
      wb_writebacked_req_o <= 0;
    end
  end
end

wbU WbU(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .rd_i                       (tmp_wb_rd_i                ),
  .rd_wen_i                   (tmp_wb_rd_wen_i            ),
  .rd_wdata_i                 (tmp_wb_rd_wdata_i          ),
  .rd_o                       (wb_rd_o                    ),
  .rd_wen_o                   (wb_rd_wen_o                ),
  .rd_wdata_o                 (wb_rd_wdata_o              )
);

endmodule
