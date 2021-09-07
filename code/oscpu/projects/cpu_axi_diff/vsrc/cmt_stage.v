
// ZhengpuShi

// Commit Interface (for difftest)

`include "defines.v"

module cmt_stage(
  input   wire                clk,
  input   wire                rst,
  input   reg                 cmt_writebacked_req_i,
  output  reg                 cmt_writebacked_ack_o,
  input   wire [4 : 0]        cmt_rd_i,
  input   wire                cmt_rd_wen_i,
  input   wire [`BUS_64]      cmt_rd_wdata_i,
  input   wire [`BUS_64]      cmt_pc_i,
  input   wire [`BUS_32]      cmt_inst_i,
  input   wire                cmt_skip_difftest_i,
  input   wire [`BUS_64]      cmt_regs_i[0 : 31],
  input   wire [`BUS_64]      cmt_csrs_i[0 :  7]
);

assign cmt_writebacked_ack_o = 1'b1;

wire writebacked_hs = cmt_writebacked_req_i & cmt_writebacked_ack_o;

// 保存输入信息

reg   [4 : 0]                 tmp_cmt_rd_i;
reg                           tmp_cmt_rd_wen_i;
reg   [`BUS_64]               tmp_cmt_rd_wdata_i;
reg   [`BUS_64]               tmp_cmt_pc_i;
reg   [`BUS_32]               tmp_cmt_inst_i;
reg                           tmp_cmt_skip_difftest_i;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_cmt_rd_i, 
      tmp_cmt_rd_wen_i, 
      tmp_cmt_rd_wdata_i,
      tmp_cmt_pc_i,
      tmp_cmt_inst_i,
      tmp_cmt_skip_difftest_i
    } <= 0;

  end
  else begin
    if (writebacked_hs) begin
      tmp_cmt_rd_i              <= cmt_rd_i; 
      tmp_cmt_rd_wen_i          <= cmt_rd_wen_i;
      tmp_cmt_rd_wdata_i        <= cmt_rd_wdata_i;
      tmp_cmt_pc_i              <= cmt_pc_i;
      tmp_cmt_inst_i            <= cmt_inst_i;
      tmp_cmt_skip_difftest_i   <= cmt_skip_difftest_i;
    end
  end
end

cmtU CmtU(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .rd                         (cmt_rd_i                   ),
  .rd_wen                     (cmt_rd_wen_i               ),
  .rd_wdata                   (cmt_rd_wdata_i             ),
  .pc                         (cmt_pc_i                   ),
  .inst                       (cmt_inst_i                 ),
  .skip_difftest              (cmt_skip_difftest_i        ),
  .regs                       (cmt_regs_i                 ),
  .csrs                       (cmt_csrs_i                 )
);

endmodule