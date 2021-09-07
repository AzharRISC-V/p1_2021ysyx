
// ZhengpuShi

// Commit Interface (for difftest)

`include "defines.v"

module cmt_stage(
  input   wire                clk,
  input   wire                rst,
  input   reg                 i_cmt_writebacked_req,
  output  reg                 o_cmt_writebacked_ack,
  input   wire [4 : 0]        i_cmt_rd,
  input   wire                i_cmt_rd_wen,
  input   wire [`BUS_64]      i_cmt_rd_wdata,
  input   wire [`BUS_64]      i_cmt_pc,
  input   wire [`BUS_32]      i_cmt_inst,
  input   wire                i_cmt_skip_difftest,
  input   wire [`BUS_64]      i_cmt_regs[0 : 31],
  input   wire [`BUS_64]      i_cmt_csrs[0 :  7]
);

assign o_cmt_writebacked_ack = 1'b1;

wire writebacked_hs = i_cmt_writebacked_req & o_cmt_writebacked_ack;

// 保存输入信息

reg   [4 : 0]                 tmp_i_cmt_rd;
reg                           tmp_i_cmt_rd_wen;
reg   [`BUS_64]               tmp_i_cmt_rd_wdata;
reg   [`BUS_64]               tmp_i_cmt_pc;
reg   [`BUS_32]               tmp_i_cmt_inst;
reg                           tmp_i_cmt_skip_difftest;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_cmt_rd, 
      tmp_i_cmt_rd_wen, 
      tmp_i_cmt_rd_wdata,
      tmp_i_cmt_pc,
      tmp_i_cmt_inst,
      tmp_i_cmt_skip_difftest
    } <= 0;

  end
  else begin
    if (writebacked_hs) begin
      tmp_i_cmt_rd              <= i_cmt_rd; 
      tmp_i_cmt_rd_wen          <= i_cmt_rd_wen;
      tmp_i_cmt_rd_wdata        <= i_cmt_rd_wdata;
      tmp_i_cmt_pc              <= i_cmt_pc;
      tmp_i_cmt_inst            <= i_cmt_inst;
      tmp_i_cmt_skip_difftest   <= i_cmt_skip_difftest;
    end
  end
end

cmtU CmtU(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_rd                       (i_cmt_rd                   ),
  .i_rd_wen                   (i_cmt_rd_wen               ),
  .i_rd_wdata                 (i_cmt_rd_wdata             ),
  .i_pc                       (i_cmt_pc                   ),
  .i_inst                     (i_cmt_inst                 ),
  .i_skip_difftest            (i_cmt_skip_difftest        ),
  .i_regs                     (i_cmt_regs                 ),
  .i_csrs                     (i_cmt_csrs                 )
);

endmodule