
// ZhengpuShi

// Commit Interface (for difftest)

`ifdef DIFFTEST_YSYX_210544

`include "defines.v"

module ysyx_210544_cmt_stage(
  input   wire                clk,
  input   wire                rst,
  input   wire                i_cmt_writebacked_req,
  output  reg                 o_cmt_writebacked_ack,
  input   wire [4 : 0]        i_cmt_rd,
  input   wire                i_cmt_rd_wen,
  input   wire [`BUS_64]      i_cmt_rd_wdata,
  input   wire [`BUS_64]      i_cmt_pc,
  input   wire [`BUS_32]      i_cmt_inst,
  input   wire                i_cmt_skipcmt,
  input   wire [`BUS_64]      i_cmt_regs[0:31],
  input   wire [`BUS_64]      i_cmt_csrs_mstatus,
  input   wire [`BUS_64]      i_cmt_csrs_mie,
  input   wire [`BUS_64]      i_cmt_csrs_mtvec,
  input   wire [`BUS_64]      i_cmt_csrs_mscratch,
  input   wire [`BUS_64]      i_cmt_csrs_mepc,
  input   wire [`BUS_64]      i_cmt_csrs_mcause,
  input   wire [`BUS_32]      i_cmt_intrNo
);

assign o_cmt_writebacked_ack = 1'b1;


wire writebacked_hs;
wire i_cmtvalid;

assign writebacked_hs = i_cmt_writebacked_req & o_cmt_writebacked_ack;
assign i_cmtvalid = writebacked_hs;

ysyx_210544_cmtU CmtU(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_rd                       (i_cmt_rd                   ),
  .i_rd_wen                   (i_cmt_rd_wen               ),
  .i_rd_wdata                 (i_cmt_rd_wdata             ),
  .i_pc                       (i_cmt_pc                   ),
  .i_inst                     (i_cmt_inst                 ),
  .i_cmtvalid                 (i_cmtvalid                 ),
  .i_skipcmt                  (i_cmt_skipcmt              ),
  .i_regs                     (i_cmt_regs                 ),
  .i_csrs_mstatus             (i_cmt_csrs_mstatus         ),
  .i_csrs_mie                 (i_cmt_csrs_mie             ),
  .i_csrs_mtvec               (i_cmt_csrs_mtvec           ),
  .i_csrs_mscratch            (i_cmt_csrs_mscratch        ),
  .i_csrs_mepc                (i_cmt_csrs_mepc            ),
  .i_csrs_mcause              (i_cmt_csrs_mcause          ),
  .i_intrNo                   (i_cmt_intrNo               )
);

reg [63:0] cnt;
always @(posedge clk) begin
  if (rst) begin
    cnt <= 1;
  end
  else begin
    
    // 判断停机
    if (i_cmt_inst == 32'h6b) begin
      if (i_cmt_regs[10] == 0) begin
        $display("*****SUCCESS!");
      end
      else begin
        $display("!!!!!FAIL!");
      end
      $finish();
    end

    // 打印执行情况
    // if (i_cmtvalid) begin
    //   cnt <= cnt + 1;
    //   if (cnt[4:0] == 0) begin
    //     $displayh("[cnt:", cnt, ", pc:", i_cmt_pc, "]");
    //   end
    // end


  end
end

wire _unused_ok = &{1'b0,
  cnt,
  1'b0};

endmodule

`endif
