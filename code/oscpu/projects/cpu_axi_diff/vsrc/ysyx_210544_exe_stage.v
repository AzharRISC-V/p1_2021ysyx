
// ZhengpuShi

// Execute Interface

`include "defines.v"

module ysyx_210544_exe_stage(
  input   wire                rst,
  input   wire                clk,
  input   wire                i_ex_decoded_req,
  output  wire                o_ex_decoded_ack,
  output  reg                 o_ex_executed_req,
  input   wire                i_ex_executed_ack,
  input   wire  [7 : 0]       i_ex_inst_opcode,
  input   wire  [`YSYX210544_BUS_64]     i_ex_pc,
  input   wire  [`YSYX210544_BUS_32]     i_ex_inst,
  input   wire  [`YSYX210544_BUS_64]     i_ex_op1,
  input   wire  [`YSYX210544_BUS_64]     i_ex_op2,
  input   wire  [`YSYX210544_BUS_64]     i_ex_op3,
  input   wire  [`YSYX210544_BUS_RIDX]   i_ex_rd,
  input   wire                i_ex_rd_wen,
  input   wire                i_ex_clint_mstatus_mie,
  input   wire                i_ex_clint_mie_mtie,
  input   wire                i_ex_clint_mtime_overflow,
  input   wire                i_ex_skipcmt,
  input   wire  [`YSYX210544_BUS_64]     i_ex_csr_rdata,
  output  wire  [11 : 0]      o_ex_csr_addr,
  output  wire                o_ex_csr_ren,
  output  wire                o_ex_csr_wen,
  output  wire  [`YSYX210544_BUS_64]     o_ex_csr_wdata,
  output  wire  [`YSYX210544_BUS_64]     o_ex_pc,
  output  wire  [`YSYX210544_BUS_32]     o_ex_inst,
  output  wire                o_ex_pc_jmp,
  output  wire  [`YSYX210544_BUS_64]     o_ex_pc_jmpaddr,
  output  wire  [`YSYX210544_BUS_RIDX]   o_ex_rd,
  output  wire                o_ex_rd_wen,
  output  wire  [`YSYX210544_BUS_64]     o_ex_rd_wdata,
  output  wire  [7 : 0]       o_ex_inst_opcode,
  output  wire  [`YSYX210544_BUS_64]     o_ex_op1,
  output  wire  [`YSYX210544_BUS_64]     o_ex_op2,
  output  wire  [`YSYX210544_BUS_64]     o_ex_op3,
  output  wire                o_ex_skipcmt,
  output  reg   [`YSYX210544_BUS_32]     o_ex_intrNo
);

wire                          i_disable;

wire                          decoded_hs;
wire                          executed_hs;
wire                          exeU_skip_cmt;

wire                          is_inst_exceptionU;    // ????????????????????????ecall, mret
wire                          is_time_int_req;       // ??????????????????????????????

// ????????????
reg                           o_ena_exeU;
reg                           o_ena_exceptionU;

wire                          exeU_pc_jmp;
wire [`YSYX210544_BUS_64]                exeU_pc_jmpaddr;
wire   [11 : 0]               exeU_csr_addr;
wire                          exeU_csr_ren;
wire                          exeU_csr_wen;
wire   [`YSYX210544_BUS_64]              exeU_csr_wdata;

wire                          exceptionU_req;
wire                          exceptionU_pc_jmp;
wire [`YSYX210544_BUS_64]                exceptionU_pc_jmpaddr;
wire   [11 : 0]               exceptionU_csr_addr;
wire                          exceptionU_csr_ren;
wire                          exceptionU_csr_wen;
wire   [`YSYX210544_BUS_64]              exceptionU_csr_wdata;

// ??????????????????
reg   [7 : 0]                 tmp_i_ex_inst_opcode;
reg   [`YSYX210544_BUS_64]               tmp_i_ex_pc;
reg   [`YSYX210544_BUS_32]               tmp_i_ex_inst;
reg   [`YSYX210544_BUS_64]               tmp_i_ex_op1;
reg   [`YSYX210544_BUS_64]               tmp_i_ex_op2;
reg   [`YSYX210544_BUS_64]               tmp_i_ex_op3;
reg   [4 : 0]                 tmp_i_ex_rd;
reg                           tmp_i_ex_rd_wen;
reg                           tmp_i_ex_skipcmt;



assign i_disable = rst | (!executed_hs);

assign o_ex_decoded_ack = 1'b1;

assign decoded_hs = i_ex_decoded_req & o_ex_decoded_ack;
assign executed_hs = i_ex_executed_ack & o_ex_executed_req;

assign is_inst_exceptionU = (i_ex_inst_opcode == `YSYX210544_INST_ECALL) | (i_ex_inst_opcode == `YSYX210544_INST_MRET);
assign is_time_int_req = i_ex_clint_mstatus_mie & i_ex_clint_mie_mtie & i_ex_clint_mtime_overflow;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_ex_inst_opcode,
      tmp_i_ex_pc,
      tmp_i_ex_inst,
      tmp_i_ex_op1, 
      tmp_i_ex_op2, 
      tmp_i_ex_op3,
      tmp_i_ex_rd,
      tmp_i_ex_rd_wen,
      tmp_i_ex_skipcmt
    } <= 0;

    o_ena_exeU          <= 0;
    o_ena_exceptionU    <= 0;
    o_ex_executed_req   <= 0;
    o_ex_intrNo         <= 0;
  end
  else begin
    // ??????
    if (decoded_hs) begin
      tmp_i_ex_inst_opcode <= i_ex_inst_opcode;
      tmp_i_ex_pc       <= i_ex_pc;
      tmp_i_ex_inst     <= i_ex_inst;
      tmp_i_ex_op1      <= i_ex_op1;
      tmp_i_ex_op2      <= i_ex_op2;
      tmp_i_ex_op3      <= i_ex_op3;
      tmp_i_ex_rd       <= i_ex_rd;
      tmp_i_ex_rd_wen   <= i_ex_rd_wen;
      tmp_i_ex_skipcmt  <= i_ex_skipcmt;
      
      o_ex_intrNo <= is_time_int_req ? 7 : 0;

      // ????????????
      if (!is_inst_exceptionU && !is_time_int_req) begin
        o_ena_exeU        <= 1;
        // exeU?????????????????????????????????
        o_ex_executed_req <= 1;
      end
      else begin
        o_ena_exceptionU  <= 1;
      end
    end
    // exceptionU???????????????????????????
    else if (exceptionU_req) begin
      o_ex_executed_req <= 1;
    end
    // exeU???exceptionU?????????????????????????????????
    else if (executed_hs) begin
      o_ena_exeU        <= 0;
      o_ena_exceptionU  <= 0;
      o_ex_executed_req <= 0;
      o_ex_intrNo       <= 0;
    end
  end
end

assign o_ex_pc            = i_disable ? 64'd0 : tmp_i_ex_pc;
assign o_ex_inst          = i_disable ? 32'd0 : tmp_i_ex_inst;
assign o_ex_op1           = i_disable ? 64'd0 : tmp_i_ex_op1;
assign o_ex_op2           = i_disable ? 64'd0 : tmp_i_ex_op2;
assign o_ex_op3           = i_disable ? 64'd0 : tmp_i_ex_op3;
assign o_ex_inst_opcode   = i_disable ?  8'd0 : tmp_i_ex_inst_opcode;
assign o_ex_rd            = i_disable ?  5'd0 : (!o_ena_exeU ? 5'd0 : tmp_i_ex_rd);
assign o_ex_rd_wen        = i_disable ?  1'd0 : (!o_ena_exeU ? 1'd0 : tmp_i_ex_rd_wen);
assign o_ex_skipcmt       = i_disable ?  1'd0 : (tmp_i_ex_skipcmt | exeU_skip_cmt);

assign o_ex_pc_jmp      = rst ?  1'd0 : (o_ena_exeU ? exeU_pc_jmp     : exceptionU_pc_jmp);
assign o_ex_pc_jmpaddr  = rst ? 64'd0 : (o_ena_exeU ? exeU_pc_jmpaddr : exceptionU_pc_jmpaddr);
assign o_ex_csr_addr    = rst ? 12'd0 : (o_ena_exeU ? exeU_csr_addr   : exceptionU_csr_addr);
assign o_ex_csr_ren     = rst ?  1'd0 : (o_ena_exeU ? exeU_csr_ren    : exceptionU_csr_ren);
assign o_ex_csr_wen     = rst ?  1'd0 : (o_ena_exeU ? exeU_csr_wen    : exceptionU_csr_wen);
assign o_ex_csr_wdata   = rst ? 64'd0 : (o_ena_exeU ? exeU_csr_wdata  : exceptionU_csr_wdata);

ysyx_210544_exeU ExeU(
  .ena                        (o_ena_exeU                 ),
  .i_inst_opcode              (tmp_i_ex_inst_opcode       ),
  .i_op1                      (tmp_i_ex_op1               ),
  .i_op2                      (tmp_i_ex_op2               ),
  .i_op3                      (tmp_i_ex_op3               ),
  .i_csr_rdata                (i_ex_csr_rdata             ),
  .o_csr_addr                 (exeU_csr_addr              ),
  .o_csr_ren                  (exeU_csr_ren               ),
  .o_csr_wen                  (exeU_csr_wen               ),
  .o_csr_wdata                (exeU_csr_wdata             ),
  .o_pc_jmp                   (exeU_pc_jmp                ),
  .o_pc_jmpaddr               (exeU_pc_jmpaddr            ),
  .o_rd_wdata                 (o_ex_rd_wdata              ),
  .o_exeU_skip_cmt            (exeU_skip_cmt              )
);

ysyx_210544_exceptionU ExceptionU(
  .rst                        (rst                        ),
  .clk                        (clk                        ),
  .ena                        (o_ena_exceptionU & (!o_ex_executed_req)),
  .ack                        (i_ex_executed_ack          ),
  .req                        (exceptionU_req             ),
  .i_inst_opcode              (i_ex_inst_opcode           ),
  .i_pc                       (tmp_i_ex_pc                ),
  .i_csr_rdata                (i_ex_csr_rdata             ),
  .o_pc_jmp                   (exceptionU_pc_jmp          ),
  .o_pc_jmpaddr               (exceptionU_pc_jmpaddr      ),
  .o_csr_addr                 (exceptionU_csr_addr        ),
  .o_csr_ren                  (exceptionU_csr_ren         ),
  .o_csr_wen                  (exceptionU_csr_wen         ),
  .o_csr_wdata                (exceptionU_csr_wdata       )
);

endmodule
