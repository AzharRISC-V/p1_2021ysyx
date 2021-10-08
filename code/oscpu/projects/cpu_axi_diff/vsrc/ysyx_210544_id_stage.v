
// ZhengpuShi

// Instruction Decode Interface

`include "defines.v"

module ysyx_210544_id_stage(
  input   wire                clk,
  input   wire                rst,
  input   wire                i_id_fetched_req,
  input   wire                i_id_decoded_ack,
  output  reg                 o_id_decoded_req,
  input   wire  [`BUS_64]     i_id_pc,
  input   wire  [`BUS_32]     i_id_inst,
  input   wire  [`BUS_64]     i_id_rs1_data,
  input   wire  [`BUS_64]     i_id_rs2_data,
  input   wire                i_id_nocmt,
  output  wire  [`BUS_64]     o_id_pc,
  output  wire  [`BUS_32]     o_id_inst,
  output  wire                o_id_rs1_ren,
  output  wire  [`BUS_RIDX]   o_id_rs1,
  output  wire                o_id_rs2_ren,
  output  wire  [`BUS_RIDX]   o_id_rs2,
  output  wire  [`BUS_RIDX]   o_id_rd,
  output  wire                o_id_rd_wen,
  output  wire  [7 : 0]       o_id_inst_opcode,
  output  wire  [`BUS_64]     o_id_op1,
  output  wire  [`BUS_64]     o_id_op2,
  output  wire  [`BUS_64]     o_id_op3,
  output  wire                o_id_nocmt,
  output  wire                o_id_skipcmt
);

reg                           i_ena;    // 是否使能组合逻辑单元部件
wire                          i_disable;
// 保存输入信息
reg   [`BUS_64]               tmp_i_id_pc;
reg   [`BUS_32]               tmp_i_id_inst;
reg                           tmp_i_id_nocmt;

wire fetched_hs;
wire decoded_hs;



assign fetched_hs = i_id_fetched_req;
assign decoded_hs = i_id_decoded_ack & o_id_decoded_req;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_id_pc,
      tmp_i_id_inst,
      tmp_i_id_nocmt
    } <= 0;

    o_id_decoded_req      <= 0;
    i_ena                 <= 0;
  end
  else begin
    if (fetched_hs) begin
      tmp_i_id_pc         <= i_id_pc;
      tmp_i_id_inst       <= i_id_inst;
      tmp_i_id_nocmt      <= i_id_nocmt;

      o_id_decoded_req    <= 1;
      i_ena               <= 1;
    end
    else if (decoded_hs) begin
      o_id_decoded_req    <= 0;
      i_ena               <= 0;
    end
  end
end

assign i_disable = !i_ena;

assign o_id_pc      = i_disable ? 0 : tmp_i_id_pc;
assign o_id_inst    = i_disable ? 0 : tmp_i_id_inst;
assign o_id_nocmt   = i_disable ? 0 : tmp_i_id_nocmt;

ysyx_210544_idU IdU(
  .rst                        (rst                        ),
  .i_inst                     (tmp_i_id_inst              ),
  .i_rs1_data                 (i_id_rs1_data              ),
  .i_rs2_data                 (i_id_rs2_data              ),
  .i_pc                       (tmp_i_id_pc                ),
  .o_inst_opcode              (o_id_inst_opcode           ),
  .o_rs1_ren                  (o_id_rs1_ren               ),
  .o_rs1                      (o_id_rs1                   ),
  .o_rs2_ren                  (o_id_rs2_ren               ),
  .o_rs2                      (o_id_rs2                   ),
  .o_rd                       (o_id_rd                    ),
  .o_rd_wen                   (o_id_rd_wen                ),
  .o_op1                      (o_id_op1                   ),
  .o_op2                      (o_id_op2                   ),
  .o_op3                      (o_id_op3                   ),
  .o_skipcmt                  (o_id_skipcmt               )
);

endmodule
