
// ZhengpuShi

// Instruction Decode Interface

`include "defines.v"

module id_stage(
  input   wire                clk,
  input   wire                rst,
  input   reg                 i_id_fetched_req,
  output  reg                 o_id_fetched_ack,
  input   reg                 i_id_decoded_ack,
  output  reg                 o_id_decoded_req,
  input   wire  [`BUS_64]     i_id_pc,
  input   wire  [`BUS_32]     i_id_inst,
  input   wire  [`BUS_64]     i_id_rs1_data,
  input   wire  [`BUS_64]     i_id_rs2_data,
  input   wire  [`BUS_64]     i_id_pc_old,
  output  wire  [`BUS_64]     o_id_pc,
  output  wire  [`BUS_32]     o_id_inst,
  output  reg                 o_id_rs1_ren,
  output  wire  [4 : 0]       o_id_rs1,
  output  wire                o_id_rs2_ren,
  output  wire  [4 : 0]       o_id_rs2,
  output  wire  [4 : 0]       o_id_rd,
  output  wire                o_id_memren,
  output  wire  [`BUS_64]     o_id_memaddr,
  output  wire                o_id_memwen,
  output  wire  [`BUS_64]     o_id_memwdata,
  output  reg   [11 : 0]      o_id_csr_addr,
  output  reg   [1 : 0]       o_id_csr_op,
  output  reg   [`BUS_64]     o_id_csr_wdata,
  input   reg   [`BUS_64]     i_id_csr_rdata,
  output  wire  [2 : 0]       o_id_itype,
  output  wire  [6 : 0]       o_id_opcode,
  output  wire  [2 : 0]       o_id_funct3,
  output  wire  [6 : 0]       o_id_funct7,
  output  wire  [`BUS_64]     o_id_op1,
  output  wire  [`BUS_64]     o_id_op2,
  output  wire  [`BUS_64]     o_id_t1,
  input   wire  [`BUS_64]     i_id_pc_pred,
  output  wire  [`BUS_64]     o_id_pc_pred,
  output  wire                o_id_skip_difftest
);


assign o_id_fetched_ack = 1'b1;

wire fetched_hs = i_id_fetched_req & o_id_fetched_ack;


// 是否使能组合逻辑单元部件
reg                           i_ena;


// 保存输入信息
reg   [`BUS_32]               tmp_i_id_inst;
reg   [`BUS_64]               tmp_i_id_pc_old;
reg   [`BUS_64]               tmp_i_id_pc;
reg   [`BUS_64]               tmp_i_id_pc_pred;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_id_inst,
      tmp_i_id_pc_old,
      tmp_i_id_pc
    } <= 0;

    o_id_decoded_req      <= 0;
    i_ena                 <= 0;
  end
  else begin
    if (fetched_hs) begin
      tmp_i_id_inst       <= i_id_inst;
      tmp_i_id_pc_old     <= i_id_pc_old;
      tmp_i_id_pc         <= i_id_pc;
      tmp_i_id_pc_pred    <= i_id_pc_pred;

      o_id_decoded_req    <= 1;
      i_ena               <= 1;
    end
    else if (i_id_decoded_ack) begin
      o_id_decoded_req    <= 0;
      i_ena               <= 0;
    end
  end
end

wire i_disable = !i_ena;

assign o_id_pc      = i_disable ? 0 : tmp_i_id_pc;
assign o_id_inst    = i_disable ? 0 : tmp_i_id_inst;
// assign id_op1_o = tmp_op1;
// assign id_op2_o = tmp_op2;


idU IdU(
  .i_ena                      (i_ena                      ),
  .i_inst                     (tmp_i_id_inst              ),
  .i_rs1_data                 (i_id_rs1_data              ),
  .i_rs2_data                 (i_id_rs2_data              ),
  .i_pc_old                   (tmp_i_id_pc_old            ),
  .i_pc                       (tmp_i_id_pc                ),
  .o_rs1_ren                  (o_id_rs1_ren               ),
  .o_rs1                      (o_id_rs1                   ),
  .o_rs2_ren                  (o_id_rs2_ren               ),
  .o_rs2                      (o_id_rs2                   ),
  .o_rd                       (o_id_rd                    ),
  .o_memaddr                  (o_id_memaddr               ),
  .o_memren                   (o_id_memren                ),
  .o_memwen                   (o_id_memwen                ),
  .o_memwdata                 (o_id_memwdata              ),
  .o_itype                    (o_id_itype                 ),
  .o_opcode                   (o_id_opcode                ),
  .o_funct3                   (o_id_funct3                ),
  .o_funct7                   (o_id_funct7                ),
  .o_op1                      (o_id_op1                   ),
  .o_op2                      (o_id_op2                   ),
  .o_t1                       (o_id_t1                    ),
  .o_csr_addr                 (o_id_csr_addr              ),
  .o_csr_op                   (o_id_csr_op                ),
  .o_csr_wdata                (o_id_csr_wdata             ),
  .i_csr_rdata                (i_id_csr_rdata             ),
  .i_pc_pred                  (tmp_i_id_pc_pred           ),
  .o_pc_pred                  (o_id_pc_pred               ),
  .o_skip_difftest            (o_id_skip_difftest         )
);

endmodule
