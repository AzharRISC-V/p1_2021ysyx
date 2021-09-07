
// ZhengpuShi

// Instruction Decode Interface

`include "defines.v"

module id_stage(
  input   wire                clk,
  input   wire                rst,
  input   reg                 id_fetched_req_i,
  output  reg                 id_fetched_ack_o,
  input   reg                 id_decoded_ack_i,
  output  reg                 id_decoded_req_o,
  input   wire  [`BUS_32]     id_inst_i,
  input   wire  [`BUS_64]     id_rs1_data_i,
  input   wire  [`BUS_64]     id_rs2_data_i,
  input   wire  [`BUS_64]     id_pc_old_i,
  input   wire  [`BUS_64]     id_pc_i,
  output  reg                 id_rs1_ren_o,
  output  wire  [4 : 0]       id_rs1_o,
  output  wire                id_rs2_ren_o,
  output  wire  [4 : 0]       id_rs2_o,
  output  wire  [4 : 0]       id_rd_o,
  output  wire                id_memren_o,
  output  wire  [`BUS_64]     id_memaddr_o,
  output  wire                id_memwen_o,
  output  wire  [`BUS_64]     id_memwdata_o,
  output  reg   [11 : 0]      id_csr_addr_o,
  output  reg   [1 : 0]       id_csr_op_o,
  output  reg   [`BUS_64]     id_csr_wdata_o,
  input   reg   [`BUS_64]     id_csr_rdata_i,
  output  wire  [2 : 0]       id_itype_o,
  output  wire  [6 : 0]       id_opcode_o,
  output  wire  [2 : 0]       id_funct3_o,
  output  wire  [6 : 0]       id_funct7_o,
  output  wire  [`BUS_64]     id_op1_o,            // 两个操作数
  output  wire  [`BUS_64]     id_op2_o,
  output  wire  [`BUS_64]     id_t1_o,
  input   wire  [`BUS_64]     id_pc_pred_i,
  output  wire  [`BUS_64]     id_pc_pred_o,
  output  wire                id_skip_difftest_o
);


assign id_fetched_ack_o = 1'b1;

wire fetched_hs = id_fetched_req_i & id_fetched_ack_o;


// 保存输入信息
reg   [`BUS_32]               tmp_id_inst_i;
reg   [`BUS_64]               tmp_id_rs1_data_i;
reg   [`BUS_64]               tmp_id_rs2_data_i;
reg   [`BUS_64]               tmp_id_pc_old_i;
reg   [`BUS_64]               tmp_id_pc_i;
reg   [`BUS_64]               tmp_id_pc_pred_i;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_id_inst_i,
      tmp_id_rs1_data_i,
      tmp_id_rs2_data_i,
      tmp_id_pc_old_i,
      tmp_id_pc_i
    } <= 0;

    id_decoded_req_o <= 0;
  end
  else begin
    if (fetched_hs) begin
      tmp_id_inst_i       <= id_inst_i;
      tmp_id_rs1_data_i   <= id_rs1_data_i;
      tmp_id_rs2_data_i   <= id_rs2_data_i;
      tmp_id_pc_old_i     <= id_pc_old_i;
      tmp_id_pc_i         <= id_pc_i;
      tmp_id_pc_pred_i    <= id_pc_pred_i;

      id_decoded_req_o    <= 1;
    end
    else if (id_decoded_ack_i) begin
      id_decoded_req_o    <= 0;
    end
  end
end

// assign id_op1_o = tmp_op1;
// assign id_op2_o = tmp_op2;


idU IdU(
  .inst                       (tmp_id_inst_i              ),
  .rs1_data                   (tmp_id_rs1_data_i          ),
  .rs2_data                   (tmp_id_rs2_data_i          ),
  .pc_old                     (tmp_id_pc_old_i            ),
  .pc                         (tmp_id_pc_i                ),
  .rs1_ren                    (id_rs1_ren_o               ),
  .rs1                        (id_rs1_o                   ),
  .rs2_ren                    (id_rs2_ren_o               ),
  .rs2                        (id_rs2_o                   ),
  .rd                         (id_rd_o                    ),
  .memaddr                    (id_memaddr_o               ),
  .memren                     (id_memren_o                ),
  .memwen                     (id_memwen_o                ),
  .memwdata                   (id_memwdata_o              ),
  .itype                      (id_itype_o                 ),
  .opcode                     (id_opcode_o                ),
  .funct3                     (id_funct3_o                ),
  .funct7                     (id_funct7_o                ),
  .op1                        (id_op1_o                   ),
  .op2                        (id_op2_o                   ),
  .t1                         (id_t1_o                    ),
  .csr_addr                   (id_csr_addr_o              ),
  .csr_op                     (id_csr_op_o                ),
  .csr_wdata                  (id_csr_wdata_o             ),
  .csr_rdata                  (id_csr_rdata_i             ),
  .pc_pred_i                  (tmp_id_pc_pred_i           ),
  .pc_pred_o                  (id_pc_pred_o               ),
  .skip_difftest              (id_skip_difftest_o         )
);

endmodule
