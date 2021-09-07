
//--xuezhen--

`include "defines.v"

module cpu(
    input                     clk,
    input                     rst,
    input                     if_ready,
    input  [63:0]             if_data_read,
    input  [1:0]              if_resp,
    output                    if_valid,
    output [63:0]             if_addr,
    output [1:0]              if_size
);

// handshake between five stages
wire                          fetched_req;
wire                          fetched_ack;
wire                          decoded_req;
wire                          decoded_ack;
wire                          executed_req;
wire                          executed_ack;
wire                          memoryed_req;
wire                          memoryed_ack;
wire                          writebacked_req;
wire                          writebacked_ack;

// Unknown, developping
wire [`BUS_64]                id_pc_pred_o;
wire                          pipe_flush_req;
wire                          pipe_flush_ack;
wire  [`BUS_64]               pipe_flush_pc;
wire                          minidec_pc_jmp;
wire  [`BUS_64]               minidec_pc_jmpaddr;

// if_stage
// if_stage -> id_stage
wire [`BUS_64]                if_pc_old_o;
wire [`BUS_64]                if_pc_o;
wire [`BUS_64]                if_pc_pred_o;
wire [`BUS_32]                if_inst_o;
wire                          if_inst_start;
// id_stage -> regfile
wire                          id_rs1_ren_o;
wire [4 : 0]                  id_rs1_o;
wire                          id_rs2_ren_o;
wire [4 : 0]                  id_rs2_o;
wire [4 : 0]                  id_rd_o;
// id_stage -> exe_stage
wire [2 : 0]                  id_itype_o;
wire [6 : 0]                  id_opcode_o;
wire [2 : 0]                  id_funct3_o;
wire [6 : 0]                  id_funct7_o;
wire [`BUS_64]                id_op1_o;
wire [`BUS_64]                id_op2_o;
wire                          id_memaddr_o;
wire                          id_memren_o;
wire                          id_memwen_o;
wire [`BUS_64]                id_memwdata_o;
wire [`BUS_64]                id_t1_o;
wire                          id_skip_difftest_o;

// exe_stage
// exe_stage -> mem_stage
wire [2 : 0]                  ex_funct3_o;
wire [`BUS_64]                ex_memaddr_o;
wire                          ex_memren_o;
wire                          ex_memwen_o;
wire [`BUS_64]                ex_memwdata_o;
// exe_stage -> wb_stage
wire [4 : 0]                  ex_opcode_o;
wire                          ex_pc_jmp_o;
wire [`BUS_64]                ex_pc_jmpaddr_o;
wire                          ex_rd_wen_o;
wire [`BUS_64]                ex_rd_wdata_o;

// mem_stage
// mem_stage -> wb_stage
reg  [`BUS_64]                mem_rdata_o;

// wb_stage
// wb_stage -> cmt_stage
wire                          wb_rd_wen_i;
wire [`BUS_64]                wb_rd_wdata_i;
wire                          wb_rd_wen_o;
wire [`BUS_64]                wb_rd_wdata_o;

// regfile
// regfile -> id_stage
wire [`BUS_64]                reg_id_rs1_data_o;
wire [`BUS_64]                reg_id_rs2_data_o;
// regfile -> difftest
wire [`BUS_64]                reg_regs_o[0 : 31];

// csrfile
// csrfile -> ex_stage
wire [`BUS_64]                csr_csrs_o[0 :  7];
wire [11 : 0]                 csr_addr;
wire [1 : 0]                  csr_op;
wire [11 : 0]                 csr_waddr;
wire [`BUS_64]                csr_wdata;
wire [`BUS_64]                csr_rdata;
// csrfile -> wb_stage
wire                          csr_rd_wen_o;
wire [`BUS_64]                csr_rd_wdata_o;

assign csr_rd_wen_o  = csr_op != 2'b00;
assign csr_rd_wdata_o = (csr_op == 2'b00) ? 0 : csr_rdata;

/////////////////////////////////////////////////
// Stages
if_stage If_stage(
  .i_clk                      (clk                        ),
  .i_rst                      (rst                        ),
  .o_if_fetched_req           (fetched_req                ),
  .i_if_fetched_ack           (fetched_ack                ),
  .o_if_axi_valid             (if_valid                   ),
  .i_if_axi_ready             (if_ready                   ),
  .i_if_axi_data_read         (if_data_read               ),
  .o_if_axi_addr              (if_addr                    ),
  .o_if_axi_size              (if_size                    ),
  .i_if_axi_resp              (if_resp                    ),
  .i_if_pc_jmp                (ex_pc_jmp_o                ),
  .i_if_pc_jmpaddr            (ex_pc_jmpaddr_o            ),
  .o_if_pc_old                (if_pc_old_o                ),
  .o_if_pc                    (if_pc_o                    ),
  .o_if_pc_pred               (if_pc_pred_o               ),
  .o_if_inst                  (if_inst_o                  )
);

id_stage Id_stage(
  .i_clk                      (clk                        ),
  .i_rst                      (rst                        ),
  .i_id_fetched_req           (fetched_req                ),
  .o_id_fetched_ack           (fetched_ack                ),
  .o_id_decoded_req           (decoded_req                ),
  .i_id_decoded_ack           (decoded_ack                ),
  .i_id_inst                  (if_inst_o                  ),
  .i_id_rs1_data              (reg_id_rs1_data_o          ),
  .i_id_rs2_data              (reg_id_rs2_data_o          ),
  .i_id_pc_old                (if_pc_old_o                ),
  .i_id_pc                    (if_pc_o                    ),
  .o_id_rs1_ren               (id_rs1_ren_o               ),
  .o_id_rs1                   (id_rs1_o                   ),
  .o_id_rs2_ren               (id_rs2_ren_o               ),
  .o_id_rs2                   (id_rs2_o                   ),
  .o_id_rd                    (id_rd_o                    ),
  .o_id_memaddr               (id_memaddr_o               ),
  .o_id_memren                (id_memren_o                ),
  .o_id_memwen                (id_memwen_o                ),
  .o_id_memwdata              (id_memwdata_o              ),
  .o_id_itype                 (id_itype_o                 ),
  .o_id_opcode                (id_opcode_o                ),
  .o_id_funct3                (id_funct3_o                ),
  .o_id_funct7                (id_funct7_o                ),
  .o_id_op1                   (id_op1_o                   ),
  .o_id_op2                   (id_op2_o                   ),
  .o_id_t1                    (id_t1_o                    ),
  .o_id_csr_addr              (csr_addr                   ),
  .o_id_csr_op                (csr_op                     ),
  .o_id_csr_wdata             (csr_wdata                  ),
  .i_id_csr_rdata             (csr_rdata                  ),
  .i_id_pc_pred               (if_pc_pred_o               ),
  .o_id_pc_pred               (id_pc_pred_o               ),
  .o_id_skip_difftest         (id_skip_difftest_o         )
);

exe_stage Exe_stage(
  .rst                        (rst                        ),
  .clk                        (clk                        ),
  .ex_decoded_req_i           (decoded_req                ),
  .ex_decoded_ack_o           (decoded_ack                ),
  .ex_executed_req_o          (executed_req               ),
  .ex_executed_ack_i          (executed_ack               ),
  .ex_opcode_i                (id_opcode_o                ),
  .ex_funct3_i                (id_funct3_o                ),
  .ex_funct7_i                (id_funct7_o                ),
  .ex_op1_i                   (id_op1_o                   ),
  .ex_op2_i                   (id_op2_o                   ),
  .ex_t1_i                    (id_t1_o                    ),
  .ex_pc_pred_i               (id_pc_pred_o               ),
  .ex_memren_i                (id_memren_o                ),
  .ex_memwen_i                (id_memwen_o                ),
  .ex_pc_jmp_o                (ex_pc_jmp_o                ),
  .ex_pc_jmpaddr_o            (ex_pc_jmpaddr_o            ),
  .ex_rd_wen_o                (ex_rd_wen_o                ),
  .ex_rd_wdata_o              (ex_rd_wdata_o              ),
  .ex_memren_o                (ex_memren_o                ),
  .ex_memwen_o                (ex_memwen_o                )
);

mem_stage Mem_stage(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .mem_executed_req_i         (executed_req               ),
  .mem_executed_ack_o         (executed_ack               ),
  .mem_memoryed_req_o         (memoryed_req               ),
  .mem_memoryed_ack_i         (memoryed_ack               ),
  .mem_addr_i                 (ex_memaddr_o               ),
  .mem_ren_i                  (ex_memren_o                ),
  .mem_wen_i                  (ex_memwen_o                ),
  .mem_wdata_i                (ex_memwdata_o              ),
  .mem_funct3_i               (ex_funct3_o                ),
  .mem_rdata_o                (mem_rdata_o                )
);


wire  [4 : 0]                 wb_rd_o;
reg                           wb_rd_wen_o;
wire  [`BUS_64]               wb_rd_wdata_o;

wb_stage Wb_stage(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .wb_memoryed_req_i          (memoryed_req               ),
  .wb_memoryed_ack_o          (memoryed_ack               ),
  .wb_writebacked_req_o       (writebacked_req            ),
  .wb_writebacked_ack_i       (writebacked_ack            ),
  .wb_rd_i                    (ex_rd_wen_o                ),
  .wb_rd_wen_i                (ex_rd_wen_o                ),
  .wb_rd_wdata_i              (ex_rd_wdata_o              ),
  .wb_rd_o                    (wb_rd_o                    ),
  .wb_rd_wen_o                (wb_rd_wen_o                ),
  .wb_rd_wdata_o              (wb_rd_wdata_o              )
  // .ex_wen_i                   (ex_rd_wen_o                ),
  // .ex_wdata_i                 (ex_rd_wdata_o              ),
  // .mem_wen_i                  (ex_memwen                  ),
  // .mem_wdata_i                (mem_rdata                  ),
  // .csr_wen_i                  (csr_rd_wen_o               ),
  // .csr_wdata_i                (csr_rd_wdata_o             ),
  // .wen_o                      (rd_wen                     ),
  // .wdata_o                    (rd_wdata                   )
);

cmt_stage Cmt_stage(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .cmt_writebacked_req_i      (writebacked_req            ),
  .cmt_writebacked_ack_o      (writebacked_ack            ),
  .cmt_rd_i                   (wb_rd_o                    ),
  .cmt_rd_wen_i               (wb_rd_wen_o                ),
  .cmt_rd_wdata_i             (wb_rd_wdata_o              ),
  .cmt_pc_i                   (if_pc_o                    ),
  .cmt_inst_i                 (if_inst_o                  ),
  .cmt_skip_difftest_i        (id_skip_difftest_o         ),
  .cmt_regs_i                 (reg_regs_o                 ),
  .cmt_csrs_i                 (csr_csrs_o                 )
);

regfile Regfile(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .rs1                        (id_rs1_o                   ),
  .rs1_ren                    (id_rs1_ren_o               ),
  .rs2                        (id_rs2_o                   ),
  .rs2_ren                    (id_rs2_ren_o               ),
  .rd                         (wb_rd_o                    ),
  .rd_wen                     (wb_rd_wen_o                ),
  .rd_data                    (wb_rd_wdata_o              ),
  .rs1_data                   (reg_id_rs1_data_o          ),
  .rs2_data                   (reg_id_rs2_data_o          ),
  .regs_o                     (reg_regs_o                 )
);

csrfile Csrfile(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .csr_addr                   (csr_addr                   ),
  .csr_op                     (csr_op                     ),
  .csr_wdata                  (csr_wdata                  ),
  .csr_rdata                  (csr_rdata                  ),
  .csrs_o                     (csr_csrs_o                 )
);




endmodule