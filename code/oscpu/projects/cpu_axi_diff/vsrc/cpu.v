
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

// if_stage
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
// instruction type : R,I,S,B,U,J
wire [2 : 0]                  id_itype_o;
wire [4 : 0]                  id_opcode_o;
wire [2 : 0]                  id_funct3_o;
wire [6 : 0]                  id_funct7_o;
wire [`BUS_64]                id_op1_o;
wire [`BUS_64]                id_op2_o;
// temp1
wire [`BUS_64]                id_t1_o;
wire                          id_skip_difftest_o;

// regfile -> id_stage
wire [`BUS_64]                rs1_data;
wire [`BUS_64]                rs2_data;
// regfile -> difftest
wire [`BUS_64]                regs[0 : 31];
wire [`BUS_64]                csrs[0 :  7];

// exe_stage
// exe_stage -> wb_stage
wire [4 : 0]                  ex_opcode_o;
wire                          ex_pc_jmp_o;
wire [`BUS_64]                ex_pc_jmpaddr_o;
wire                          ex_rd_wen_o;
wire [`BUS_64]                ex_rd_wdata_o;

// mem_stage
wire [`BUS_64]                mem_addr;
wire                          id_memren;
wire                          ex_memren;
reg  [`BUS_64]                mem_rdata;
wire                          id_memwen;
wire                          ex_memwen;
wire [`BUS_64]                mem_wdata;

// wb_stage
wire                          wb_rd_wen_i;
wire [`BUS_64]                wb_rd_wdata_i;
wire                          wb_rd_wen_o;
wire [`BUS_64]                wb_rd_wdata_o;

// // rd_write -> regfile
// wire                          rd_wen;
// wire [`BUS_64]                rd_wdata;

// csrfile
wire [11 : 0]                 csr_addr;
wire [1 : 0]                  csr_op;
wire [11 : 0]                 csr_waddr;
wire [`BUS_64]                csr_wdata;
wire [`BUS_64]                csr_rdata;

// exe_stage -> wb_stage
wire                          csr_rd_wen_o;
wire [`BUS_64]                csr_rd_wdata_o;

assign csr_rd_wen_o  = csr_op != 2'b00;
assign csr_rd_wdata_o = (csr_op == 2'b00) ? 0 : csr_rdata;

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

wire [`BUS_64]                id_pc_pred_o;
wire                          pipe_flush_req;
wire                          pipe_flush_ack;
wire  [`BUS_64]               pipe_flush_pc;
wire                          minidec_pc_jmp;
wire  [`BUS_64]               minidec_pc_jmpaddr;

if_stage If_stage(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .if_fetched_req             (fetched_req                ),
  .if_fetched_ack             (fetched_ack                ),
  .if_axi_valid_o             (if_valid                   ),
  .if_axi_ready_i             (if_ready                   ),
  .if_axi_data_read_i         (if_data_read               ),
  .if_axi_addr_o              (if_addr                    ),
  .if_axi_size_o              (if_size                    ),
  .if_axi_resp_i              (if_resp                    ),
  .if_pc_jmp_i                (ex_pc_jmp_o                ),
  .if_pc_jmpaddr_i            (ex_pc_jmpaddr_o            ),
  .if_pc_old_o                (if_pc_old_o                ),
  .if_pc_o                    (if_pc_o                    ),
  .if_pc_pred_o               (if_pc_pred_o               ),
  .if_inst_o                  (if_inst_o                  )
);

id_stage Id_stage(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .id_fetched_req_i           (fetched_req                ),
  .id_fetched_ack_o           (fetched_ack                ),
  .id_decoded_req_o           (decoded_req                ),
  .id_decoded_ack_i           (decoded_ack                ),
  .id_inst_i                  (if_inst_o                  ),
  .id_rs1_data_i              (rs1_data                   ),
  .id_rs2_data_i              (rs2_data                   ),
  .id_pc_old_i                (if_pc_old_o                ),
  .id_pc_i                    (if_pc_o                    ),
  .id_rs1_ren_o               (id_rs1_ren_o               ),
  .id_rs1_o                   (id_rs1_o                   ),
  .id_rs2_ren_o               (id_rs2_ren_o               ),
  .id_rs2_o                   (id_rs2_o                   ),
  .id_rd_o                    (id_rd_o                    ),
  .id_mem_addr_o              (mem_addr                   ),
  .id_mem_ren_o               (id_memren                  ),
  .id_mem_wen_o               (id_memwen                  ),
  .id_mem_wdata_o             (mem_wdata                  ),
  .id_itype_o                 (id_itype_o                 ),
  .id_opcode_o                (id_opcode_o                ),
  .id_funct3_o                (id_funct3_o                ),
  .id_funct7_o                (id_funct7_o                ),
  .id_op1_o                   (id_op1_o                   ),
  .id_op2_o                   (id_op2_o                   ),
  .id_t1_o                    (id_t1_o                    ),
  .id_csr_addr_o              (csr_addr                   ),
  .id_csr_op_o                (csr_op                     ),
  .id_csr_wdata_o             (csr_wdata                  ),
  .id_csr_rdata_i             (csr_rdata                  ),
  .id_pc_pred_i               (if_pc_pred_o               ),
  .id_pc_pred_o               (id_pc_pred_o               ),
  .id_skip_difftest_o         (id_skip_difftest_o         )
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
  .ex_memren_i                (id_memren                  ),
  .ex_memwen_i                (id_memwen                  ),
  .ex_pc_jmp_o                (ex_pc_jmp_o                ),
  .ex_pc_jmpaddr_o            (ex_pc_jmpaddr_o            ),
  .ex_rd_wen_o                (ex_rd_wen_o                ),
  .ex_rd_wdata_o              (ex_rd_wdata_o              ),
  .ex_memren_o                (ex_memren                  ),
  .ex_memwen_o                (ex_memwen                  )
);

mem_stage Mem_stage(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .mem_executed_req_i         (executed_req               ),
  .mem_executed_ack_o         (executed_ack               ),
  .mem_memoryed_req_o         (memoryed_req               ),
  .mem_memoryed_ack_i         (memoryed_ack               ),
  .mem_addr_i                 (mem_addr                   ),
  .mem_ren_i                  (ex_memren                  ),
  .mem_funct3_i               (id_funct3_o                ),
  .mem_wen_i                  (ex_memwen                  ),
  .mem_wdata_i                (mem_wdata                  ),
  .mem_rdata_o                (mem_rdata                  )
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
  .cmt_regs_i                 (regs                       ),
  .cmt_csrs_i                 (csrs                       )
);

regfile Regfile(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .rs1                        (id_rs1_o                   ),
  .rs1_ren                    (id_rs1_ren_o               ),
  .rs2                        (id_rs2_o                   ),
  .rs2_ren                    (id_rs2_ren_o               ),
  .rs1_data                   (rs1_data                   ),
  .rs2_data                   (rs2_data                   ),
  .rd                         (wb_rd_o                    ),
  .rd_wen                     (wb_rd_wen_o                ),
  .rd_data                    (wb_rd_wdata_o              ),
  .regs_o                     (regs                       )
);

csrfile Csrfile(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .csr_addr                   (csr_addr                   ),
  .csr_op                     (csr_op                     ),
  .csr_wdata                  (csr_wdata                  ),
  .csr_rdata                  (csr_rdata                  ),
  .csrs_o                     (csrs                       )
);




endmodule