
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
wire [`BUS_64]                o_if_pc_old;
wire [`BUS_64]                o_if_pc;
wire [`BUS_64]                o_if_pc_pred;
wire [`BUS_32]                o_if_inst;
// id_stage -> regfile
wire                          o_id_rs1_ren;
wire [4 : 0]                  o_id_rs1;
wire                          o_id_rs2_ren;
wire [4 : 0]                  o_id_rs2;
wire [4 : 0]                  o_id_rd;
// id_stage -> csrfile
wire [11 : 0]                 o_id_csraddr;
wire [1 : 0]                  o_id_csrop;
wire [11 : 0]                 o_id_csrwaddr;
wire [`BUS_64]                o_id_csrwdata;
// id_stage -> exe_stage
wire [2 : 0]                  o_id_itype;
wire [6 : 0]                  o_id_opcode;
wire [2 : 0]                  o_id_funct3;
wire [6 : 0]                  o_id_funct7;
wire [`BUS_64]                o_id_op1;
wire [`BUS_64]                o_id_op2;
wire                          o_id_memaddr;
wire                          o_id_memren;
wire                          o_id_memwen;
wire [`BUS_64]                o_id_memwdata;
wire [`BUS_64]                o_id_t1;
wire                          o_id_skip_difftest;
wire [`BUS_64]                o_id_pc;
wire [`BUS_32]                o_id_inst;

// exe_stage
// exe_stage -> mem_stage
wire [2 : 0]                  o_ex_funct3;
wire [`BUS_64]                o_ex_memaddr;
wire                          o_ex_memren;
wire                          o_ex_memwen;
wire [`BUS_64]                o_ex_memwdata;
wire [`BUS_64]                o_ex_pc;
wire [`BUS_32]                o_ex_inst;
wire [4 : 0]                  o_ex_opcode;
wire                          o_ex_pc_jmp;
wire [`BUS_64]                o_ex_pc_jmpaddr;
wire                          o_ex_rd_wen;
wire [`BUS_64]                o_ex_rd_wdata;
wire                          o_ex_skip_difftest;

// mem_stage
// mem_stage -> wb_stage
reg  [`BUS_64]                o_mem_rdata;
wire [`BUS_64]                o_mem_pc;
wire [`BUS_32]                o_mem_inst;
wire                          o_mem_skip_difftest;

// wb_stage
// wb_stage -> cmt_stage
wire [`BUS_64]                o_wb_pc;
wire [`BUS_32]                o_wb_inst;
wire                          o_wb_rd_wen;
wire [`BUS_64]                o_wb_rd_wdata;
wire                          o_wb_skip_difftest;

// regfile
// regfile -> id_stage
wire [`BUS_64]                o_reg_id_rs1_data;
wire [`BUS_64]                o_reg_id_rs2_data;
// regfile -> difftest
wire [`BUS_64]                o_reg_regs[0 : 31];

// csrfile
// csrfile -> ex_stage
wire [`BUS_64]                o_csr_rdata;
wire [`BUS_64]                o_csr_csrs[0 :  7];
// csrfile -> wb_stage
wire                          o_csr_rd_wen;
wire [`BUS_64]                o_csr_rd_wdata;

assign o_csr_rd_wen  = o_id_csrop != 2'b00;
assign o_csr_rd_wdata = (o_id_csrop == 2'b00) ? 0 : o_csr_rdata;

/////////////////////////////////////////////////
// Stages
if_stage If_stage(
  .rst                        (rst                        ),
  .clk                        (clk                        ),
  .o_if_fetched_req           (fetched_req                ),
  .i_if_fetched_ack           (fetched_ack                ),
  .o_if_axi_valid             (if_valid                   ),
  .i_if_axi_ready             (if_ready                   ),
  .i_if_axi_data_read         (if_data_read               ),
  .o_if_axi_addr              (if_addr                    ),
  .o_if_axi_size              (if_size                    ),
  .i_if_axi_resp              (if_resp                    ),
  .i_if_pc_jmp                (o_ex_pc_jmp                ),
  .i_if_pc_jmpaddr            (o_ex_pc_jmpaddr            ),
  .o_if_pc_old                (o_if_pc_old                ),
  .o_if_pc                    (o_if_pc                    ),
  .o_if_pc_pred               (o_if_pc_pred               ),
  .o_if_inst                  (o_if_inst                  )
);

id_stage Id_stage(
  .rst                        (rst                        ),
  .clk                        (clk                        ),
  .i_id_fetched_req           (fetched_req                ),
  .o_id_fetched_ack           (fetched_ack                ),
  .o_id_decoded_req           (decoded_req                ),
  .i_id_decoded_ack           (decoded_ack                ),
  .i_id_pc                    (o_if_pc                    ),
  .i_id_inst                  (o_if_inst                  ),
  .i_id_rs1_data              (o_reg_id_rs1_data          ),
  .i_id_rs2_data              (o_reg_id_rs2_data          ),
  .i_id_pc_old                (o_if_pc_old                ),
  .o_id_pc                    (o_id_pc                    ),
  .o_id_inst                  (o_id_inst                  ),
  .o_id_rs1_ren               (o_id_rs1_ren               ),
  .o_id_rs1                   (o_id_rs1                   ),
  .o_id_rs2_ren               (o_id_rs2_ren               ),
  .o_id_rs2                   (o_id_rs2                   ),
  .o_id_rd                    (o_id_rd                    ),
  .o_id_memaddr               (o_id_memaddr               ),
  .o_id_memren                (o_id_memren                ),
  .o_id_memwen                (o_id_memwen                ),
  .o_id_memwdata              (o_id_memwdata              ),
  .o_id_itype                 (o_id_itype                 ),
  .o_id_opcode                (o_id_opcode                ),
  .o_id_funct3                (o_id_funct3                ),
  .o_id_funct7                (o_id_funct7                ),
  .o_id_op1                   (o_id_op1                   ),
  .o_id_op2                   (o_id_op2                   ),
  .o_id_t1                    (o_id_t1                    ),
  .o_id_csr_addr              (o_id_csraddr               ),
  .o_id_csr_op                (o_id_csrop                 ),
  .o_id_csr_wdata             (o_id_csrwdata              ),
  .i_id_csr_rdata             (o_csr_rdata                ),
  .i_id_pc_pred               (o_if_pc_pred               ),
  .o_id_pc_pred               (id_pc_pred_o               ),
  .o_id_skip_difftest         (o_id_skip_difftest         )
);

exe_stage Exe_stage(
  .rst                        (rst                        ),
  .clk                        (clk                        ),
  .i_ex_decoded_req           (decoded_req                ),
  .o_ex_decoded_ack           (decoded_ack                ),
  .o_ex_executed_req          (executed_req               ),
  .i_ex_pc                    (o_id_pc                    ),
  .i_ex_inst                  (o_id_inst                  ),
  .i_ex_executed_ack          (executed_ack               ),
  .i_ex_opcode                (o_id_opcode                ),
  .i_ex_funct3                (o_id_funct3                ),
  .i_ex_funct7                (o_id_funct7                ),
  .i_ex_op1                   (o_id_op1                   ),
  .i_ex_op2                   (o_id_op2                   ),
  .i_ex_t1                    (o_id_t1                    ),
  .i_ex_pc_pred               (id_pc_pred_o               ),
  .i_ex_memren                (o_id_memren                ),
  .i_ex_memwen                (o_id_memwen                ),
  .o_ex_pc                    (o_ex_pc                    ),
  .o_ex_inst                  (o_ex_inst                  ),
  .o_ex_pc_jmp                (o_ex_pc_jmp                ),
  .o_ex_pc_jmpaddr            (o_ex_pc_jmpaddr            ),
  .o_ex_rd_wen                (o_ex_rd_wen                ),
  .o_ex_rd_wdata              (o_ex_rd_wdata              ),
  .o_ex_memren                (o_ex_memren                ),
  .o_ex_memwen                (o_ex_memwen                )
);

mem_stage Mem_stage(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_mem_executed_req         (executed_req               ),
  .o_mem_executed_ack         (executed_ack               ),
  .o_mem_memoryed_req         (memoryed_req               ),
  .i_mem_pc                   (o_ex_pc                    ),
  .i_mem_inst                 (o_ex_inst                  ),
  .i_mem_memoryed_ack         (memoryed_ack               ),
  .i_mem_addr                 (o_ex_memaddr               ),
  .i_mem_ren                  (o_ex_memren                ),
  .i_mem_wen                  (o_ex_memwen                ),
  .i_mem_wdata                (o_ex_memwdata              ),
  .i_mem_funct3               (o_ex_funct3                ),
  .o_mem_pc                   (o_mem_pc                   ),
  .o_mem_inst                 (o_mem_inst                 ),
  .o_mem_rdata                (o_mem_rdata                )
);


wire  [4 : 0]                 o_wb_rd;
reg                           o_wb_rd_wen;
wire  [`BUS_64]               o_wb_rd_wdata;

wb_stage Wb_stage(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_wb_memoryed_req          (memoryed_req               ),
  .o_wb_memoryed_ack          (memoryed_ack               ),
  .o_wb_writebacked_req       (writebacked_req            ),
  .i_wb_writebacked_ack       (writebacked_ack            ),
  .i_wb_pc                    (o_mem_pc                   ),
  .i_wb_inst                  (o_mem_inst                 ),
  .i_wb_rd                    (o_ex_rd_wen                ),
  .i_wb_rd_wen                (o_ex_rd_wen                ),
  .i_wb_rd_wdata              (o_ex_rd_wdata              ),
  .o_wb_pc                    (o_wb_pc                    ),
  .o_wb_inst                  (o_wb_inst                  ),
  .o_wb_rd                    (o_wb_rd                    ),
  .o_wb_rd_wen                (o_wb_rd_wen                ),
  .o_wb_rd_wdata              (o_wb_rd_wdata              )
  // .ex_wen_i                   (o_ex_rd_wen                ),
  // .ex_wdata_i                 (o_ex_rd_wdata              ),
  // .mem_wen_i                  (ex_memwen                  ),
  // .mem_wdata_i                (mem_rdata                  ),
  // .csr_wen_i                  (o_csr_rd_wen               ),
  // .csr_wdata_i                (o_csr_rd_wdata             ),
  // .wen_o                      (rd_wen                     ),
  // .wdata_o                    (rd_wdata                   )
);

cmt_stage Cmt_stage(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_cmt_writebacked_req      (writebacked_req            ),
  .o_cmt_writebacked_ack      (writebacked_ack            ),
  .i_cmt_rd                   (o_wb_rd                    ),
  .i_cmt_rd_wen               (o_wb_rd_wen                ),
  .i_cmt_rd_wdata             (o_wb_rd_wdata              ),
  .i_cmt_pc                   (o_wb_pc                    ),
  .i_cmt_inst                 (o_wb_inst                  ),
  .i_cmt_skip_difftest        (o_wb_skip_difftest         ),
  .i_cmt_regs                 (o_reg_regs                 ),
  .i_cmt_csrs                 (o_csr_csrs                 )
);

regfile Regfile(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_rs1                      (o_id_rs1                   ),
  .i_rs1_ren                  (o_id_rs1_ren               ),
  .i_rs2                      (o_id_rs2                   ),
  .i_rs2_ren                  (o_id_rs2_ren               ),
  .i_rd                       (o_wb_rd                    ),
  .i_rd_wen                   (o_wb_rd_wen                ),
  .i_rd_data                  (o_wb_rd_wdata              ),
  .o_rs1_data                 (o_reg_id_rs1_data          ),
  .o_rs2_data                 (o_reg_id_rs2_data          ),
  .o_regs                     (o_reg_regs                 )
);

csrfile Csrfile(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_csr_addr                 (o_id_csraddr               ),
  .i_csr_op                   (o_id_csrop                 ),
  .i_csr_wdata                (o_id_csrwdata              ),
  .o_csr_rdata                (o_csr_rdata                ),
  .o_csrs                     (o_csr_csrs                 )
);




endmodule