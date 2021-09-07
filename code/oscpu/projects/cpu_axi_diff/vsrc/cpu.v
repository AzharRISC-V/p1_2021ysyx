
//--xuezhen--

`include "defines.v"

module cpu(
    input                               clk,
    input                               rst,
    
    output                              if_valid,
    input                               if_ready,
    input  [63:0]                       if_data_read,
    output [63:0]                       if_addr,
    output [1:0]                        if_size,
    input  [1:0]                        if_resp
);

// Global counter
reg [`BUS_64]           clk_cnt;
always @(posedge clk) begin
  clk_cnt += 1;
end

// Special Instruction: putch a0
wire            putch_wen     = inst == 32'h7b;
wire [7 : 0]    putch_wdata   = (!putch_wen) ? 0 : (regs[10][7:0]); 
// putch Putch(
//   .clk                (clock            ),
//   .rst                (reset            ),
//   .wen                (putch_wen        ),
//   .wdata              (putch_wdata      ) 
// );
// always @(posedge clock) begin
//   if (inst == 7) begin
//     $write("%c", regs[10][7:0]);
//   end
// end
// assign io_uart_out_valid = putch_wen;
// assign io_uart_out_ch = putch_wdata;
  
// if_stage
wire                    pc_jmp;
wire [`BUS_64]          pc_jmpaddr;
wire [`BUS_64]          pc_old;
wire [`BUS_64]          pc;
wire [`BUS_64]          if_pc_pred_o;
wire [`BUS_32]          inst;
wire                    inst_start;

// id_stage -> regfile
wire                    rs1_ren;
wire [4 : 0]            rs1;
wire                    rs2_ren;
wire [4 : 0]            rs2;
wire [4 : 0]            rd;
// id_stage -> exe_stage
wire [2 : 0]            itype;    // instruction type : R,I,S,B,U,J
wire [4 : 0]            opcode;
wire [2 : 0]            funct3;
wire [6 : 0]            funct7;
wire [`BUS_64]          op1;
wire [`BUS_64]          op2;
wire [`BUS_64]          t1;   // temp1
wire                    skip_difftest;

// regfile -> id_stage
wire [`BUS_64]          rs1_data;
wire [`BUS_64]          rs2_data;
// regfile -> difftest
wire [`BUS_64]          regs[0 : 31];
wire [`BUS_64]          csrs[0 :  7];

// exe_stage
// exe_stage -> other stage
wire [4 : 0]            opcode_o;
wire                    pc_jmp_o;
wire [`BUS_64]          pc_jmpaddr_o;
// exe_stage -> wb_stage
wire                    ex_rd_wen_o;
wire [`BUS_64]          ex_rd_wdata_o;

// mem_stage
wire [`BUS_64]          mem_addr;
wire                    id_memren;
wire                    ex_memren;
reg  [`BUS_64]          mem_rdata;
wire                    id_memwen;
wire                    ex_memwen;
wire [`BUS_64]          mem_wdata;

// wb_stage
wire                    wb_rd_wen_i;
wire [`BUS_64]          wb_rd_wdata_i;
wire                    wb_rd_wen_o;
wire [`BUS_64]          wb_rd_wdata_o;

// rd_write -> regfile
wire                    rd_wen;
wire [`BUS_64]          rd_wdata;

// csrfile
wire [11 : 0]           csr_addr;
wire [1 : 0]            csr_op;
wire [11 : 0]           csr_waddr;
wire [`BUS_64]          csr_wdata;
wire [`BUS_64]          csr_rdata;

// exe_stage -> wb_stage
wire                    csr_rd_wen_o = csr_op != 2'b00;
wire [`BUS_64]          csr_rd_wdata_o = (csr_op == 2'b00) ? 0 : csr_rdata;

wire  fetched_req;
wire  fetched_ack;
wire  decoded_req;
wire  decoded_ack;
wire  executed_req;
wire  executed_ack;
wire  memoryed_req;
wire  memoryed_ack;
wire  writebacked_req;
wire  writebacked_ack;

wire [`BUS_64]          id_pc_pred_o;

wire                    pipe_flush_req;
wire                    pipe_flush_ack;
wire  [`BUS_64]         pipe_flush_pc;

wire                    minidec_pc_jmp;
wire  [`BUS_64]         minidec_pc_jmpaddr;

if_stage If_stage(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .pc_jmp                     (pc_jmp                     ),
  .pc_jmpaddr                 (pc_jmpaddr                 ),
  .pc_old                     (pc_old                     ),
  .pc                         (pc                         ),
  .pc_pred_o                  (if_pc_pred_o               ),
  .inst                       (inst                       ),
  .if_valid                   (if_valid                   ),
  .if_ready                   (if_ready                   ),
  .if_data_read               (if_data_read               ),
  .if_addr                    (if_addr                    ),
  .if_size                    (if_size                    ),
  .if_resp                    (if_resp                    ),
  .if_fetched_req             (fetched_req                ),
  .if_fetched_ack             (fetched_ack                )
  // .pipe_flush_req     (pipe_flush_req       ),
  // .pipe_flush_ack     (pipe_flush_ack       ),
  // .pipe_flush_pc      (pipe_flush_pc        )
);

id_stage Id_stage(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .id_fetched_req_i           (fetched_req                ),
  .id_fetched_ack_o           (fetched_ack                ),
  .id_decoded_req_o           (decoded_req                ),
  .id_decoded_ack_i           (decoded_ack                ),
  .id_inst_i                  (inst                       ),
  .id_rs1_data_i              (rs1_data                   ),
  .id_rs2_data_i              (rs2_data                   ),
  .id_pc_old_i                (pc_old                     ),
  .id_pc_i                    (pc                         ),
  .id_rs1_ren_o               (rs1_ren                    ),
  .id_rs1_o                   (rs1                        ),
  .id_rs2_ren_o               (rs2_ren                    ),
  .id_rs2_o                   (rs2                        ),
  .id_rd_o                    (rd                         ),
  .id_mem_addr_o              (mem_addr                   ),
  .id_mem_ren_o               (id_memren                  ),
  .id_mem_wen_o               (id_memwen                  ),
  .id_mem_wdata_o             (mem_wdata                  ),
  .id_itype_o                 (itype                      ),
  .id_opcode_o                (opcode                     ),
  .id_funct3_o                (funct3                     ),
  .id_funct7_o                (funct7                     ),
  .id_op1_o                   (op1                        ),
  .id_op2_o                   (op2                        ),
  .id_t1_o                    (t1                         ),
  .id_csr_addr_o              (csr_addr                   ),
  .id_csr_op_o                (csr_op                     ),
  .id_csr_wdata_o             (csr_wdata                  ),
  .id_csr_rdata_i             (csr_rdata                  ),
  .id_pc_pred_i               (if_pc_pred_o               ),
  .id_pc_pred_o               (id_pc_pred_o               ),
  .id_skip_difftest_o         (skip_difftest              )
);

exe_stage Exe_stage(
  .rst                        (rst                        ),
  .clk                        (clk                        ),
  .ex_decoded_req_i           (decoded_req                ),
  .ex_decoded_ack_o           (decoded_ack                ),
  .ex_executed_req_o          (executed_req               ),
  .ex_executed_ack_i          (executed_ack               ),
  .ex_opcode_i                (opcode                     ),
  .ex_funct3_i                (funct3                     ),
  .ex_funct7_i                (funct7                     ),
  .ex_op1_i                   (op1                        ),
  .ex_op2_i                   (op2                        ),
  .ex_t1_i                    (t1                         ),
  .ex_pc_pred_i               (id_pc_pred_o               ),
  .ex_memren_i                (id_memren                  ),
  .ex_memwen_i                (id_memwen                  ),
  .ex_pc_jmp_o                (pc_jmp_o                   ),
  .ex_pc_jmpaddr_o            (pc_jmpaddr_o               ),
  .ex_rd_wen_o                (ex_rd_wen_o                ),
  .ex_rd_wdata_o              (ex_rd_wdata_o              ),
  .ex_memren_o                (ex_memren                  ),
  .ex_memwen_o                (ex_memwen                  )
  // .o_jump_flush_req   (jump_flush_req       ),
  // .o_jump_flush_pc    (jump_flush_pc        )
);

mem_stage Mem_stage(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .clk_cnt                    (clk_cnt                    ),
  .mem_executed_req_i         (executed_req               ),
  .mem_executed_ack_o         (executed_ack               ),
  .mem_memoryed_req_o         (memoryed_req               ),
  .mem_memoryed_ack_i         (memoryed_ack               ),
  .mem_addr_i                 (mem_addr                   ),
  .mem_ren_i                  (ex_memren                  ),
  .mem_funct3_i               (funct3                     ),
  .mem_wen_i                  (ex_memwen                  ),
  .mem_wdata_i                (mem_wdata                  ),
  .mem_rdata_o                (mem_rdata                  )
);


wire  [4 : 0]         wb_rd_o;
reg                   wb_rd_wen_o;
wire  [`BUS_64]       wb_rd_wdata_o;

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
  .cmt_rd_i                   (rd                         ),
  .cmt_rd_wen_i               (rd_wen                     ),
  .cmt_rd_wdata_i             (rd_wdata                   ),
  .cmt_pc_i                   (pc                         ),
  .cmt_inst_i                 (inst                       ),
  .cmt_skip_difftest_i        (skip_difftest              ),
  .cmt_regs_i                 (regs                       ),
  .cmt_csrs_i                 (csrs                       )
);

wire w_ena = rd_wen & fetched_req;

regfile Regfile(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .rs1                        (rs1                        ),
  .rs1_ren                    (rs1_ren                    ),
  .rs1_data                   (rs1_data                   ),
  .rs2                        (rs2                        ),
  .rs2_ren                    (rs2_ren                    ),
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