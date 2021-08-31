
//--xuezhen--

`include "defines.v"

module SimTop(
    input               clock,
    input               reset,

    input   [`BUS_64]   io_logCtrl_log_begin,
    input   [`BUS_64]   io_logCtrl_log_end,
    input   [`BUS_64]   io_logCtrl_log_level,
    input               io_perfInfo_clean,
    input               io_perfInfo_dump,

    output              io_uart_out_valid,
    output  [7:0]       io_uart_out_ch,
    output              io_uart_in_valid,
    input   [7:0]       io_uart_in_ch
);

// A counter for controlling IF actions
reg                     instcycle_cnt_clear;
wire  [`BUS_8]          instcycle_cnt_val;

counter InstCycleCunter (
  .clk                  (clock                  ),
  .rst                  (reset                  ),
  .clear                (instcycle_cnt_clear    ),
  .min                  (3                      ),
  .max                  (4                      ),
  .val                  (instcycle_cnt_val      )
);

// Global counter
reg [`BUS_64]           clk_cnt;
always @(posedge clock) begin
  clk_cnt += 1;
end

// Special Instruction: putch a0
always @(posedge clock) begin
  if ((inst == 7) && (instcycle_cnt_val == 4)) begin
    $write("%c", regs[10][7:0]);
  end
end

// State
reg                     sig_memread;
wire                    sig_memwrite;
wire                    sig_memread_ok;
wire                    sig_memwrite_ok;
reg                     sig_wb;
wire                    sig_wb_ok;
  
// if_stage
wire                    pc_jmp;
wire [`BUS_64]          pc_jmpaddr;
wire [`BUS_64]          pc_cur;
wire [`BUS_64]          pc;
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
wire                    mem_ren;
reg  [`BUS_64]          mem_rdata;
wire                    mem_wen;
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


if_stage If_stage(
  .clk_cnt            (clk_cnt          ),
  .clk                (clock              ),
  .rst                (reset              ),
  .instcycle_cnt_val  (instcycle_cnt_val  ),
  .pc_jmp             (pc_jmp_o         ),
  .pc_jmpaddr         (pc_jmpaddr_o     ),
  .pc_cur             (pc_cur           ),
  .pc                 (pc               ),
  .inst               (inst             )
);

id_stage Id_stage(
  .clk                (clock            ),
  .rst                (reset            ),
  .instcycle_cnt_val  (instcycle_cnt_val  ),
  .inst               (inst             ),
  .sig_memread        (sig_memread      ),     
  .sig_memwrite       (sig_memwrite     ),  
  .rs1_data           (rs1_data         ),
  .rs2_data           (rs2_data         ),
  .pc_cur             (pc_cur           ),
  .pc                 (pc               ),
  .rs1_ren            (rs1_ren          ),
  .rs1                (rs1              ),
  .rs2_ren            (rs2_ren          ),
  .rs2                (rs2              ),
  .rd                 (rd               ),
  .mem_addr           (mem_addr         ),
  .mem_ren            (mem_ren          ),
  .mem_wen            (mem_wen          ),
  .mem_wdata          (mem_wdata        ),
  .itype              (itype            ),
  .opcode             (opcode           ),
  .funct3             (funct3           ),
  .funct7             (funct7           ),
  .op1                (op1              ),
  .op2                (op2              ),
  .t1                 (t1               ),
  .csr_addr           (csr_addr         ),
  .csr_op             (csr_op           ),
  .csr_wdata          (csr_wdata        ),
  .csr_rdata          (csr_rdata        ),
  .skip_difftest      (skip_difftest    )
);

exe_stage Exe_stage(
  .clk                (clock            ),
  .rst                (reset            ),
  .instcycle_cnt_val  (instcycle_cnt_val  ),
  .opcode_i           (opcode           ),
  .funct3_i           (funct3           ),
  .funct7_i           (funct7           ),
  .op1_i              (op1              ),
  .op2_i              (op2              ),
  .t1_i               (t1               ),
  .pc_jmp             (pc_jmp_o         ),
  .pc_jmpaddr         (pc_jmpaddr_o     ),
  .rd_wen             (ex_rd_wen_o      ),
  .rd_data            (ex_rd_wdata_o    )
);

mem_stage Mem_stage(
  .clk_cnt            (clk_cnt          ),
  .clk                (clock            ),
  .rst                (reset            ),
  .instcycle_cnt_val  (instcycle_cnt_val  ),
  .sig_memread_ok     (sig_memread_ok   ),     
  .sig_memwrite_ok    (sig_memwrite_ok  ), 
  .addr               (mem_addr         ),
  .ren                (mem_ren          ),
  .funct3             (funct3           ),
  .rdata              (mem_rdata        ),
  .wen                (mem_wen          ),
  .wdata              (mem_wdata        )
);
    
wb_stage Wb_stage(
  .clk                (clock            ),
  .rst                (reset            ),
  .instcycle_cnt_val  (instcycle_cnt_val  ),
  .ex_wen_i           (ex_rd_wen_o      ),
  .ex_wdata_i         (ex_rd_wdata_o    ),
  .mem_wen_i          (sig_memread_ok   ),
  .mem_wdata_i        (mem_rdata        ),
  .csr_wen_i          (csr_rd_wen_o     ),
  .csr_wdata_i        (csr_rd_wdata_o   ),
  .wen_o              (rd_wen           ),
  .wdata_o            (rd_wdata         )
);

regfile Regfile(
  .clk                (clock            ),
  .rst                (reset            ),
  .rs1                (rs1              ),
  .rs1_ren            (rs1_ren          ),
  .rs1_data           (rs1_data         ),
  .rs2                (rs2              ),
  .rs2_ren            (rs2_ren          ),
  .rs2_data           (rs2_data         ),
  .rd                 (rd               ),
  .rd_data            (rd_wdata         ),
  .rd_wen             (rd_wen           ),
  .sig_wb_ok          (sig_wb_ok        ),
  .regs_o             (regs             )
);

csrfile Csrfile(
  .clk                (clock            ),
  .rst                (reset            ),
  .csr_addr           (csr_addr         ),
  .csr_op             (csr_op           ),
  .csr_wdata          (csr_wdata        ),
  .csr_rdata          (csr_rdata        ),
  .csrs_o             (csrs             )
);

// Difftest
reg                   cmt_wen;        // commit write enable
reg   [7:0]           cmt_wdest;
reg   [`REG_BUS]      cmt_wdata;
reg   [`REG_BUS]      cmt_pc;
reg   [`BUS_32]       cmt_inst;
reg                   cmt_valid;      // control commit valid
reg                   cmt_skip;       // control commit skip
reg                   trap;
reg   [7:0]           trap_code;
reg   [`BUS_64]       cycleCnt;
reg   [`BUS_64]       instrCnt;
reg   [`BUS_64]       regs_diff [0 : 31];
reg   [`BUS_64]       csrs_diff [0 : 7];


wire inst_valid = ((pc != `PC_START) | (inst != 0)) & (instcycle_cnt_val == 4);

always @(posedge clock) begin
  if (reset) begin
    {cmt_wen, cmt_wdest, cmt_wdata, cmt_pc, cmt_inst, cmt_valid, cmt_skip, trap, trap_code, cycleCnt, instrCnt} <= 0;
  end
  else if (~trap) begin
    cmt_wen <= rd_wen;
    cmt_wdest <= {3'd0, rd};
    cmt_wdata <= rd_wdata;
    cmt_pc <= pc;
    cmt_inst <= inst;
    cmt_skip <= skip_difftest;

    cmt_valid <= inst_valid;

		regs_diff <= regs;
		csrs_diff <= csrs;

    trap <= inst[6:0] == 7'h6b;
    trap_code <= regs[10][7:0];
    cycleCnt <= cycleCnt + 1;
    instrCnt <= instrCnt + inst_valid;
  end
end

DifftestInstrCommit DifftestInstrCommit(
  .clock              (clock),
  .coreid             (0),
  .index              (0),
  .valid              (cmt_valid),
  .pc                 (cmt_pc),
  .instr              (cmt_inst),
  .skip               (cmt_skip),
  .isRVC              (0),
  .scFailed           (0),
  .wen                (cmt_wen),
  .wdest              (cmt_wdest),
  .wdata              (cmt_wdata)
);

DifftestArchIntRegState DifftestArchIntRegState (
  .clock              (clock),
  .coreid             (0),
  .gpr_0              (regs_diff[0]),
  .gpr_1              (regs_diff[1]),
  .gpr_2              (regs_diff[2]),
  .gpr_3              (regs_diff[3]),
  .gpr_4              (regs_diff[4]),
  .gpr_5              (regs_diff[5]),
  .gpr_6              (regs_diff[6]),
  .gpr_7              (regs_diff[7]),
  .gpr_8              (regs_diff[8]),
  .gpr_9              (regs_diff[9]),
  .gpr_10             (regs_diff[10]),
  .gpr_11             (regs_diff[11]),
  .gpr_12             (regs_diff[12]),
  .gpr_13             (regs_diff[13]),
  .gpr_14             (regs_diff[14]),
  .gpr_15             (regs_diff[15]),
  .gpr_16             (regs_diff[16]),
  .gpr_17             (regs_diff[17]),
  .gpr_18             (regs_diff[18]),
  .gpr_19             (regs_diff[19]),
  .gpr_20             (regs_diff[20]),
  .gpr_21             (regs_diff[21]),
  .gpr_22             (regs_diff[22]),
  .gpr_23             (regs_diff[23]),
  .gpr_24             (regs_diff[24]),
  .gpr_25             (regs_diff[25]),
  .gpr_26             (regs_diff[26]),
  .gpr_27             (regs_diff[27]),
  .gpr_28             (regs_diff[28]),
  .gpr_29             (regs_diff[29]),
  .gpr_30             (regs_diff[30]),
  .gpr_31             (regs_diff[31])
);

DifftestTrapEvent DifftestTrapEvent(
  .clock              (clock),
  .coreid             (0),
  .valid              (trap),
  .code               (trap_code),
  .pc                 (cmt_pc),
  .cycleCnt           (cycleCnt),
  .instrCnt           (instrCnt)
);

DifftestCSRState DifftestCSRState(
  .clock              (clock),
  .coreid             (0),
  .priviledgeMode     (`RISCV_PRIV_MODE_M),
  .mstatus            (csrs[`CSR_IDX_MSTATUS]),
  .sstatus            (0),
  .mepc               (0),
  .sepc               (0),
  .mtval              (0),
  .stval              (0),
  .mtvec              (0),
  .stvec              (0),
  .mcause             (0),
  .scause             (0),
  .satp               (0),
  .mip                (0),
  .mie                (0),
  .mscratch           (0),
  .sscratch           (0),
  .mideleg            (0),
  .medeleg            (0)
);

DifftestArchFpRegState DifftestArchFpRegState(
  .clock              (clock),
  .coreid             (0),
  .fpr_0              (0),
  .fpr_1              (0),
  .fpr_2              (0),
  .fpr_3              (0),
  .fpr_4              (0),
  .fpr_5              (0),
  .fpr_6              (0),
  .fpr_7              (0),
  .fpr_8              (0),
  .fpr_9              (0),
  .fpr_10             (0),
  .fpr_11             (0),
  .fpr_12             (0),
  .fpr_13             (0),
  .fpr_14             (0),
  .fpr_15             (0),
  .fpr_16             (0),
  .fpr_17             (0),
  .fpr_18             (0),
  .fpr_19             (0),
  .fpr_20             (0),
  .fpr_21             (0),
  .fpr_22             (0),
  .fpr_23             (0),
  .fpr_24             (0),
  .fpr_25             (0),
  .fpr_26             (0),
  .fpr_27             (0),
  .fpr_28             (0),
  .fpr_29             (0),
  .fpr_30             (0),
  .fpr_31             (0)
);

endmodule