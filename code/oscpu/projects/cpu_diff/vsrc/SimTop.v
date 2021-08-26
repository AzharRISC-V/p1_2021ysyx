
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

// State
wire                    sig_memread;
wire                    sig_memwrite;
wire                    sig_memread_ok;
wire                    sig_memwrite_ok;
reg                     sig_wb;
wire                    sig_wb_ok;
wire [`BUS_STATE]       state;

// if_stage
wire [2 : 0]            inst_state;   // 指令状态
wire                    pc_jmp;
wire [`BUS_64]          pc_jmpaddr;
wire [`BUS_64]          pc_cur;
wire [`BUS_64]          pc;
wire [`BUS_32]          inst;

// id_stage
// id_stage -> regfile
wire [2 : 0]            id_inst_state_o;   // 指令状态
wire                    rs1_ren;
wire [4 : 0]            rs1_raddr;
wire                    rs2_ren;
wire [4 : 0]            rs2_raddr;
wire [4 : 0]            rd_waddr;
// id_stage -> exe_stage
wire [2 : 0]            inst_type;
wire [4 : 0]            inst_opcode;
wire [2 : 0]            inst_funct3;
wire [6 : 0]            inst_funct7;
wire [`BUS_64]          op1;
wire [`BUS_64]          op2;
wire [`BUS_64]          t1;   // temp1
// id_stage -> wb_stage
wire                    id_rd_wen;

// regfile -> id_stage
wire [`BUS_64]          rs1_data;
wire [`BUS_64]          rs2_data;
// regfile -> difftest
wire [`BUS_64]          regs[0 : 31];

// exe_stage
// exe_stage -> other stage
wire [4 : 0]            inst_opcode_o;
wire                    pc_jmp_o;
wire [`BUS_64]          pc_jmpaddr_o;
// exe_stage -> wb_stage
wire                    ex_rd_wen_o;
wire [`BUS_64]          ex_rd_wdata_o;
wire [4 : 0]            ex_rd_waddr_i;

// mem_stage
wire                    mem_ren;
wire [`BUS_64]          mem_raddr;
reg  [`BUS_64]          mem_rdata;
wire                    mem_wen;
wire [`BUS_64]          mem_waddr;
wire [`BUS_64]          mem_wdata;
wire [`BUS_64]          mem_wmask;      // 数据掩码，比如0x00F0，则仅写入[7:4]位
wire                    mem_rd_wen_o;   // rd写入使能，需要等 mem_rdata有效时置位

// wb_stage
wire                    wb_rd_wen_i;
wire [`BUS_64]          wb_rd_wdata_i;
wire                    wb_rd_wen_o;
wire [`BUS_64]          wb_rd_wdata_o;

// rd_write -> regfile
wire                    rd_wen;
wire [`BUS_64]          rd_wdata;

// cmt_stage
reg                     sig_cmt_ok;

State u1_state(
  .clk                (clock            ),              
  .rst                (reset            ),
  .pc                 (pc               ),
  .memread            (sig_memread      ),     
  .memwrite           (sig_memwrite     ),    
  .memread_ok         (sig_memread_ok   ),  
  .memwrite_ok        (sig_memwrite_ok  ), 
  .wb                 (sig_wb           ),          
  .wb_ok              (sig_wb_ok        ),
  .cmt_ok             (sig_cmt_ok       ),       
  .state              (state            ) 
);

always @(posedge clock) begin
  if (reset)
    sig_wb = 0;
  else
    sig_wb = ex_rd_wen_o;
end

always @(negedge clock) begin
  sig_wb = 0;
end

//assign sig_wb = ex_rd_wen_o;

if_stage If_stage(
  .clk                (clock            ),
  .rst                (reset            ),
  .state              (state            ),
  .pc_jmp             (pc_jmp_o         ),
  .pc_jmpaddr         (pc_jmpaddr_o     ),
  .pc_cur             (pc_cur           ),
  .pc                 (pc               ),
  .inst               (inst             )
);

id_stage Id_stage(
  .rst                (reset            ),
  .inst               (inst             ),
  .sig_memread        (sig_memread      ),     
  .sig_memwrite       (sig_memwrite     ),  
  .rs1_data           (rs1_data         ),
  .rs2_data           (rs2_data         ),
  .pc_cur             (pc_cur           ),
  .pc                 (pc               ),
  .rs1_ren            (rs1_ren          ),
  .rs1_raddr          (rs1_raddr        ),
  .rs2_ren            (rs2_ren          ),
  .rs2_raddr          (rs2_raddr        ),
  .rd_waddr           (rd_waddr         ),
  .rd_wen             (id_rd_wen        ),
  .mem_ren            (mem_ren          ),
  .mem_raddr          (mem_raddr        ),
  .mem_rdata          (mem_rdata        ),
  .mem_wen            (mem_wen          ),
  .mem_waddr          (mem_waddr        ),
  .mem_wdata          (mem_wdata        ),
  .mem_wmask          (mem_wmask        ),
  .inst_type          (inst_type        ),
  .inst_opcode        (inst_opcode      ),
  .inst_funct3        (inst_funct3      ),
  .inst_funct7        (inst_funct7      ),
  .op1                (op1              ),
  .op2                (op2              ),
  .t1                 (t1               )
);

exe_stage Exe_stage(
  .rst                (reset            ),
  .inst_opcode        (inst_opcode      ),
  .inst_funct3        (inst_funct3      ),
  .inst_funct7        (inst_funct7      ),
  .op1                (op1              ),
  .op2                (op2              ),
  .t1                 (t1               ),
  .pc_jmp             (pc_jmp_o         ),
  .pc_jmpaddr         (pc_jmpaddr_o     ),
  .rd_wen_o           (ex_rd_wen_o      ),
  .rd_wdata_o         (ex_rd_wdata_o    )
);

mem_stage Mem_stage(
  .clk                (clock            ),
  .rst                (reset            ),
  .sig_memread_ok     (sig_memread_ok   ),     
  .sig_memwrite_ok    (sig_memwrite_ok  ), 
  .ren                (mem_ren          ),
  .raddr              (mem_raddr        ),
  .rdata              (mem_rdata        ),
  .wen                (mem_wen          ),
  .waddr              (mem_waddr        ),
  .wdata              (mem_wdata        ),
  .wmask              (mem_wmask        ),
  .rd_wen_i           (id_rd_wen        ),
  .rd_wen_o           (mem_rd_wen_o     )
);
    
wb_stage u1_wb_stage(
  .clk                (clock            ),
  .rst                (reset            ),
  .ex_wen_i           (ex_rd_wen_o      ),
  .ex_wdata_i         (ex_rd_wdata_o    ),
  .mem_wen_i          (mem_rd_wen_o     ),
  .mem_wdata_i        (mem_rdata        ),
  .wen_o              (rd_wen           ),
  .wdata_o            (rd_wdata         )
);

regfile Regfile(
  .clk                (clock            ),
  .rst                (reset            ),
  .w_addr             (rd_waddr         ),
  .w_data             (rd_wdata         ),
  .w_ena              (rd_wen           ),
  .r_addr1            (rs1_raddr        ),
  .r_data1            (rs1_data         ),
  .r_ena1             (rs1_ren          ),
  .r_addr2            (rs2_raddr        ),
  .r_data2            (rs2_data         ),
  .r_ena2             (rs2_ren          ),
  .sig_wb_ok          (sig_wb_ok        ),
  .regs_o             (regs             )
);


// Difftest
reg                   cmt_wen;        // commit write enable
reg   [7:0]           cmt_wdest;
reg   [`REG_BUS]      cmt_wdata;
reg   [`REG_BUS]      cmt_pc;
reg   [`BUS_32]       cmt_inst;
reg                   cmt_valid;      // control commit valid
reg                   trap;
reg   [7:0]           trap_code;
reg   [`BUS_64]       cycleCnt;
reg   [`BUS_64]       instrCnt;
reg   [`BUS_64]       regs_diff [0 : 31];


//wire inst_valid = (pc != `PC_START) | (inst != 0);
wire inst_valid = ((pc != `PC_START) | & (state == `STATE_CMT));

// always @(posedge clock) begin
//   if (reset) begin
//     sig_cmt_ok <= 0;
//   end
//   else
//     sig_cmt_ok <= 0;
// end

// 时钟下降沿，提交指令到 difftest
always @(negedge clock) begin
  if (reset) begin
    {cmt_wen, cmt_wdest, cmt_wdata, cmt_pc, cmt_inst, cmt_valid, trap, trap_code, cycleCnt, instrCnt} <= 0;
  end
  else if (~trap) begin
    cmt_wen <= rd_wen;
    cmt_wdest <= {3'd0, rd_waddr};
    cmt_wdata <= rd_wdata;
    cmt_pc <= pc;
    cmt_inst <= inst;
    cmt_valid <= inst_valid;

    // commit ok signal, generated at negedge of clock, and only valid wehn inst_valid
    sig_cmt_ok <= inst_valid;

		regs_diff <= regs;

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
  .skip               (0),
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
  .mstatus            (0),
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