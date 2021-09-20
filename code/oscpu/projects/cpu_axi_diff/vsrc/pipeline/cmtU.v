
// ZhengpuShi

// Commit Unit (for difftest)

`include "../defines.v"

module cmtU(
  input   wire                clk,
  input   wire                rst,
  input   wire [`BUS_RIDX]    i_rd,
  input   wire                i_rd_wen,
  input   wire [`BUS_64]      i_rd_wdata,
  input   wire [`BUS_64]      i_pc,
  input   wire [`BUS_32]      i_inst,
  input   wire [`BUS_64]      i_regs[0 : 31],
  input   wire [`BUS_64]      i_csrs[0 :  7],
  input   wire                i_cmtvalid,
  input   wire                i_skipcmt
);


// Difftest
reg                           cmt_wen;
reg   [7:0]                   cmt_wdest;
reg   [`BUS_64]               cmt_wdata;
reg   [`BUS_64]               cmt_pc;
reg   [`BUS_32]               cmt_inst;
reg                           cmt_valid;
reg                           cmt_skip;       // control commit skip
reg                           trap;
reg   [7:0]                   trap_code;
reg   [`BUS_64]               cycleCnt;
reg   [`BUS_64]               instrCnt;
reg   [`BUS_64]               regs_diff [0 : 31];
reg   [`BUS_64]               csrs_diff [0 : 7];

reg   [`BUS_64] instrCnt_inc = i_cmtvalid ? 1 : 0;

always @(negedge clk) begin
  if (rst) begin
    {cmt_wen, cmt_wdest, cmt_wdata, cmt_pc, cmt_inst, cmt_valid, cmt_skip, trap, trap_code, cycleCnt, instrCnt} <= 0;
  end
  else if (~trap) begin
    cmt_wen       <= i_rd_wen;
    cmt_wdest     <= {3'd0, i_rd};
    cmt_wdata     <= i_rd_wdata;
    cmt_pc        <= i_pc;
    cmt_inst      <= i_inst;
    cmt_skip      <= i_skipcmt;
    cmt_valid     <= i_cmtvalid;
    regs_diff     <= i_regs;
		csrs_diff     <= i_csrs;
    trap          <= i_inst[6:0] == 7'h6b;
    trap_code     <= i_regs[10][7:0];
    cycleCnt      <= cycleCnt + 1;
    instrCnt      <= instrCnt + instrCnt_inc;
  end
end

DifftestInstrCommit DifftestInstrCommit(
  .clock              (clk),
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
  .clock              (clk),
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
  .clock              (clk),
  .coreid             (0),
  .valid              (trap),
  .code               (trap_code),
  .pc                 (cmt_pc),
  .cycleCnt           (cycleCnt),
  .instrCnt           (instrCnt)
);

DifftestCSRState DifftestCSRState(
  .clock              (clk),
  .coreid             (0),
  .priviledgeMode     (`RISCV_PRIV_MODE_M),
  .mstatus            (i_csrs[`CSR_IDX_MSTATUS]),
  .sstatus            (0),
  .mepc               (i_csrs[`CSR_IDX_MEPC]),
  .sepc               (0),
  .mtval              (0),
  .stval              (0),
  .mtvec              (i_csrs[`CSR_IDX_MTVEC]),
  .stvec              (0),
  .mcause             (i_csrs[`CSR_IDX_MCAUSE]),
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
  .clock              (clk),
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