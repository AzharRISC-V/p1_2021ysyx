// ZhengpuShi

`include "defines.v"
`include "single_pulse.v"

module State(
  input   wire                  clk,
  input   wire                  rst,
  output  wire                  cpu_started,

  input   wire  [`BUS_64]       pc,

  input   wire                  ifreq,          // 请求if
  input   wire                  memread,        // 需要 memory read
  input   wire                  memwrite,       // 需要 memory write
  input   wire                  memread_ok,     // memory read 完成，则进入wb
  input   wire                  memwrite_ok,    // memory write 完成，则进入cmt
  input   wire                  wb,             // 需要 wb
  input   wire                  wb_ok,          // wb完成，则进入cmt
  input   wire                  cmt_ok,         // commit完成，则全部完成

  output  wire  [`BUS_STATE]    state,          // 状态
  output  wire                  state_stable
  // ,    // 状态机是否稳定（前后两次值一致）
  // output  reg   [`BUS_STAGE]    stage           // 指令阶段
);

// wire wb_inuse;
// single_pulse u1_wb(
//   .clk(clk),
//   .rst(rst),
//   .signal_in(wb),
//   .pluse_out(wb_inuse)
// );

// cpu是否已经启动：复位信号完成 & 已取到第一条指令
assign cpu_started = (!rst) & (pc != `PC_START_RESET);

assign state_stable = (state_cur == state_next);

// 指令阶段
// always @(posedge clk) begin
//   if (rst || (pc == `PC_START_RESET))
//     stage = `STAGE_EMPTY;
// end

// -----------<信号定义> -------------
reg [`BUS_STATE] state_cur;
reg [`BUS_STATE] state_next;

// -----------<状态机第1段：状态转移> -------------
always @(posedge clk) begin
  if (rst)
    state_cur <= `STATE_EMPTY;
  else
      state_cur <= state_next;
end

// -----------<状态机第2段：状态转换> -------------
always @(*) begin
  if (!cpu_started) begin
    state_next = `STATE_EMPTY;
  end
  else begin
    case (state_cur)
      `STATE_EMPTY: begin
        if (ifreq)
          state_next = `STATE_IDLE;
        else
          state_next = state_cur;
      end
      `STATE_IDLE: begin
        $display(" idle->, memread=", memread, " memwrite=", memwrite, " wb=", wb);
        if (memread)
          state_next = `STATE_MEMREAD;
        else if (memwrite)
          state_next = `STATE_MEMWRITE;
        else if (wb)
          state_next = `STATE_WB;
        else
          state_next = state_cur;
      end
      `STATE_MEMREAD: begin
        if (memread_ok)
          state_next = `STATE_WB;
        else
          state_next = state_cur;
      end
      `STATE_MEMWRITE: begin
        if (memwrite_ok)
          state_next = `STATE_CMT;
        else
          state_next = state_cur;
      end
      `STATE_WB: begin
        if (wb_ok)
          state_next = `STATE_CMT;
        else
          state_next = state_cur;
      end
      `STATE_CMT: begin
        if (cmt_ok)
          state_next = `STATE_EMPTY;
        else
          state_next = state_cur;
      end
      default:
        state_next = state_cur;
    endcase
  end
end

// -----------<状态机第3段：输出逻辑> -------------
assign state = rst ? `STATE_EMPTY : state_cur;


always @(*)
  $display("STATE=", state, 
    " memread=", memread, 
    " memread_ok=", memread_ok, 
    " memwrite=", memwrite,
    " memwrite_ok=", memwrite_ok,
    " wb=", wb,
    " wb_ok=", wb_ok
    );
endmodule