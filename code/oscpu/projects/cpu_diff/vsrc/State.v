// ZhengpuShi

/*
  State machine of current instruction

  IDLE      + memread       => MEMREAD
  IDLE      + memwrite      => MEMWRITE
  IDLE      + wb            => WB
  MEMREAD   + memread_ok    => WB
  MEMWRITE  + memwrite_ok   => CMT
  WB        + wb_ok         => CMT
  CMT       @ clk_neg       => IDLE
  
*/

`include "defines.v"

module State(
  input   wire                  clk,
  input   wire                  rst,
  input   wire  [`BUS_64]       pc,

  input   wire                  memread,        // 需要 memory read
  input   wire                  memwrite,       // 需要 memory write
  input   wire                  memread_ok,     // memory read 完成，则进入wb
  input   wire                  memwrite_ok,    // memory write 完成，则进入cmt
  input   wire                  wb,             // 需要 wb
  input   wire                  wb_ok,          // wb完成，则进入cmt
  input   wire                  cmt_ok,         // commit完成，则全部完成

  output  wire  [`BUS_STATE]    state           // 指令状态
);


// cpu是否已经启动：复位信号完成 & 已取到第一条指令
wire cpu_started = (!rst) & (pc != `PC_START_RESET);

// -----------<信号定义> -------------
reg [`BUS_STATE] state_cur;
reg [`BUS_STATE] state_next;

// -----------<状态机第1段：状态转移> -------------
always @(posedge clk) begin
  if (rst)
    state_cur <= `STATE_IDLE;
  else
    state_cur <= state_next;
end

// -----------<状态机第2段：状态转换> -------------
always @(negedge clk) begin
  if (!cpu_started) begin
    state_next = `STATE_IDLE;
  end
  else begin
    case (state_cur)
      `STATE_IDLE: begin
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
          state_next = `STATE_IDLE;
        else
          state_next = state_cur;
      end
      default:
        state_next = state_cur;
    endcase
  end
end

// -----------<状态机第3段：输出逻辑> -------------
assign state = rst ? `STATE_IDLE : state_cur;


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