// ZhengpuShi

/*
  State machine of current instruction

  IDLE      + memread       => MEMREAD
  IDLE      + memwrite      => MEMWRITE
  IDLE      + wb            => WB
  MEMREAD   + memread_ok    => WB
  MEMWRITE  + memwrite_ok   => IDLE
  WB        + wb_ok         => IDLE
  
*/

`include "defines.v"

module State(
  input   wire                  clk,
  input   wire                  rst,

  input   wire                  memread,        // 需要 memory read
  input   wire                  memwrite,       // 需要 memory write
  input   wire                  memread_ok,     // memory read 完成，需要 wb
  input   wire                  memwrite_ok,    // memory write 完成，则全部完成
  input   wire                  wb,             // 需要 wb
  input   wire                  wb_ok,          // wb完成，则全部完成

  output  wire  [`BUS_STATE]    state           // 指令状态
);

// -----------<信号定义> -------------
reg [`BUS_STATE] state_cur;
reg [`BUS_STATE] state_next;

// -----------<状态机第1段：状态转移> -------------
always @(posedge clk or negedge rst) begin
  if (rst)
    state_cur <= `STATE_IDLE;
  else
    state_cur <= state_next;
end

// -----------<状态机第2段：状态转换> -------------
always @(*) begin
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
        state_next = `STATE_IDLE;
      else
        state_next = state_cur;
    end
    `STATE_WB: begin
      if (wb_ok)
        state_next = `STATE_IDLE;
      else
        state_next = state_cur;
    end
    default:
      state_next = state_cur;
  endcase
end

// -----------<状态机第3段：输出逻辑> -------------
assign state = rst ? `STATE_IDLE : state_cur;

endmodule