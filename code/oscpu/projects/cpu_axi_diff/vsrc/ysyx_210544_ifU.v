
// ZhengpuShi

// Fetch Unit

`include "defines.v"

module ysyx_210544_ifU(
  input   wire                clk,
  input   wire                rst,

  /////////////////////////////////////////////////////////
  // AXI interface for Fetch
  input                       i_bus_ack,
  input         [`BUS_32]     i_bus_rdata,
  output reg                  o_bus_req,
  output reg    [`BUS_64]     o_bus_addr,
  
  /////////////////////////////////////////////////////////
  input                       i_writebacked_req,    // 是否写回阶段完成
  input   wire                i_pc_jmp,
  input   wire  [`BUS_64]     i_pc_jmpaddr,
  output  reg   [`BUS_64]     o_pc,
  output  reg   [`BUS_32]     o_inst,
  output  reg                 o_fetched             // 取到指令的通知
);

wire              handshake_done;
reg               ignore_next_inst;     // 忽略下一条取指
reg [`BUS_64]     saved_pc_jmpaddr;     // 记忆的pc跳转指令
reg               fetch_again;          // 再次取指
reg [`BUS_64]     pc_pred;              // 预测的下一个PC



// o_bus_req
always @(posedge clk) begin
  if (rst) begin
    o_bus_req <= 1;
  end
  else begin
    // 停止信号
    if (handshake_done) begin
      // 若要求再次取指，则这次不要停止
      if (fetch_again) begin
        fetch_again <= 0;
      end
      else begin
        o_bus_req <= 0;
      end
    end
    // 启动信号
    else if (i_writebacked_req) begin
      o_bus_req <= 1;
    end
  end
end

assign handshake_done = o_bus_req & i_bus_ack;

// 跳转指令处理
always @(posedge clk) begin
  if (rst) begin
    ignore_next_inst <= 0;
    saved_pc_jmpaddr <= 0;
    fetch_again <= 0;
  end
  else begin
    if (i_pc_jmp & (i_pc_jmpaddr != pc_pred)) begin
      ignore_next_inst <= 1;
      fetch_again <= 1;
      saved_pc_jmpaddr <= i_pc_jmpaddr;
    end
  end
end

// fetch an instruction
always @( posedge clk ) begin
  if (rst) begin
    o_bus_addr              <= `PC_START;
    o_pc                    <= 0;
    pc_pred                 <= 0;
    o_fetched               <= 0;
  end
  else begin
    if (handshake_done) begin
      if (ignore_next_inst) begin
        ignore_next_inst        <= 0;
        o_bus_addr              <= saved_pc_jmpaddr;
        o_pc                    <= saved_pc_jmpaddr;
        pc_pred                 <= saved_pc_jmpaddr + 4;
      end
      else begin
        o_bus_addr              <= o_bus_addr + 4;
        o_pc                    <= o_bus_addr;
        pc_pred                 <= o_bus_addr + 4;
        o_inst                  <= i_bus_rdata;
        o_fetched               <= 1;
      end
    end
    else begin
      o_inst                  <= 0;
      o_fetched               <= 0;
    end
  end
end


endmodule
