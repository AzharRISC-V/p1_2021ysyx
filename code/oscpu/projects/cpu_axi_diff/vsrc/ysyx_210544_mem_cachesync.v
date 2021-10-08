
// ZhengpuShi

// Memory State for Cache Sync

`include "defines.v"

module ysyx_210544_mem_cachesync(
  input   wire                clk,
  input   wire                rst,

  input   wire                start,
  input   wire                ack,
  output  reg                 req,

  ///////////////////////////////////////////////
  // Cache Sync interface
  output  reg                 o_cachesync_req,
  input   wire                i_cachesync_ack
);

wire hs_cachesync;



assign hs_cachesync  = o_cachesync_req & i_cachesync_ack;

always @(posedge clk) begin
  if (rst) begin
    req <= 0;
    o_cachesync_req <= 0;
  end
  else begin
    if (start) begin
      o_cachesync_req <= 1;
    end
    else begin
      if (hs_cachesync) begin
        o_cachesync_req   <= 0;
        req <= 1;
      end
      // 清除req信号
      else if (ack) begin
        req <= 0;
      end
    end
  end
end

endmodule
