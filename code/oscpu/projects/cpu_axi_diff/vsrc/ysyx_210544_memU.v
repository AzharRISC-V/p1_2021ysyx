
// ZhengpuShi

// Memory Unit, 组合逻辑电路

`include "defines.v"

module ysyx_210544_memU(
  input   wire                clk,
  input   wire                rst,

  input   wire                start,
  input   wire                ack,
  output  reg                 req,

  input   wire  [`BUS_64]     i_addr,
  input   wire  [2:0]         i_bytes,
  input   wire                i_ren,
  input   wire                i_wen,
  input   wire  [`BUS_64]     i_wdata,
  output  wire  [`BUS_64]     o_rdata,

  ///////////////////////////////////////////////
  // DCache interface
  output  wire                o_dcache_req,
  output  wire  [63:0]        o_dcache_addr,
  output  wire                o_dcache_op,
  output  wire  [2 :0]        o_dcache_bytes,
  output  wire  [63:0]        o_dcache_wdata,
  input   wire                i_dcache_ack,
  input   wire  [63:0]        i_dcache_rdata
);

wire                          hs_dcache;
reg                           wait_finish;  // 是否等待访存完毕？


assign hs_dcache  = o_dcache_req & i_dcache_ack;

always @(posedge clk) begin
  if (rst) begin
    wait_finish    <= 0;
    req <= 0;
  end
  else begin
    if (start) begin
      if (i_ren) begin
        o_dcache_req      <= 1;
        o_dcache_op       <= `REQ_READ;
        o_dcache_addr     <= i_addr;
        o_dcache_bytes    <= i_bytes;
        wait_finish       <= 1;
      end
      else if (i_wen) begin
        o_dcache_req      <= 1;
        o_dcache_op       <= `REQ_WRITE;
        o_dcache_addr     <= i_addr;
        o_dcache_bytes    <= i_bytes;
        o_dcache_wdata    <= i_wdata;
        wait_finish       <= 1;
      end
    end
    else begin
      // 等待访存完毕
      if (wait_finish) begin
        if (hs_dcache) begin
          wait_finish       <= 0;
          o_dcache_req      <= 0;
          req               <= 1;
          o_rdata           <= i_dcache_rdata;
        end
      end
      // 清除req信号
      else if (ack) begin
        req    <= 0;
      end
    end
  end
end

// assign o_rdata = i_dcache_rdata;

endmodule
