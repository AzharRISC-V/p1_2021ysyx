
// ZhengpuShi

// No Cache Unit
// 没有Cache的AXI总线访问，比如UART。其实Flash也可以用。

`include "defines.v"

module ysyx_210544_cache_nocache (
  input   wire                clk,
  input   wire                rst,
  input   wire  [`BUS_64]     i_cache_nocache_addr,          // 地址
  input   wire  [`BUS_64]     i_cache_nocache_wdata,         // 写入的数据
  input   wire  [2 : 0]       i_cache_nocache_bytes,         // 操作的字大小: 0~7表示1~8字节
	input   wire                i_cache_nocache_op,            // 操作: 0:read, 1:write
	input   wire                i_cache_nocache_req,           // 请求
  output  reg   [`BUS_64]     o_cache_nocache_rdata,         // 读出的数据
	output  reg                 o_cache_nocache_ack,           // 应答

  // AXI interface
  input   wire  [511:0]       i_axi_io_rdata,
  input   wire                i_axi_io_ready,
  output  wire                o_axi_io_valid,
  output  wire                o_axi_io_op,
  output  wire  [511:0]       o_axi_io_wdata,
  output  wire  [63:0]        o_axi_io_addr,
  output  wire  [2:0]         o_axi_io_size,
  output  wire  [7:0]         o_axi_io_blks
);

wire hs_axi_io;
reg [2:0] nocache_size;



assign hs_axi_io = o_axi_io_valid & i_axi_io_ready;

always @(*) begin
  case (i_cache_nocache_bytes)
    3'b000: nocache_size = `SIZE_B;
    3'b001: nocache_size = `SIZE_H;
    3'b011: nocache_size = `SIZE_W;
    3'b111: nocache_size = `SIZE_D;
    default: nocache_size = `SIZE_B;  // 这种情况应该是不支持的。
  endcase
end

always @(posedge clk) begin
  if (rst) begin
    o_axi_io_valid <= 0;
  end
  else begin
    // 发现用户请求
    if (i_cache_nocache_req & !o_cache_nocache_ack) begin
      // 发出请求
      if (!hs_axi_io) begin
        o_axi_io_addr   <= i_cache_nocache_addr;
        o_axi_io_blks   <= 0;
        o_axi_io_op     <= i_cache_nocache_op;
        o_axi_io_size   <= nocache_size;
        o_axi_io_wdata  <= {448'b0, i_cache_nocache_wdata};
        o_axi_io_valid  <= 1;
      end
      // 收到回应
      else begin
        o_axi_io_valid  <= 0;
        o_cache_nocache_rdata <= i_axi_io_rdata[63:0];
        o_cache_nocache_ack   <= 1;
      end
    end
    // 结束应答
    else begin
      o_cache_nocache_ack <= 0;
    end
  end
end

wire _unused_ok = &{1'b0,
  i_axi_io_rdata[511:64],
  1'b0};

endmodule
