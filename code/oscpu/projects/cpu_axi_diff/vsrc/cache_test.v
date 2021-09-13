
// ZhengpuShi

// cache Test Interface

`include "defines.v"

module cache_test(
  input   wire                      clk,
  input   wire                      rst,

  // cache_axi 接口
  input   wire  [511:0]             i_cache_rw_axi_rdata,
  input   wire                      i_cache_rw_axi_ready,
  output  wire                      o_cache_rw_axi_valid,
  output  wire                      o_cache_rw_axi_op,
  output  wire  [511:0]             o_cache_rw_axi_wdata,
  output  wire  [63:0]              o_cache_rw_axi_addr,
  output  wire  [1:0]               o_cache_rw_axi_size,
  output  wire  [7:0]               o_cache_rw_axi_blks
);

reg   [63 : 0]                o_cache_addr;        // 存储器地址（字节为单位），64字节对齐，低6位为0。
reg   [63 : 0]                o_cache_wdata;       // 要写入的数据
reg   [2  : 0]                o_cache_bytes;       // 字节数
reg                           o_cache_op;          // 操作类型：0读取，1写入
reg                           o_cache_req;         // 请求
wire  [63 : 0]                i_cache_rdata;       // 已读出的数据
wire                          i_cache_ack;         // 应答

// 测试数据
reg [63:0] reg_rand [0:7];
assign reg_rand[0] = 64'h8c2078a7_07e5484d;
assign reg_rand[1] = 64'h4765af4e_5226ec81;
assign reg_rand[2] = 64'h8046a887_4f66de44;
assign reg_rand[3] = 64'h24334404_8c940a7d;
assign reg_rand[4] = 64'h01dec340_02e85dec;
assign reg_rand[5] = 64'h9bb5df90_9d43c9b6;
assign reg_rand[6] = 64'h2b9b566d_5c040a78;
assign reg_rand[7] = 64'h196df530_aeb93dad;
reg [2:0] reg_rand_idx;
assign o_cache_wdata = reg_rand[reg_rand_idx];

// 指示读出的数据是否与写入的一致
wire equal_flag = o_cache_wdata == i_cache_rdata;

reg [`BUS_64] cnt;
wire hs = o_cache_req & i_cache_ack;
wire hs_read  = hs & (o_cache_op == `REQ_READ);
wire hs_write = hs & (o_cache_op == `REQ_WRITE);

// 演示：延时；写入64字节；延时；读取64字节；。。。
always @(posedge clk) begin
  if (rst) begin
    cnt <= 0;
    o_cache_req     <= 0;
    o_cache_bytes   <= 7;
    o_cache_addr    <= 64'h8000_0000;//3D;// 64'h8000_0400;// `PC_START;
    o_cache_op      <= `REQ_READ;// `REQ_READ;// `REQ_WRITE;
    reg_rand_idx    <= 0;
  end
  else begin
    // 写入完毕
    if (hs_write) begin
      o_cache_req      <= 0;
      cnt              <= 0;
      o_cache_op       <= `REQ_READ;
    end
    // 读取完毕
    else if (hs_read) begin
      o_cache_req      <= 0;
      cnt              <= 0;

      // $displayh("a:", o_cache_addr, ", d:",
      //   " ", i_cache_rdata[ 0+:8],
      //   " ", i_cache_rdata[ 8+:8],
      //   " ", i_cache_rdata[16+:8],
      //   " ", i_cache_rdata[24+:8],
      //   " ", i_cache_rdata[32+:8],
      //   " ", i_cache_rdata[40+:8],
      //   " ", i_cache_rdata[48+:8],
      //   " ", i_cache_rdata[56+:8]);

      // if (o_cache_addr >= 64'h8000_0200) begin
        // o_cache_op       <= `REQ_WRITE;
      // end

      reg_rand_idx     <= reg_rand_idx + 1;              // 数据偏移
      o_cache_addr     <= o_cache_addr + 64'h8;    // 地址偏移

      if (o_cache_addr >= 64'h8001_0000) begin
        o_cache_addr <= 64'h8000_0000;
      end
    end
    else begin
      // if (!(i_cache_ack | o_cache_req)) begin    // 测试连续请求，也是可以的。
      // 计数1000后发出请求
      cnt <= cnt + 1;
      if (cnt >= 5) begin
        o_cache_req <= 1;
      end
    end
  end
end

cache_top Cache_top(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_top_addr           (o_cache_addr               ),
	.i_cache_top_wdata          (o_cache_wdata              ),
	.i_cache_top_bytes          (o_cache_bytes              ),
	.i_cache_top_op             (o_cache_op                 ),
	.i_cache_top_req            (o_cache_req                ),
	.o_cache_top_rdata          (i_cache_rdata              ),
	.o_cache_top_ack            (i_cache_ack                ),

  .i_cache_rw_axi_ready       (i_cache_rw_axi_ready       ),
  .i_cache_rw_axi_rdata       (i_cache_rw_axi_rdata       ),
  .o_cache_rw_axi_op          (o_cache_rw_axi_op          ),
  .o_cache_rw_axi_valid       (o_cache_rw_axi_valid       ),
  .o_cache_rw_axi_wdata       (o_cache_rw_axi_wdata       ),
  .o_cache_rw_axi_addr        (o_cache_rw_axi_addr        ),
  .o_cache_rw_axi_size        (o_cache_rw_axi_size        ),
  .o_cache_rw_axi_blks        (o_cache_rw_axi_blks        )
);


endmodule
