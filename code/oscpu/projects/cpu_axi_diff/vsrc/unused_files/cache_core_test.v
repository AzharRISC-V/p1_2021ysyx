
// ZhengpuShi

// cache_core Test Interface

`include "defines.v"

module cache_core_test(
  input   wire                      clk,
  input   wire                      rst,

  // AXI interface
  input   wire  [511:0]             i_axi_io_rdata,
  input   wire                      i_axi_io_ready,
  output  wire                      o_axi_io_valid,
  output  wire                      o_axi_io_op,
  output  wire  [511:0]             o_axi_io_wdata,
  output  wire  [63:0]              o_axi_io_addr,
  output  wire  [1:0]               o_axi_io_size,
  output  wire  [7:0]               o_axi_io_blks
);

reg   [63 : 0]                      o_cache_basic_addr;        // 存储器地址（字节为单位），64字节对齐，低6位为0。
reg   [63 : 0]                      o_cache_basic_wdata;       // 要写入的数据
reg   [2  : 0]                      o_cache_basic_bytes;       // 字节数
reg                                 o_cache_basic_op;          // 操作类型：0读取，1写入
reg                                 o_cache_basic_req;         // 请求
wire  [63 : 0]                      i_cache_basic_rdata;       // 已读出的数据
wire                                i_cache_basic_ack;         // 应答

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
// assign o_cache_basic_wdata = reg_rand[reg_rand_idx];

// 指示读出的数据是否与写入的一致
wire equal_flag = o_cache_basic_wdata == i_cache_basic_rdata;

reg [`YSYX210544_BUS_64] cnt;
wire hs = o_cache_basic_req & i_cache_basic_ack;
wire hs_read  = hs & (o_cache_basic_op == `YSYX210544_REQ_READ);
wire hs_write = hs & (o_cache_basic_op == `YSYX210544_REQ_WRITE);

// 演示：延时；写入64字节；延时；读取64字节；。。。
reg f1;
always @(posedge clk) begin
  if (rst) begin
    cnt <= 0;
    o_cache_basic_req     <= 0;
    o_cache_basic_bytes   <= 7;
    o_cache_basic_addr    <= 64'h8000_0000;//3D;// 64'h8000_0400;// `YSYX210544_PC_START;
    o_cache_basic_wdata   <= 64'h01234567_0000_0000 | 64'h8000_0000;
    o_cache_basic_op      <= `YSYX210544_REQ_READ;// `YSYX210544_REQ_READ;// `YSYX210544_REQ_WRITE;
    reg_rand_idx    <= 0;
    f1 <= 0;
  end
  else begin
    // 写入完毕
    if (hs_write) begin
      o_cache_basic_req     <= 0;
      cnt             <= 0;
      o_cache_basic_op      <= `YSYX210544_REQ_READ;
      o_cache_basic_addr    <= o_cache_basic_addr + 64'h8;    // 地址偏移
      o_cache_basic_wdata   <= 64'h01234567_0000_0000 | (o_cache_basic_addr + 64'h8);

      if (o_cache_basic_addr >= 64'h8000_11F8) begin
        o_cache_basic_addr    <= 64'h8000_0000;
        // 第一轮读写完毕后，记录该标志
        f1 <= 1;
      end

    end
    // 读取完毕
    else if (hs_read) begin
      o_cache_basic_req     <= 0;
      cnt             <= 0;
      if (!f1) begin
        o_cache_basic_op      <= `YSYX210544_REQ_WRITE;
      end
      else begin
        o_cache_basic_addr    <= o_cache_basic_addr + 64'h8;    // 地址偏移
      end

      // $displayh("a:", o_cache_basic_addr, ", d:",
      //   " ", i_cache_basic_rdata[ 0+:8],
      //   " ", i_cache_basic_rdata[ 8+:8],
      //   " ", i_cache_basic_rdata[16+:8],
      //   " ", i_cache_basic_rdata[24+:8],
      //   " ", i_cache_basic_rdata[32+:8],
      //   " ", i_cache_basic_rdata[40+:8],
      //   " ", i_cache_basic_rdata[48+:8],
      //   " ", i_cache_basic_rdata[56+:8]);
      reg_rand_idx     <= reg_rand_idx + 1;              // 数据偏移

    end
    else begin
      // if (!(i_cache_basic_ack | o_cache_basic_req)) begin    // 测试连续请求，也是可以的。
      // 计数1000后发出请求
      cnt <= cnt + 1;
      if (cnt >= 5) begin
        o_cache_basic_req <= 1;
      end
    end
  end
end

cache_core Cache_core(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_core_addr          (o_cache_basic_addr               ),
	.i_cache_core_wdata         (o_cache_basic_wdata              ),
	.i_cache_core_bytes         (o_cache_basic_bytes              ),
	.i_cache_core_op            (o_cache_basic_op                 ),
	.i_cache_core_req           (o_cache_basic_req                ),
	.o_cache_core_rdata         (i_cache_basic_rdata              ),
	.o_cache_core_ack           (i_cache_basic_ack                ),

  .i_axi_io_ready             (i_axi_io_ready             ),
  .i_axi_io_rdata             (i_axi_io_rdata             ),
  .o_axi_io_op                (o_axi_io_op                ),
  .o_axi_io_valid             (o_axi_io_valid             ),
  .o_axi_io_wdata             (o_axi_io_wdata             ),
  .o_axi_io_addr              (o_axi_io_addr              ),
  .o_axi_io_size              (o_axi_io_size              ),
  .o_axi_io_blks              (o_axi_io_blks              )
);


endmodule
