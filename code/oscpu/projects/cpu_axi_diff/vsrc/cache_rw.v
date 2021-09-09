
// ZhengpuShi

// Cache ReadWrite Unit
// 通过AXI更新Cache数据的，根据Cache的设计而定制的AXI访问控制
// 对外接口：访问64字节（=512bit），包括读、写
// 内部需要转换为AXI访问的多次读写。
// 1. AXI数据宽度最多64bit，已确认。
// 2. AXI burst len最多是8，这样一次最多传输64字节。
/*
  Cache Disign (2021.09.08, by ZhengpuShi):
    [*] word_size = 32bit (4 bytes)             ----- 指令是32bit的
    [*] block_size = 512bit (64 bytes)          ----- AXI总线burst最大传输8次*8字节=64字节
    [*] offset index bits = 6 (2^6 = 64)        ----- 由块大小决定
    [*] cache ways = 2way                       ----- 路数与块数的决定比较困难，至少2路，总容量受限于4KB（包括data、tag、v、d等字段）
    [*] cache blocks per way = 16blocks         ----- 同上
    [*] cache data bytes = 2 * 16 * 64B = 2KB   ----- 由总容量、路数、块数决定
    [*] cache block index bits = 4 (2^4 = 16)   ----- 由块数决定
    [*] main memory bytes = 2GB = 2^31          ----- 主存地址空间2GB
    [*] bits_data = 512                         ----- 由块大小决定
    [*] bits_tag = 31 - 4 - 6 = 21              ----- 主存位数 - cache块数的位数 - 块内位数
    [*] bits_v = 1 (data valid)
    [*] bits_d = 1 (data dirty, need to writeback when replace it out)
    [*] bits_time = 2 (write time, for replace )
    [*] cache bits = 16 * 2 * (2 + 1 + 1 + 21 + 512) = 17216
    [*] cache bytes = 17216 / 8 = 2152
*/
`include "defines.v"

module cache_rw(
  input   wire                      clk,
  input   wire                      rst,
	input                             i_cache_rw_req,         // 请求读写
	output  reg                       o_cache_rw_ack,         // 读写完成应答
  input   wire  [63 : 0]            i_cache_rw_addr,        // 存储器地址（字节为单位），128字节对齐，低7位为0。
  input   wire                      o_cache_rw_ren,         // 读使能
  input   wire                      o_cache_rw_wen,         // 写使能
  input   reg   [511 : 0]           o_cache_rw_wdata,       // 写入的数据
  output  reg   [511 : 0]           o_cache_rw_rdata,       // 读出的数据

  ///////////////////////////////////////////////
  // AXI interface
	input                             i_cache_axi_wen,        // 1:write, 0:read
	input                             i_cache_axi_ready,
  input         [511 : 0]           i_cache_axi_rdata,
  input         [1 : 0]             i_cache_axi_resp,
	output reg                        o_cache_axi_valid,
  output reg    [63 : 0]            o_cache_axi_addr,
  // output        [63 : 0]            o_cache_axi_wdata,
  output        [1 : 0]             o_cache_axi_size
);

// axi一次传输完成
wire hs_ok = o_cache_axi_valid & i_cache_axi_ready;

// axi每次传输的大小
assign o_cache_axi_size = `SIZE_D;

// 跟踪req信号，连续两个周期的 req 才认为是开始信号，防止一结束就又开始了新的阶段
reg cache_req_his[2];

// axi请求开始
wire  axi_start    = i_cache_rw_req & cache_req_his[0] & (!cache_req_his[1]);

// 传输起始地址，64字节对齐
assign o_cache_axi_addr = i_cache_rw_addr & (~64'h3F);

// 控制传输
always @( posedge clk ) begin
  if (rst) begin
    o_cache_rw_rdata        <= 0;
    o_cache_rw_ack          <= 0;
    o_cache_axi_valid       <= 0;
    cache_req_his[0]        <= 0;
    cache_req_his[1]        <= 0;
  end
  else begin
    // 追踪开始信号
    cache_req_his[0]  <= i_cache_rw_req;
    cache_req_his[1]  <= cache_req_his[0]; 

    // 收到数据：保存数据、增加计数、握手反馈
    if (hs_ok) begin
      o_cache_rw_rdata  <= i_cache_axi_rdata;
      o_cache_rw_ack    <= 1;
      o_cache_axi_valid <= 0;
    end
    else begin
      // 触发采样
      if (axi_start) begin
        o_cache_axi_valid <= 1;
        o_cache_rw_rdata  <= 0;
      end
      // 清除信号   
      o_cache_rw_ack    <= 0;
    end
  end
end


endmodule