
// ZhengpuShi

// Cache ReadWrite Unit
// 通过AXI更新Cache数据的，根据Cache的设计而定制的AXI访问控制
// 对外接口：访问64字节（=512bit），包括读、写
// 内部需要转换为AXI访问的多次读写。
// 1. 现在测试发现一次可以传输512bit(=64字节)，1024会出错。
// 2. 但只使用64bit来传输，因为soc那边说还没有测试。
/*
  Cache Disign (2021.09.08, by ZhengpuShi):
    [*] word_size = 32bit (4 bytes)
    [*] block_size = 1024bit (128 bytes)
    [*] offset index bits = 7 (2^7 = 128)
    [*] cache address_mode: 2way * 8blocks
    [*] cache bytes = 2 * 8 * 128 Bytes = 2KB
    [*] cache block index bits = 3 (2^3 = 8)
    [*] main memory bytes = 256MB = 2^28
    [*] bits_data = block_size = 1024
    [*] bits_tag = 28 - 3 - 7 = 18
    [*] bits_v = 1 (data valid)
    [*] bits_d = 1 (data dirty, need to writeback when replace it out)
    [*] cache bits = 8 * 2 * (1 + 1 + 18 + 1024) = 16704
    [*] cache bytes = 16704 / 8 = 2088

  Cache and AXI communication:
    [*] axi access bits per time = 64bit
    [*] axi access bits total = 1024bit
    [*] axi access times = 1024 / 64 = 16
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
  input   reg   [1023 : 0]          o_cache_rw_wdata,       // 写入的数据
  output  reg   [1023 : 0]          o_cache_rw_rdata,       // 读出的数据

  ///////////////////////////////////////////////
  // AXI interface
	input                             i_cache_axi_ready,
  input         [63 : 0]            i_cache_axi_rdata,
  input         [1 : 0]             i_cache_axi_resp,
	output reg                        o_cache_axi_valid,
  output reg    [63 : 0]            o_cache_axi_addr,
  output        [1 : 0]             o_cache_axi_size
);

// axi一次传输完成
wire hs_once = o_cache_axi_valid & i_cache_axi_ready;

// axi每次传输的大小
assign o_cache_axi_size = `SIZE_D;

// 传输次数，每次64bit(=8bytes)，16次完成1024bit(=64bytes)
reg   [3 : 0] trans_cnt;   // 0,1,2,..,15
reg   [7 : 0] offset_bytes = trans_cnt << 3;   // 0,8,16,..,120
reg   [9 : 0] offset_bits  = trans_cnt << 6;   // 0,64,128,..,960

// 跟踪req信号，连续两个周期的 req 才认为是开始信号，防止一结束就又开始了新的阶段
reg cache_req_his[2];

// axi请求开始
wire  axi_start    = i_cache_rw_req & cache_req_his[0] & (!cache_req_his[1]);

// 传输起始地址，128字节对齐
assign o_cache_axi_addr = i_cache_rw_addr & (~64'h7F) | {56'd0, offset_bytes};

// 控制传输
always @( posedge clk ) begin
  if (rst) begin
    o_cache_rw_rdata        <= 0;
    o_cache_rw_ack          <= 0;
    trans_cnt               <= 0;
    o_cache_axi_valid       <= 0;
    cache_req_his[0]        <= 0;
    cache_req_his[1]        <= 0;
  end
  else begin
    // 追踪开始信号
    cache_req_his[0]  <= i_cache_rw_req;
    cache_req_his[1]  <= cache_req_his[0]; 

    // 收到数据：保存数据、增加计数、握手反馈
    if (hs_once) begin

      //o_cache_rw_rdata[offset_bits +: 256] <= i_cache_axi_rdata;
      o_cache_rw_rdata[offset_bits +: 64] <= i_cache_axi_rdata;

      if (trans_cnt == 15) begin
        trans_cnt         <= 0;
        o_cache_rw_ack    <= 1;
        o_cache_axi_valid <= 0;
      end
      else begin
        trans_cnt   <= trans_cnt + 1;
      end
    end
    else begin
      // 触发第一次采样
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
