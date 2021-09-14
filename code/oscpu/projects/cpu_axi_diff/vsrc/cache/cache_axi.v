
// ZhengpuShi

// Cache AXI Unit
// Cache的AXI通信模块。
// 通过AXI更新Cache数据的，根据Cache的设计而定制的AXI访问控制
// 对外接口：访问64字节（=512bit），包括读、写
// 内部需要转换为AXI访问的多次读写。
// 1. AXI数据宽度最多64bit，已确认。
// 2. AXI burst len最多是8，这样一次最多传输64字节。

`include "defines.v"

module cache_axi(
  input   wire                      clk,
  input   wire                      rst,
	input                             i_cache_rw_req,         // 请求读写
  input   wire  [63 : 0]            i_cache_rw_addr,        // 存储器地址（字节为单位），128字节对齐，低7位为0。
  input   wire                      i_cache_rw_op,          // 操作类型：0读取，1写入
  input   reg   [511 : 0]           i_cache_rw_wdata,       // 写入的数据
  output  reg   [511 : 0]           o_cache_rw_rdata,       // 读出的数据
	output  reg                       o_cache_rw_ack,         // 读写完成应答

  ///////////////////////////////////////////////
  // AXI interface
	output                            o_cache_rw_axi_op,        // 0:read, 1:write
	input                             i_cache_rw_axi_ready,
  input         [511 : 0]           i_cache_rw_axi_rdata,
	output reg                        o_cache_rw_axi_valid,
  output reg    [63 : 0]            o_cache_rw_axi_addr,
  output        [511 : 0]           o_cache_rw_axi_wdata,
  output        [1 : 0]             o_cache_rw_axi_size,
  output        [7 : 0]             o_cache_rw_axi_blks
);

// axi一次传输完成
wire hs_ok = o_cache_rw_axi_valid & i_cache_rw_axi_ready;

// axi每次传输的大小：64bit
assign o_cache_rw_axi_size = `SIZE_D;

// 块数：0~7表示1~8块
assign o_cache_rw_axi_blks = 7;

// 操作类型：0:read, 1:write
assign o_cache_rw_axi_op = i_cache_rw_op;

// 跟踪req信号，连续两个周期的 req 才认为是开始信号，防止一结束就又开始了新的阶段
reg cache_req_his[2];

// axi请求开始
wire  axi_start    = i_cache_rw_req & cache_req_his[0] & (!cache_req_his[1]);
wire  axi_start2   = i_cache_rw_req & !cache_req_his[0];// & (!cache_req_his[1]);

// 传输起始地址，64字节对齐
assign o_cache_rw_axi_addr = i_cache_rw_addr & (~64'h3F);

// 控制传输
always @( posedge clk ) begin
  if (rst) begin
    // o_cache_rw_rdata        <= 0;
    o_cache_rw_ack          <= 0;
    o_cache_rw_axi_valid       <= 0;
    cache_req_his[0]        <= 0;
    cache_req_his[1]        <= 0;
  end
  else begin
    // 追踪开始信号
    cache_req_his[0]  <= i_cache_rw_req;
    cache_req_his[1]  <= cache_req_his[0]; 

    // 收到数据：保存数据、增加计数、握手反馈
    if (hs_ok) begin
      // o_cache_rw_rdata  <= i_cache_rw_axi_rdata;
      o_cache_rw_ack    <= 1;
      o_cache_rw_axi_valid <= 0;
    end
    else begin
      // 触发采样
      if (axi_start2) begin
        o_cache_rw_axi_valid <= 1;
        // o_cache_rw_rdata  <= 0;
      end
      // 清除信号   
      o_cache_rw_ack    <= 0;
    end
  end
end

assign o_cache_rw_rdata = i_cache_rw_axi_rdata;
assign o_cache_rw_axi_wdata = i_cache_rw_wdata;

endmodule
