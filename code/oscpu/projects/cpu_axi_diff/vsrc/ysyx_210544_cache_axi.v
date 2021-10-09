
// ZhengpuShi

// Cache AXI Unit
// Cache的AXI通信模块。
// 通过AXI更新Cache数据的，根据Cache的设计而定制的AXI访问控制
// 对外接口：访问64字节（=512bit），包括读、写
// 内部需要转换为AXI访问的多次读写。
// 1. AXI数据宽度最多64bit，已确认。
// 2. AXI burst len最多是8，这样一次最多传输64字节。

`include "defines.v"

module ysyx_210544_cache_axi(
  input   wire                      clk,
  input   wire                      rst,
  input                             i_cache_axi_req,        // 请求读写
  input   wire  [63 : 0]            i_cache_axi_addr,       // 存储器地址（字节为单位），128字节对齐，低7位为0。
  input   wire                      i_cache_axi_op,         // 操作类型：0读取，1写入
  input   wire  [511 : 0]           i_cache_axi_wdata,      // 写入的数据
  output  reg   [511 : 0]           o_cache_axi_rdata,      // 读出的数据
  output  reg                       o_cache_axi_ack,        // 读写完成应答

  ///////////////////////////////////////////////
  // AXI interface
  output                            o_axi_io_op,            // 0:read, 1:write
  input                             i_axi_io_ready,
  input         [511 : 0]           i_axi_io_rdata,
  output reg                        o_axi_io_valid,
  output reg    [63 : 0]            o_axi_io_addr,
  output reg    [511 : 0]           o_axi_io_wdata,
  output        [2 : 0]             o_axi_io_size,
  output        [7 : 0]             o_axi_io_blks
);


wire is_flash;    // 是否为Flash外设，此时只能4字节传输，且不能使用burst模式，所以64字节需要16次传输
wire hs_ok;       // axi一次传输完成
reg cache_req_his0;   // 跟踪req信号，连续两个周期的 req 才认为是开始信号，防止一结束就又开始了新的阶段
wire  axi_start;    // axi请求开始

reg [3:0] trans_cnt;          // 传输次数
reg [3:0] trans_cnt_write;    // 传输次数（写入）
wire [8:0] offset_bits;       // 偏移位数
wire [8:0] offset_bits_write; // 偏移位数（写入）



assign is_flash = i_cache_axi_addr[31:28] == 4'h3;
assign hs_ok = o_axi_io_valid & i_axi_io_ready;

// axi每次传输的大小：64bit
assign o_axi_io_size = is_flash ? `SIZE_W : `SIZE_D;

// 块数：0~7表示1~8块
assign o_axi_io_blks = is_flash ? 8'd0 : 8'd7;

// 操作类型：0:read, 1:write
assign o_axi_io_op = i_cache_axi_op;

assign axi_start    = i_cache_axi_req & !cache_req_his0;

// 传输起始地址，64字节对齐
// assign o_axi_io_addr = i_cache_axi_addr & (~64'h3F);

// 控制传输次数，
// 如果是主存，  需要 1次AXI传输得512bit；
// 如果是Flash，需要16次AXI传输得到512bit，每次传输32bit（64bit是否支持？？）；
assign offset_bits = {5'd0, trans_cnt} << 3'd5;
assign offset_bits_write = {5'd0, trans_cnt_write} << 3'd5;

// 控制传输
always @( posedge clk ) begin
  if (rst) begin
    o_cache_axi_ack         <= 1'd0;
    o_axi_io_valid          <= 1'd0;
    o_axi_io_addr           <= 64'd0;
    o_axi_io_wdata          <= 512'd0;
    cache_req_his0          <= 1'd0;
    trans_cnt               <= 4'd0;
  end
  else begin
    // 追踪开始信号
    cache_req_his0  <= i_cache_axi_req;

    // 收到数据：保存数据、增加计数、握手反馈
    if (hs_ok) begin
      if (is_flash) begin
          o_cache_axi_rdata[offset_bits +:32] <= i_axi_io_rdata[0+:32]; // 保存数据
        if (trans_cnt < 4'd15) begin
          o_axi_io_wdata    <= {480'd0, i_cache_axi_wdata[offset_bits_write +:32]}; // 准备数据
          o_axi_io_addr <= o_axi_io_addr + 64'd4;     // 地址递增
          trans_cnt <= trans_cnt + 4'd1;             // 次数递增
          trans_cnt_write <= trans_cnt_write + 4'd1;
        end
        else begin
          o_cache_axi_ack   <= 1'd1;   // 完成
          o_axi_io_valid    <= 1'd0;   // 关闭axi请求
          trans_cnt <= 4'd0;   // 清零计数，准备下次继续
          trans_cnt_write <= 4'd1; // 初始为1，方便计算偏移量
        end
      end
      else begin
        o_cache_axi_rdata <= i_axi_io_rdata;    // 保存数据
        o_cache_axi_ack   <= 1'd1;   // 完成
        o_axi_io_valid    <= 1'd0;   // 关闭axi请求
      end
    end
    else begin
      // 触发采样
      if (axi_start) begin
        // 仅在第一次进入时修改地址
        if (!o_axi_io_valid) begin
          if (is_flash) begin
            o_axi_io_addr <= i_cache_axi_addr & (~64'h3);   // 传输起始地址，4字节对齐
            o_axi_io_wdata    <= i_cache_axi_wdata;         // 准备数据
          end
          else begin
            o_axi_io_addr <= i_cache_axi_addr & (~64'h3F);  // 传输起始地址，64字节对齐
            o_axi_io_wdata    <= i_cache_axi_wdata;         // 准备数据
          end
        end
        o_axi_io_valid <= 1'd1;
      end
      // 清除信号   
      o_cache_axi_ack <= 1'd0;
    end
  end
end

// assign o_cache_axi_rdata = i_axi_io_rdata;
// assign o_axi_io_wdata = i_cache_axi_wdata;

endmodule
