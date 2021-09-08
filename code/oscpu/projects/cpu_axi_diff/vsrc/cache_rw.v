
// ZhengpuShi

// Cache ReadWrite Unit
// 通过AXI更新Cache数据的功能，根据Cache的设计而定制的AXI访问控制
// 对外接口：访问256字节（=2048bit），包括读、写
// 内部需要转换为AXI访问的多次读写。现在测试发现一次可以传输512bit(=64字节)，1024会出错。

`include "defines.v"

module cache_rw(
  input   wire                      clk,
  input   wire                      rst,
	input                             i_cache_rw_req,
	output  reg                       o_cache_rw_ack,
  input   wire  [`BUS_64]           i_cache_rw_addr,         // 存储器地址（字节为单位），256对齐
  input   wire                      o_cache_rw_ren,          // 读使能
  input   wire                      o_cache_rw_wen,          // 写使能
  // input   reg   [2047:0]            o_cache_rw_wdata,        // 写入的数据
  // output  reg   [2047:0]            o_cache_rw_rdata,        // 读出的数据
  input   reg   [255:0]            o_cache_rw_wdata,        // 写入的数据
  output  reg   [255:0]            o_cache_rw_rdata,        // 读出的数据

  ///////////////////////////////////////////////
  // AXI interface
	input                             i_cache_axi_ready,
  // input         [`BUS_256]          i_cache_axi_rdata,
  input         [`BUS_64]          i_cache_axi_rdata,
  input         [1:0]               i_cache_axi_resp,
	output reg                        o_cache_axi_valid,
  output reg    [`BUS_64]           o_cache_axi_addr,
  output        [1:0]               o_cache_axi_size
);

// wire i_disable = !i_ena;

// assign o_axi_valid = 1'b1;

wire handshake_done = o_cache_axi_valid & i_cache_axi_ready;

assign o_cache_axi_size = `SIZE_D;

// // 传输次数，每次32字节，8次可得到256字节
// reg   [10 : 0] trans_cnt;   // 0,1,2,...
// wire  [10 : 0] offset_bytes = trans_cnt << 5;   // 0,32,64,...
// wire  [10 : 0] offset_bits  = trans_cnt << 8;   // 0,256,512,...

// 传输次数，每次8字节，4次可得到32字节
reg   [7 : 0] trans_cnt;   // 0,1,2,...
reg   [7 : 0] offset_bytes = trans_cnt << 3;   // 0,8,16,...
reg   [7 : 0] offset_bits  = trans_cnt << 6;   // 0,64,128,...


// 连续两个周期的 req 才认为是开始信号，防止一结束就又开始了新的阶段

reg axi_ready_last;
reg cache_req_his[2];

wire [`BUS_64] cache_rdata;

wire  access_start    = i_cache_rw_req & cache_req_his[0] & (!cache_req_his[1]);

// 传输起始地址，256字节对齐
// assign o_cache_axi_addr   = i_cache_rw_addr & (~64'hFF) + {53'd0, offset_bytes};
assign o_cache_axi_addr = i_cache_rw_addr & (~64'h1F) | {56'd0, offset_bytes};

// 控制传输
always @( posedge clk ) begin
  if (rst) begin
    o_cache_rw_rdata        <= 0;
    o_cache_rw_ack          <= 0;
    trans_cnt               <= 0;
    o_cache_axi_valid       <= 0;
    axi_ready_last          <= 0;
    cache_req_his[0]        <= 0;
    cache_req_his[1]        <= 0;
  end
  else begin
    // 追踪开始信号
    cache_req_his[0]  <= i_cache_rw_req;
    cache_req_his[1]  <= cache_req_his[0]; 
    axi_ready_last    <= i_cache_axi_ready;

    // 收到数据：保存数据、增加计数、握手反馈
    if (handshake_done) begin

      //o_cache_rw_rdata[offset_bits +: 256] <= i_cache_axi_rdata;
      o_cache_rw_rdata[offset_bits +: 64] <= i_cache_axi_rdata;

      if (trans_cnt == 3) begin
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
      if (access_start) begin
        o_cache_axi_valid <= 1;
        o_cache_rw_rdata  <= 0;
      end
      // 清除信号   
      o_cache_rw_ack    <= 0;
    end
  end
end


endmodule
