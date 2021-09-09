
// ZhengpuShi

// Cache Unit
// 参考 cache_rw.v 中的说明。

`include "defines.v"

module cache (
  input   wire                      clk,
  input   wire                      rst,
  input   wire  [`BUS_64]           i_cache_addr,         // 地址
  input   reg   [`BUS_64]           i_cache_wdata,        // 写入的数据
  input   reg   [`BUS_64]           i_cache_wmask,        // 写入的掩码
	input                             i_cache_op,           // 操作: 0:read, 1:write
	input                             i_cache_req,          // 请求
  output  reg   [`BUS_64]           o_cache_rdata,        // 读出的数据
	output                            o_cache_ack,          // 应答

  // cache_rw 接口
  input   wire  [511:0]             i_cache_rw_axi_rdata,
  input   wire                      i_cache_rw_axi_ready,
  output  wire                      o_cache_rw_axi_valid,
  output  wire                      o_cache_rw_axi_op,
  output  wire  [511:0]             o_cache_rw_axi_wdata,
  output  wire  [63:0]              o_cache_rw_axi_addr,
  output  wire  [1:0]               o_cache_rw_axi_size,
  output  wire  [7:0]               o_cache_rw_axi_blks
);

// ====== cache_rw 从机端，请求传输数据 ===============
reg                                 i_cache_rw_req;    // 请求
reg   [63 : 0]                      i_cache_rw_addr;   // 存储器地址（字节为单位），64字节对齐，低6位为0。
reg                                 i_cache_rw_op;     // 操作类型：0读取，1写入
reg   [511 : 0]                     i_cache_rw_wdata;  // 要写入的数据
wire  [511 : 0]                     o_cache_rw_rdata;  // 已读出的数据
wire                                o_cache_rw_ack;    // 应答

cache_rw Cache_rw(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_rw_req             (i_cache_rw_req             ),
	.i_cache_rw_addr            (i_cache_rw_addr            ),
	.i_cache_rw_op              (i_cache_rw_op              ),
	.i_cache_rw_wdata           (i_cache_rw_wdata           ),
	.o_cache_rw_rdata           (o_cache_rw_rdata           ),
	.o_cache_rw_ack             (o_cache_rw_ack             ),

  .i_cache_rw_axi_ready       (i_cache_rw_axi_ready       ),
  .i_cache_rw_axi_rdata       (i_cache_rw_axi_rdata       ),
  .o_cache_rw_axi_op          (o_cache_rw_axi_op          ),
  .o_cache_rw_axi_valid       (o_cache_rw_axi_valid       ),
  .o_cache_rw_axi_wdata       (o_cache_rw_axi_wdata       ),
  .o_cache_rw_axi_addr        (o_cache_rw_axi_addr        ),
  .o_cache_rw_axi_size        (o_cache_rw_axi_size        ),
  .o_cache_rw_axi_blks        (o_cache_rw_axi_blks        )
);

// 业务逻辑

// 命中判断
//  若存在，则返回
//  若不存在，则替换
//    FIFO策略

endmodule
