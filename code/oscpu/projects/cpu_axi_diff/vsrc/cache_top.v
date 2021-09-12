
// ZhengpuShi

// Cache Top Unit
// 为处理64字节不对齐访问而设计的Cache之上的模块。
// 将可能不对齐的访问转换为1~2次cache访问。

`include "defines.v"

module cache_top (
  input   wire                clk,
  input   wire                rst,
  input   wire  [`BUS_64]     i_cache_top_addr,           // 地址
  input   reg   [`BUS_64]     i_cache_top_wdata,          // 写入的数据
  input   reg   [2 : 0]       i_cache_top_bytes,          // 操作的字节数: 0~7表示1~8字节
	input                       i_cache_top_op,             // 操作: 0:read, 1:write
	input                       i_cache_top_req,            // 请求
  output  reg   [`BUS_64]     o_cache_top_rdata,          // 读出的数据
	output                      o_cache_top_ack,            // 应答

  // cache_rw 接口
  input   wire  [511:0]       i_cache_rw_axi_rdata,
  input   wire                i_cache_rw_axi_ready,
  output  wire                o_cache_rw_axi_valid,
  output  wire                o_cache_rw_axi_op,
  output  wire  [511:0]       o_cache_rw_axi_wdata,
  output  wire  [63:0]        o_cache_rw_axi_addr,
  output  wire  [1:0]         o_cache_rw_axi_size,
  output  wire  [7:0]         o_cache_rw_axi_blks
);

// =============== cache 从机端 ===============

reg   [63 : 0]                o_cache_addr;        // 存储器地址（字节为单位），64字节对齐，低6位为0。
reg   [63 : 0]                o_cache_wdata;       // 要写入的数据
reg   [2  : 0]                o_cache_bytes;       // 字节数
reg                           o_cache_op;          // 操作类型：0读取，1写入
reg                           o_cache_req;         // 请求
wire  [63 : 0]                i_cache_rdata;       // 已读出的数据
wire                          i_cache_ack;         // 应答

cache Cache(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_addr               (o_cache_addr               ),
	.i_cache_wdata              (o_cache_wdata              ),
	.i_cache_bytes              (o_cache_bytes              ),
	.i_cache_op                 (o_cache_op                 ),
	.i_cache_req                (o_cache_req                ),
	.o_cache_rdata              (i_cache_rdata              ),
	.o_cache_ack                (i_cache_ack                ),

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
