
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
wire                          o_cache_op;          // 操作类型：0读取，1写入
reg                           o_cache_req;         // 请求
wire  [63 : 0]                i_cache_rdata;       // 已读出的数据
reg                           i_cache_ack;         // 应答

assign o_cache_op = i_cache_top_op;

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


// =============== 处理跨行问题 ===============

wire  [57:0]                  i_addr_58;                  // 输入地址的高58位
wire  [5:0]                   i_addr_6;                   // 输入地址的低6位 (0~63)
wire  [5:0]                   i_bytes_6;                  // 输入字节数扩展为6位

assign i_addr_58 = i_cache_top_addr[63:6];
assign i_addr_6 = i_cache_top_addr[5:0];
assign i_bytes_6 = {3'd0, i_cache_top_bytes};

wire                          en_second;                  // 第二次操作使能
wire  [2 : 0]                 bytes[0:1];                 // 字节数
wire  [63: 0]                 addr[0:1];                  // 地址
wire  [63: 0]                 wdata[0:1];                 // 写数据
reg   [63: 0]                 rdata[0:1];                 // 读数据

assign en_second = i_addr_6 + i_bytes_6 < i_addr_6;
assign bytes[0] = en_second ? {6'd63 - i_addr_6}[2:0] : i_cache_top_bytes;
assign bytes[1] = en_second ? {i_addr_6 + i_bytes_6}[2:0] : 0;
assign addr[0] = i_cache_top_addr;
assign addr[1] = {i_addr_58 + 58'd1, 6'd0};
assign wdata[0] = i_cache_top_wdata;
assign wdata[1] = i_cache_top_wdata >> (({3'd0,bytes[0]} + 1) << 3);

// parameter [1:0] STATE_FIRST = 2'd0;
// parameter [1:0] STATE_SECOND = 2'd1;
// parameter [1:0] STATE_FIRST = 2'd0;

wire hs_cache = i_cache_ack & o_cache_req;

wire [63:0] s1 = addr[0];

reg   index;      // 操作的序号：0,1
always @(posedge clk) begin
  if (rst) begin
    index <= 0;
    o_cache_req <= 0;
  end
  else begin
    // 发现用户请求
    if (i_cache_top_req) begin
      // 第一次请求
      if (index == 0) begin
        // 发出请求
        if (!hs_cache) begin
          o_cache_addr <= i_cache_top_addr;// addr[0];
          o_cache_bytes <= bytes[0];
          o_cache_wdata <= wdata[0];
          o_cache_req <= 1;
        end
        // 收到回应
        else begin
          o_cache_req <= 0;
          // 启动第二次请求，或者结束任务
          if (en_second) begin
            index <= index + 1;
          end
          else begin
            o_cache_top_ack <= 1;
          end
        end
      end
      // 第二次请求
      else if (index == 1) begin
        // 发出请求
        if (!hs_cache) begin
          o_cache_addr <= addr[1];
          o_cache_bytes <= bytes[1];
          o_cache_wdata <= wdata[1];
          o_cache_req <= 1;
        end
        // 收到回应
        else begin
          o_cache_req <= 0;
          index <= 0;
          o_cache_top_ack <= 1;
        end
      end
    end
    // 结束应答
    else begin
      o_cache_top_ack <= 0;
    end
  end
end


endmodule
