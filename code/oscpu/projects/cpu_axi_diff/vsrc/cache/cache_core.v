
// ZhengpuShi

// Cache Core Unit
// 支持不对齐访问的Cache核心模块
// 封装了 cache_basic，将不对齐的访问转换为1~2次cache访问。

`include "../defines.v"

module cache_core (
  input   wire                clk,
  input   wire                rst,
  input   wire  [`BUS_64]     i_cache_core_addr,          // 地址
  input   wire  [`BUS_64]     i_cache_core_wdata,         // 写入的数据
  input   wire  [2 : 0]       i_cache_core_bytes,         // 操作的字节数: 0~7表示1~8字节
	input   wire                i_cache_core_op,            // 操作: 0:read, 1:write
	input   wire                i_cache_core_req,           // 请求
  output  reg   [`BUS_64]     o_cache_core_rdata,         // 读出的数据
	output  reg                 o_cache_core_ack,           // 应答

  // AXI interface
  input   wire  [511:0]       i_axi_io_rdata,
  input   wire                i_axi_io_ready,
  output  wire                o_axi_io_valid,
  output  wire                o_axi_io_op,
  output  wire  [511:0]       o_axi_io_wdata,
  output  wire  [63:0]        o_axi_io_addr,
  output  wire  [1:0]         o_axi_io_size,
  output  wire  [7:0]         o_axi_io_blks
);

// =============== cache 从机端 ===============

reg   [63 : 0]                o_cache_basic_addr;         // 存储器地址（字节为单位），64字节对齐，低6位为0。
reg   [63 : 0]                o_cache_basic_wdata;        // 要写入的数据
reg   [2  : 0]                o_cache_basic_bytes;        // 字节数
wire                          o_cache_basic_op;           // 操作类型：0读取，1写入
reg                           o_cache_basic_req;          // 请求
wire  [63 : 0]                i_cache_basic_rdata;        // 已读出的数据
reg                           i_cache_basic_ack;          // 应答

assign o_cache_basic_op = i_cache_core_op;

cache_basic Cache_basic(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_basic_addr         (o_cache_basic_addr         ),
	.i_cache_basic_wdata        (o_cache_basic_wdata        ),
	.i_cache_basic_bytes        (o_cache_basic_bytes        ),
	.i_cache_basic_op           (o_cache_basic_op           ),
	.i_cache_basic_req          (o_cache_basic_req          ),
	.o_cache_basic_rdata        (i_cache_basic_rdata        ),
	.o_cache_basic_ack          (i_cache_basic_ack          ),

  .i_axi_io_ready             (i_axi_io_ready             ),
  .i_axi_io_rdata             (i_axi_io_rdata             ),
  .o_axi_io_op                (o_axi_io_op                ),
  .o_axi_io_valid             (o_axi_io_valid             ),
  .o_axi_io_wdata             (o_axi_io_wdata             ),
  .o_axi_io_addr              (o_axi_io_addr              ),
  .o_axi_io_size              (o_axi_io_size              ),
  .o_axi_io_blks              (o_axi_io_blks              )
);


// =============== 处理跨行问题 ===============

wire  [59:0]                  i_addr_high;                // 输入地址的高60位
wire  [3:0]                   i_addr_4;                   // 输入地址的低4位 (0~15)
wire  [3:0]                   i_bytes_4;                  // 输入字节数扩展为4位

assign i_addr_high = i_cache_core_addr[63:4];
assign i_addr_4 = i_cache_core_addr[3:0];
assign i_bytes_4 = {1'd0, i_cache_core_bytes};

wire                          en_second;                  // 第二次操作使能
wire  [2 : 0]                 bytes[0:1];                 // 字节数
wire  [63: 0]                 addr[0:1];                  // 地址
wire  [63: 0]                 wdata[0:1];                 // 写数据
reg   [63: 0]                 rdata[0:1];                 // 读数据

assign en_second = i_addr_4 + i_bytes_4 < i_addr_4;
assign bytes[0] = en_second ? {4'd15 - i_addr_4}[2:0] : i_cache_core_bytes;
assign bytes[1] = en_second ? {i_addr_4 + i_bytes_4}[2:0] : 0;
assign addr[0] = i_cache_core_addr;
assign addr[1] = {i_addr_high + 60'd1, 4'd0};
assign wdata[0] = i_cache_core_wdata;
assign wdata[1] = i_cache_core_wdata >> (({3'd0,bytes[0]} + 1) << 3);

wire hs_cache = i_cache_basic_ack & o_cache_basic_req;

assign o_cache_basic_addr = (index == 0) ? addr[0] : addr[1];
assign o_cache_basic_bytes = (index == 0) ? bytes[0] : bytes[1];
assign o_cache_basic_wdata = (index == 0) ? wdata[0] : wdata[1];

reg   index;      // 操作的序号：0,1表示两个阶段
always @(posedge clk) begin
  if (rst) begin
    index <= 0;
    o_cache_basic_req <= 0;
  end
  else begin
    // 发现用户请求
    if (i_cache_core_req & !o_cache_core_ack) begin
      // 第一次请求
      if (index == 0) begin
        // 发出请求
        if (!hs_cache) begin
          o_cache_basic_req <= 1;
        end
        // 收到回应
        else begin
          o_cache_basic_req <= 0;
          rdata[0] <= i_cache_basic_rdata;
          // 启动第二次请求，或者结束任务
          if (en_second) begin
            index <= 1;
          end
          else begin
            o_cache_core_rdata <= i_cache_basic_rdata;
            o_cache_core_ack <= 1;
          end
        end
      end
      // 第二次请求
      else if (index == 1) begin
        // 发出请求
        if (!hs_cache) begin
          o_cache_basic_req <= 1;
        end
        // 收到回应
        else begin
          rdata[1] <= i_cache_basic_rdata;
          o_cache_core_rdata <= rdata[0] + (i_cache_basic_rdata << ((bytes[0] + 1) << 3));
          o_cache_basic_req <= 0;
          o_cache_core_ack <= 1;
        end
      end
    end
    // 结束应答
    else begin
      index <= 0;
      o_cache_core_ack <= 0;
    end
  end
end


endmodule
