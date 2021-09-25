
// ZhengpuShi

// Cache Interface
// 对ICache和DCache的统一

`include "defines.v"

module ysyx_210544_cache(
    input                     clk,
    input                     rst,
    
    // ICache
    input   wire              i_icache_req,
    input   wire  [63:0]      i_icache_addr,
    output  wire              o_icache_ack,
    output  wire  [31:0]      o_icache_rdata,

    // DCache
    input   wire              i_dcache_req,
    input   wire  [63:0]      i_dcache_addr,
    input   wire              i_dcache_op,
    input   wire  [2 :0]      i_dcache_bytes,
    input   wire  [63:0]      i_dcache_wdata,
    output  wire              o_dcache_ack,
    output  wire  [63:0]      o_dcache_rdata,

    // No Cache
    input   wire              i_nocache_req,
    input   wire  [63:0]      i_nocache_addr,
    input   wire              i_nocache_op,
    input   wire  [2 :0]      i_nocache_bytes,
    input   wire  [63:0]      i_nocache_wdata,
    output  wire              o_nocache_ack,
    output  wire  [63:0]      o_nocache_rdata,
    
    // AXI interface
    input   wire  [511:0]     i_axi_io_rdata,
    input   wire              i_axi_io_ready,
    output  wire              o_axi_io_valid,
    output  wire              o_axi_io_op,
    output  wire  [511:0]     o_axi_io_wdata,
    output  wire  [63:0]      o_axi_io_addr,
    output  wire  [1:0]       o_axi_io_size,
    output  wire  [7:0]       o_axi_io_blks
);


// 数据选择器
wire ch_icache = i_icache_req;
wire ch_dcache = i_dcache_req;
wire ch_nocache = i_nocache_req;

wire [63:0] icache_rdata;
assign o_icache_rdata = icache_rdata[31:0];

reg              icache_axi_io_valid;
reg              icache_axi_io_op;
reg  [511:0]     icache_axi_io_wdata;
reg  [63:0]      icache_axi_io_addr;
reg  [1:0]       icache_axi_io_size;
reg  [7:0]       icache_axi_io_blks;

reg              dcache_axi_io_valid;
reg              dcache_axi_io_op;
reg  [511:0]     dcache_axi_io_wdata;
reg  [63:0]      dcache_axi_io_addr;
reg  [1:0]       dcache_axi_io_size;
reg  [7:0]       dcache_axi_io_blks;

reg              nocache_axi_io_valid;
reg              nocache_axi_io_op;
reg  [511:0]     nocache_axi_io_wdata;
reg  [63:0]      nocache_axi_io_addr;
reg  [1:0]       nocache_axi_io_size;
reg  [7:0]       nocache_axi_io_blks;

ysyx_210544_cache_core ICache(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_core_addr          (i_icache_addr              ),
	.i_cache_core_wdata         (0                          ),
	.i_cache_core_bytes         (3                          ),
	.i_cache_core_op            (`REQ_READ                  ),
	.i_cache_core_req           (i_icache_req               ),
	.o_cache_core_rdata         (icache_rdata               ),
	.o_cache_core_ack           (o_icache_ack               ),

  .i_axi_io_ready             (ch_icache ? i_axi_io_ready : 0        ),
  .i_axi_io_rdata             (ch_icache ? i_axi_io_rdata : 0        ),
  .o_axi_io_op                (icache_axi_io_op           ),
  .o_axi_io_valid             (icache_axi_io_valid        ),
  .o_axi_io_wdata             (icache_axi_io_wdata        ),
  .o_axi_io_addr              (icache_axi_io_addr         ),
  .o_axi_io_size              (icache_axi_io_size         ),
  .o_axi_io_blks              (icache_axi_io_blks         )
);

ysyx_210544_cache_core DCache(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_core_addr          (i_dcache_addr              ),
	.i_cache_core_wdata         (i_dcache_wdata             ),
	.i_cache_core_bytes         (i_dcache_bytes             ),
	.i_cache_core_op            (i_dcache_op                ),
	.i_cache_core_req           (i_dcache_req               ),
	.o_cache_core_rdata         (o_dcache_rdata             ),
	.o_cache_core_ack           (o_dcache_ack               ),

  .i_axi_io_ready             (ch_dcache ? i_axi_io_ready : 0        ),
  .i_axi_io_rdata             (ch_dcache ? i_axi_io_rdata : 0        ),
  .o_axi_io_op                (dcache_axi_io_op           ),
  .o_axi_io_valid             (dcache_axi_io_valid        ),
  .o_axi_io_wdata             (dcache_axi_io_wdata        ),
  .o_axi_io_addr              (dcache_axi_io_addr         ),
  .o_axi_io_size              (dcache_axi_io_size         ),
  .o_axi_io_blks              (dcache_axi_io_blks         )
);


// 访问UART
ysyx_210544_cache_nocache NoCache(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_nocache_addr       (i_nocache_addr             ),
	.i_cache_nocache_wdata      (i_nocache_wdata            ),
	.i_cache_nocache_bytes      (i_nocache_bytes            ),
	.i_cache_nocache_op         (i_nocache_op               ),
	.i_cache_nocache_req        (i_nocache_req              ),
	.o_cache_nocache_rdata      (o_nocache_rdata            ),
	.o_cache_nocache_ack        (o_nocache_ack              ),

  .i_axi_io_ready             (ch_nocache ? i_axi_io_ready : 0        ),
  .i_axi_io_rdata             (ch_nocache ? i_axi_io_rdata : 0        ),
  .o_axi_io_op                (nocache_axi_io_op          ),
  .o_axi_io_valid             (nocache_axi_io_valid       ),
  .o_axi_io_wdata             (nocache_axi_io_wdata       ),
  .o_axi_io_addr              (nocache_axi_io_addr        ),
  .o_axi_io_size              (nocache_axi_io_size        ),
  .o_axi_io_blks              (nocache_axi_io_blks        )
);

assign o_axi_io_valid   = ch_icache ? icache_axi_io_valid   : (ch_dcache ? dcache_axi_io_valid  : nocache_axi_io_valid);
assign o_axi_io_op      = ch_icache ? icache_axi_io_op      : (ch_dcache ? dcache_axi_io_op     : nocache_axi_io_op);
assign o_axi_io_wdata   = ch_icache ? icache_axi_io_wdata   : (ch_dcache ? dcache_axi_io_wdata  : nocache_axi_io_wdata);
assign o_axi_io_addr    = ch_icache ? icache_axi_io_addr    : (ch_dcache ? dcache_axi_io_addr   : nocache_axi_io_addr);
assign o_axi_io_size    = ch_icache ? icache_axi_io_size    : (ch_dcache ? dcache_axi_io_size   : nocache_axi_io_size);
assign o_axi_io_blks    = ch_icache ? icache_axi_io_blks    : (ch_dcache ? dcache_axi_io_blks   : nocache_axi_io_blks);


wire _unused_ok = &{1'b0,
  icache_rdata[63:32],
  1'b0};

endmodule
