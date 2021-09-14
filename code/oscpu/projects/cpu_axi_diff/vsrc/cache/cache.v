
// ZhengpuShi

// Cache Interface
// 对ICache和DCache的统一

`include "../defines.v"

module cache(
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
    input   wire  [3 :0]      i_dcache_bytes,
    input   wire  [63:0]      i_dcache_wdata,
    output  wire              o_dcache_ack,
    output  wire  [63:0]      o_dcache_rdata,
    
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


wire [63:0] icache_rdata;
assign o_icache_rdata = icache_rdata[31:0];

cache_core ICache(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_core_addr          (i_icache_addr              ),
	.i_cache_core_wdata         (                           ),
	.i_cache_core_bytes         (3                          ),
	.i_cache_core_op            (`REQ_READ                  ),
	.i_cache_core_req           (i_icache_req               ),
	.o_cache_core_rdata         (icache_rdata               ),
	.o_cache_core_ack           (o_icache_ack               ),

  .i_axi_io_ready             (i_axi_io_ready             ),
  .i_axi_io_rdata             (i_axi_io_rdata             ),
  .o_axi_io_op                (o_axi_io_op                ),
  .o_axi_io_valid             (o_axi_io_valid             ),
  .o_axi_io_wdata             (o_axi_io_wdata             ),
  .o_axi_io_addr              (o_axi_io_addr              ),
  .o_axi_io_size              (o_axi_io_size              ),
  .o_axi_io_blks              (o_axi_io_blks              )
);


cache_core DCache(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_core_addr          (i_icache_addr              ),
	.i_cache_core_wdata         (                           ),
	.i_cache_core_bytes         (3                          ),
	.i_cache_core_op            (`REQ_READ                  ),
	.i_cache_core_req           (i_icache_req               ),
	.o_cache_core_rdata         (icache_rdata               ),
	.o_cache_core_ack           (o_icache_ack               ),

  .i_axi_io_ready             (i_axi_io_ready             ),
  .i_axi_io_rdata             (i_axi_io_rdata             ),
  .o_axi_io_op                (o_axi_io_op                ),
  .o_axi_io_valid             (o_axi_io_valid             ),
  .o_axi_io_wdata             (o_axi_io_wdata             ),
  .o_axi_io_addr              (o_axi_io_addr              ),
  .o_axi_io_size              (o_axi_io_size              ),
  .o_axi_io_blks              (o_axi_io_blks              )
);

endmodule
