
// ZhengpuShi

// Cache Interface
// 对ICache和DCache的统一入口

// module cache(
//     input                     clk,
//     input                     rst,
//     input                     if_ready,
//     input  [63:0]             if_rdata,
//     input  [1:0]              if_resp,
//     output                    if_valid,
//     output [63:0]             if_addr,
//     output [1:0]              if_size,
    
//     // cache_axi 接口
//     input   wire  [511:0]             i_cache_rw_axi_rdata,
//     input   wire                      i_cache_rw_axi_ready,
//     output  wire                      o_cache_rw_axi_valid,
//     output  wire                      o_cache_rw_axi_op,
//     output  wire  [511:0]             o_cache_rw_axi_wdata,
//     output  wire  [63:0]              o_cache_rw_axi_addr,
//     output  wire  [1:0]               o_cache_rw_axi_size,
//     output  wire  [7:0]               o_cache_rw_axi_blks
// );



// cache_core ICache(
//   .clk                        (clk                        ),
//   .rst                        (rst                        ),
// 	.i_cache_top_addr           (o_cache_addr               ),
// 	.i_cache_top_wdata          (o_cache_wdata              ),
// 	.i_cache_top_bytes          (o_cache_bytes              ),
// 	.i_cache_top_op             (o_cache_op                 ),
// 	.i_cache_top_req            (o_cache_req                ),
// 	.o_cache_top_rdata          (i_cache_rdata              ),
// 	.o_cache_top_ack            (i_cache_ack                ),

//   .i_cache_rw_axi_ready       (i_cache_rw_axi_ready       ),
//   .i_cache_rw_axi_rdata       (i_cache_rw_axi_rdata       ),
//   .o_cache_rw_axi_op          (o_cache_rw_axi_op          ),
//   .o_cache_rw_axi_valid       (o_cache_rw_axi_valid       ),
//   .o_cache_rw_axi_wdata       (o_cache_rw_axi_wdata       ),
//   .o_cache_rw_axi_addr        (o_cache_rw_axi_addr        ),
//   .o_cache_rw_axi_size        (o_cache_rw_axi_size        ),
//   .o_cache_rw_axi_blks        (o_cache_rw_axi_blks        )
// );


// endmodule
