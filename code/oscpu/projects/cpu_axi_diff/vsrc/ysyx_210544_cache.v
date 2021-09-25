
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

    // AXI interface
    input   wire  [511:0]     i_axi_io_rdata,
    input   wire              i_axi_io_ready,
    output  wire              o_axi_io_valid,
    output  wire              o_axi_io_op,
    output  wire  [511:0]     o_axi_io_wdata,
    output  wire  [63:0]      o_axi_io_addr,
    output  wire  [2:0]       o_axi_io_size,
    output  wire  [7:0]       o_axi_io_blks
);

/////////////////////////////////////////////////
// 数据通路选择

// 0x1000_0000 ~ END, 是UART
// 0x3000_0000 ~ END, 是Flash
// 0x8000_0000 ~ END, 是主存
wire iaddr_UART   = i_icache_addr[31:28] == 4'h1;
wire iaddr_FLASH  = i_icache_addr[31:28] == 4'h3;
wire iaddr_MEM    = i_icache_addr[31:28] == 4'h8;

wire daddr_UART   = i_dcache_addr[31:28] == 4'h1;
wire daddr_FLASH  = i_dcache_addr[31:28] == 4'h3;
wire daddr_MEM    = i_dcache_addr[31:28] == 4'h8;

wire addr_UART    = iaddr_UART  | daddr_UART;
wire addr_FLASH   = iaddr_FLASH | daddr_FLASH;
wire addr_MEM     = iaddr_MEM   | daddr_MEM;

wire ch_icache    = addr_MEM & i_icache_req;
wire ch_dcache    = addr_MEM & i_dcache_req;
// 注意： FLASH可选的使用Cache或不使用Cache，Cache已做适配。
wire ch_nocache   = (i_icache_req | i_dcache_req) &
  (addr_UART | addr_FLASH);


/////////////////////////////////////////////////
// Instruction Cache

wire  [63:0]      icache_rdata;
wire              icache_ack;
wire              icache_axi_io_valid;
wire              icache_axi_io_op;
wire  [511:0]     icache_axi_io_wdata;
wire  [63:0]      icache_axi_io_addr;
wire  [2:0]       icache_axi_io_size;
wire  [7:0]       icache_axi_io_blks;

ysyx_210544_cache_core ICache(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_core_addr          (i_icache_addr              ),
	.i_cache_core_wdata         (0                          ),
	.i_cache_core_bytes         (3                          ),
	.i_cache_core_op            (`REQ_READ                  ),
	.i_cache_core_req           (i_icache_req               ),
	.o_cache_core_rdata         (icache_rdata               ),
	.o_cache_core_ack           (icache_ack                 ),

  .i_axi_io_ready             (ch_icache ? i_axi_io_ready : 0        ),
  .i_axi_io_rdata             (ch_icache ? i_axi_io_rdata : 0        ),
  .o_axi_io_op                (icache_axi_io_op           ),
  .o_axi_io_valid             (icache_axi_io_valid        ),
  .o_axi_io_wdata             (icache_axi_io_wdata        ),
  .o_axi_io_addr              (icache_axi_io_addr         ),
  .o_axi_io_size              (icache_axi_io_size         ),
  .o_axi_io_blks              (icache_axi_io_blks         )
);


/////////////////////////////////////////////////
// Data Cache

wire [63:0]       dcache_rdata;
wire              dcache_ack;
wire              dcache_axi_io_valid;
wire              dcache_axi_io_op;
wire  [511:0]     dcache_axi_io_wdata;
wire  [63:0]      dcache_axi_io_addr;
wire  [2:0]       dcache_axi_io_size;
wire  [7:0]       dcache_axi_io_blks;

ysyx_210544_cache_core DCache(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_core_addr          (i_dcache_addr              ),
	.i_cache_core_wdata         (i_dcache_wdata             ),
	.i_cache_core_bytes         (i_dcache_bytes             ),
	.i_cache_core_op            (i_dcache_op                ),
	.i_cache_core_req           (i_dcache_req               ),
	.o_cache_core_rdata         (dcache_rdata               ),
	.o_cache_core_ack           (dcache_ack                 ),

  .i_axi_io_ready             (ch_dcache ? i_axi_io_ready : 0        ),
  .i_axi_io_rdata             (ch_dcache ? i_axi_io_rdata : 0        ),
  .o_axi_io_op                (dcache_axi_io_op           ),
  .o_axi_io_valid             (dcache_axi_io_valid        ),
  .o_axi_io_wdata             (dcache_axi_io_wdata        ),
  .o_axi_io_addr              (dcache_axi_io_addr         ),
  .o_axi_io_size              (dcache_axi_io_size         ),
  .o_axi_io_blks              (dcache_axi_io_blks         )
);


/////////////////////////////////////////////////
// NoCache, access bus directly
  
wire              nocache_req;
wire  [63:0]      nocache_addr;
wire              nocache_op;
wire  [2 :0]      nocache_bytes;
wire  [63:0]      nocache_wdata;
wire              nocache_ack;
wire  [63:0]      nocache_rdata;

wire              nocache_axi_io_valid;
wire              nocache_axi_io_op;
wire  [511:0]     nocache_axi_io_wdata;
wire  [63:0]      nocache_axi_io_addr;
wire  [2:0]       nocache_axi_io_size;
wire  [7:0]       nocache_axi_io_blks;

ysyx_210544_cache_nocache NoCache(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_nocache_addr       (nocache_addr               ),
	.i_cache_nocache_wdata      (nocache_wdata              ),
	.i_cache_nocache_bytes      (nocache_bytes              ),
	.i_cache_nocache_op         (nocache_op                 ),
	.i_cache_nocache_req        (nocache_req                ),
	.o_cache_nocache_rdata      (nocache_rdata              ),
	.o_cache_nocache_ack        (nocache_ack                ),

  .i_axi_io_ready             (ch_nocache ? i_axi_io_ready : 0        ),
  .i_axi_io_rdata             (ch_nocache ? i_axi_io_rdata : 0        ),
  .o_axi_io_op                (nocache_axi_io_op          ),
  .o_axi_io_valid             (nocache_axi_io_valid       ),
  .o_axi_io_wdata             (nocache_axi_io_wdata       ),
  .o_axi_io_addr              (nocache_axi_io_addr        ),
  .o_axi_io_size              (nocache_axi_io_size        ),
  .o_axi_io_blks              (nocache_axi_io_blks        )
);



/////////////////////////////////////////////////
// 信号互联

assign nocache_req      = ch_nocache ? (i_icache_req | i_dcache_req                     ) : 0;
assign nocache_addr     = ch_nocache ? (i_icache_req ? i_icache_addr  : i_dcache_addr   ) : 0;
assign nocache_wdata    = ch_nocache ? (i_icache_req ? 0              : i_dcache_wdata  ) : 0;
assign nocache_bytes    = ch_nocache ? (i_icache_req ? 3              : i_dcache_bytes  ) : 0;
assign nocache_op       = ch_nocache ? (i_icache_req ? `REQ_READ      : i_dcache_op     ) : 0;

assign o_axi_io_valid   = ch_icache ? icache_axi_io_valid   : (ch_dcache ? dcache_axi_io_valid  : nocache_axi_io_valid);
assign o_axi_io_op      = ch_icache ? icache_axi_io_op      : (ch_dcache ? dcache_axi_io_op     : nocache_axi_io_op);
assign o_axi_io_wdata   = ch_icache ? icache_axi_io_wdata   : (ch_dcache ? dcache_axi_io_wdata  : nocache_axi_io_wdata);
assign o_axi_io_addr    = ch_icache ? icache_axi_io_addr    : (ch_dcache ? dcache_axi_io_addr   : nocache_axi_io_addr);
assign o_axi_io_size    = ch_icache ? icache_axi_io_size    : (ch_dcache ? dcache_axi_io_size   : nocache_axi_io_size);
assign o_axi_io_blks    = ch_icache ? icache_axi_io_blks    : (ch_dcache ? dcache_axi_io_blks   : nocache_axi_io_blks);

assign o_icache_rdata   = ch_icache ? icache_rdata[31:0] : nocache_rdata[31:0];
assign o_icache_ack     = ch_icache ? icache_ack         : nocache_ack        ;

assign o_dcache_rdata   = ch_dcache ? dcache_rdata       : nocache_rdata      ;
assign o_dcache_ack     = ch_dcache ? dcache_ack         : nocache_ack        ;

wire _unused_ok = &{1'b0,
  icache_rdata[63:32],
  1'b0};

endmodule
