
// ZhengpuShi

// Cache Interface
// 对ICache和DCache的统一

`include "defines.v"

module ysyx_210544_cache(
    input                     clk,
    input                     rst,
    
    // fence.i。同步通道，在Exe_stage执行
    input   wire              i_fencei_req,
    output  wire              o_fencei_ack,
    
    // ICache。取指通道
    input   wire              i_icache_req,
    input   wire  [63:0]      i_icache_addr,
    output  wire              o_icache_ack,
    output  wire  [31:0]      o_icache_rdata,

    // DCache。访存通道
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
wire              iaddr_FLASH;
wire              iaddr_MEM;
wire              daddr_PERI;
wire              daddr_FLASH;
wire              daddr_MEM;
wire              ch_icache;
wire              ch_dcache;
wire              ch_nocache;

// Instruction Cache
wire  [63:0]      icache_rdata;
wire              icache_ack;
wire              icache_axi_io_valid;
wire              icache_axi_io_op;
wire  [511:0]     icache_axi_io_wdata;
wire  [63:0]      icache_axi_io_addr;
wire  [2:0]       icache_axi_io_size;
wire  [7:0]       icache_axi_io_blks;

// Data Cache
wire [63:0]       dcache_rdata;
wire              dcache_ack;
wire              dcache_axi_io_valid;
wire              dcache_axi_io_op;
wire  [511:0]     dcache_axi_io_wdata;
wire  [63:0]      dcache_axi_io_addr;
wire  [2:0]       dcache_axi_io_size;
wire  [7:0]       dcache_axi_io_blks;

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

// Cache_sync, ICache and DCache auto exchange data
wire              sync_dcache_rreq;
wire              sync_dcache_rack;
wire              sync_dcache_rpackreq;
wire              sync_dcache_rpackack;
wire              sync_dcache_wack;
wire  [  1: 0]    sync_dcache_rwayid;
wire  [  3: 0]    sync_dcache_rblkid;
wire  [ 25:0]     sync_dcache_rinfo;
wire  [511:0]     sync_dcache_rdata;

wire              sync_icache_rack;
wire              sync_icache_rpackreq;
wire              sync_icache_wreq;
wire              sync_icache_wack;
wire  [  1: 0]    sync_icache_rwayid;
wire  [  3: 0]    sync_icache_rblkid;
wire  [ 25:0]     sync_icache_rinfo;
wire  [511:0]     sync_icache_rdata;
wire  [  1: 0]    sync_icache_wwayid;
wire  [  3: 0]    sync_icache_wblkid;
wire  [ 25:0]     sync_icache_winfo;
wire  [511:0]     sync_icache_wdata;



// 0x1000_0000 ~ 0x2FFF_FFFF, 是UART/SPI等外设
// 0x3000_0000 ~ 0x3FFF_FFFF, 是Flash
// 0x8000_0000 ~ 0xFFFF_FFFF, 是主存
assign iaddr_FLASH  = i_icache_req && (i_icache_addr[31:28] == 4'h3);
assign iaddr_MEM    = i_icache_req && (i_icache_addr[31] == 1'b1);

assign daddr_PERI   = i_dcache_req && ((i_dcache_addr[31:28] == 4'h1) || (i_dcache_addr[31:28] == 4'h2));
assign daddr_FLASH  = i_dcache_req && (i_dcache_addr[31:28] == 4'h3);
assign daddr_MEM    = i_dcache_req && (i_dcache_addr[31] == 1'b1);

// 注意： FLASH可选的使用Cache或不使用Cache，Cache已做适配。
assign ch_icache    = iaddr_MEM | iaddr_FLASH;
assign ch_dcache    = daddr_MEM | daddr_FLASH;
assign ch_nocache   = daddr_PERI | daddr_PERI;// | iaddr_FLASH | daddr_FLASH;

ysyx_210544_cache_core ICache(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_cache_core_addr          (i_icache_addr              ),
  .i_cache_core_wdata         (64'd0                      ),
  .i_cache_core_bytes         (3'd3                       ),
  .i_cache_core_op            (`YSYX210544_REQ_READ                  ),
  .i_cache_core_req           (ch_icache ? i_icache_req : 1'b0),
  .o_cache_core_rdata         (icache_rdata               ),
  .o_cache_core_ack           (icache_ack                 ),


  .i_cache_core_sync_rreq     (1'b0                       ),
  .o_cache_core_sync_rack     (sync_icache_rack           ),
  .i_cache_core_sync_rpackack (1'b0                       ),
  .o_cache_core_sync_rpackreq (sync_icache_rpackreq       ),
  .i_cache_core_sync_wreq     (sync_icache_wreq           ),
  .o_cache_core_sync_wack     (sync_icache_wack           ),
  .o_cache_core_sync_rwayid   (sync_icache_rwayid         ),
  .o_cache_core_sync_rblkid   (sync_icache_rblkid         ),
  .o_cache_core_sync_rinfo    (sync_icache_rinfo          ),
  .o_cache_core_sync_rdata    (sync_icache_rdata          ),
  .i_cache_core_sync_wwayid   (sync_icache_wwayid         ),
  .i_cache_core_sync_wblkid   (sync_icache_wblkid         ),
  .i_cache_core_sync_winfo    (sync_icache_winfo          ),
  .i_cache_core_sync_wdata    (sync_icache_wdata          ),

  .i_axi_io_ready             (ch_icache ? i_axi_io_ready : 1'b0 ),
  .i_axi_io_rdata             (ch_icache ? i_axi_io_rdata : 512'd0 ),
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
  .i_cache_core_req           (ch_dcache ? i_dcache_req : 1'b0),
  .o_cache_core_rdata         (dcache_rdata               ),
  .o_cache_core_ack           (dcache_ack                 ),

  .i_cache_core_sync_rreq     (sync_dcache_rreq           ),
  .o_cache_core_sync_rack     (sync_dcache_rack           ),
  .i_cache_core_sync_rpackack (sync_dcache_rpackack       ),
  .o_cache_core_sync_rpackreq (sync_dcache_rpackreq       ),
  .i_cache_core_sync_wreq     (1'b0                       ),
  .o_cache_core_sync_wack     (sync_dcache_wack           ),
  .o_cache_core_sync_rwayid   (sync_dcache_rwayid         ),
  .o_cache_core_sync_rblkid   (sync_dcache_rblkid         ),
  .o_cache_core_sync_rinfo    (sync_dcache_rinfo          ),
  .o_cache_core_sync_rdata    (sync_dcache_rdata          ),
  .i_cache_core_sync_wwayid   (2'd0                       ),
  .i_cache_core_sync_wblkid   (4'd0                       ),
  .i_cache_core_sync_winfo    (26'd0                      ),
  .i_cache_core_sync_wdata    (512'd0                     ),

  .i_axi_io_ready             (ch_dcache ? i_axi_io_ready : 1'b0),
  .i_axi_io_rdata             (ch_dcache ? i_axi_io_rdata : 512'd0),
  .o_axi_io_op                (dcache_axi_io_op           ),
  .o_axi_io_valid             (dcache_axi_io_valid        ),
  .o_axi_io_wdata             (dcache_axi_io_wdata        ),
  .o_axi_io_addr              (dcache_axi_io_addr         ),
  .o_axi_io_size              (dcache_axi_io_size         ),
  .o_axi_io_blks              (dcache_axi_io_blks         )
);

ysyx_210544_cache_nocache NoCache(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_cache_nocache_addr       (nocache_addr               ),
  .i_cache_nocache_wdata      (nocache_wdata              ),
  .i_cache_nocache_bytes      (nocache_bytes              ),
  .i_cache_nocache_op         (nocache_op                 ),
  .i_cache_nocache_req        (ch_nocache ? nocache_req : 1'b0),
  .o_cache_nocache_rdata      (nocache_rdata              ),
  .o_cache_nocache_ack        (nocache_ack                ),

  .i_axi_io_ready             (ch_nocache ? i_axi_io_ready : 1'b0        ),
  .i_axi_io_rdata             (ch_nocache ? i_axi_io_rdata : 512'd0      ),
  .o_axi_io_op                (nocache_axi_io_op          ),
  .o_axi_io_valid             (nocache_axi_io_valid       ),
  .o_axi_io_wdata             (nocache_axi_io_wdata       ),
  .o_axi_io_addr              (nocache_axi_io_addr        ),
  .o_axi_io_size              (nocache_axi_io_size        ),
  .o_axi_io_blks              (nocache_axi_io_blks        )
);

ysyx_210544_cache_sync Cache_sync(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_fencei_req               (i_fencei_req               ),
  .o_fencei_ack               (o_fencei_ack               ),
  .o_sync_dcache_rreq         (sync_dcache_rreq           ),
  .i_sync_dcache_rack         (sync_dcache_rack           ),
  .o_sync_dcache_rpackack     (sync_dcache_rpackack       ),
  .i_sync_dcache_rpackreq     (sync_dcache_rpackreq       ),
  .i_sync_dcache_rwayid       (sync_dcache_rwayid         ),
  .i_sync_dcache_rblkid       (sync_dcache_rblkid         ),
  .i_sync_dcache_rinfo        (sync_dcache_rinfo          ),
  .i_sync_dcache_rdata        (sync_dcache_rdata          ),
  .o_sync_icache_wreq         (sync_icache_wreq           ),
  .i_sync_icache_wack         (sync_icache_wack           ),
  .o_sync_icache_wwayid       (sync_icache_wwayid         ),
  .o_sync_icache_wblkid       (sync_icache_wblkid         ),
  .o_sync_icache_winfo        (sync_icache_winfo          ),
  .o_sync_icache_wdata        (sync_icache_wdata          )
);


/////////////////////////////////////////////////
// 信号互联

assign nocache_req      = ch_nocache ? (i_icache_req | i_dcache_req                     ) : 1'b0;
assign nocache_addr     = ch_nocache ? (i_icache_req ? i_icache_addr  : i_dcache_addr   ) : 64'd0;
assign nocache_wdata    = ch_nocache ? (i_icache_req ? 64'd0          : i_dcache_wdata  ) : 64'd0;
assign nocache_bytes    = ch_nocache ? (i_icache_req ? 3'd3           : i_dcache_bytes  ) : 3'd0;
assign nocache_op       = ch_nocache ? (i_icache_req ? `YSYX210544_REQ_READ      : i_dcache_op     ) : `YSYX210544_REQ_READ;

assign o_axi_io_valid   =                   ch_icache ? icache_axi_io_valid   : (ch_dcache ? dcache_axi_io_valid  : nocache_axi_io_valid);
assign o_axi_io_op      = o_axi_io_valid ? (ch_icache ? icache_axi_io_op      : (ch_dcache ? dcache_axi_io_op     : nocache_axi_io_op   )) : 0;
assign o_axi_io_wdata   = o_axi_io_valid ? (ch_icache ? icache_axi_io_wdata   : (ch_dcache ? dcache_axi_io_wdata  : nocache_axi_io_wdata)) : 0;
assign o_axi_io_addr    = o_axi_io_valid ? (ch_icache ? icache_axi_io_addr    : (ch_dcache ? dcache_axi_io_addr   : nocache_axi_io_addr )) : 0;
assign o_axi_io_size    = o_axi_io_valid ? (ch_icache ? icache_axi_io_size    : (ch_dcache ? dcache_axi_io_size   : nocache_axi_io_size )) : 0;
assign o_axi_io_blks    = o_axi_io_valid ? (ch_icache ? icache_axi_io_blks    : (ch_dcache ? dcache_axi_io_blks   : nocache_axi_io_blks )) : 0;

assign o_icache_rdata   = ch_icache ? icache_rdata[31:0] : nocache_rdata[31:0];
assign o_icache_ack     = ch_icache ? icache_ack         : nocache_ack        ;

assign o_dcache_rdata   = ch_dcache ? dcache_rdata       : nocache_rdata      ;
assign o_dcache_ack     = ch_dcache ? dcache_ack         : nocache_ack        ;


//wire _unused_ok = &{1'b0,
//  icache_rdata[63:32],
//  sync_dcache_wack,
//  sync_icache_rack,
//  sync_icache_rwayid,
//  sync_icache_rblkid,
//  sync_icache_rinfo,
//  sync_icache_rdata,
//  sync_icache_rpackreq,
//  1'b0};

endmodule
