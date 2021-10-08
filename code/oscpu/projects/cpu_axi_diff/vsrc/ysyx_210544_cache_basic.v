
// ZhengpuShi

// Cache Basic Unit
// 仅支持对齐访问的Cache基本单元

/*
  Cache Disign (2021.09.08, by ZhengpuShi):
    [-] --- BASIC CONFIG
    [*] word_size = 32bit (4 bytes)             -- 指令是32bit的
    [*] block_size = 512bit (64 bytes)          -- 块大小，AXI总线burst最大传输8次*8字节=64字节
    [*] offset index bits = 6 (2^6 = 64)        -- 由块大小决定
    [*] cache bytes max = 4KB * 2               -- ICache/DCache各4KB
    [*] main memory bytes = 4GB = 2^32          -- 主存地址空间0~(4GB-1)
    [*] raw-memory width = 128bit               -- 后端决定
    [*] raw-memory depth = 64                   -- 后端决定
    [-] --- CACHE CONFIG，4路16组
    [*] cache ways = 4way                       -- 2/4/8/...
    [*] cache blocks per way = 16blocks         -- 8/16/32/...
    [*] cache block index bits = 4 (2^4 = 16)   -- 由块数决定
    [*] cache data bytes = 4 * 16 * 64B = 4KB   -- 由路数、块数、块大小决定
    [*] bits_mem_tag = 32 - 4 - 6 = 22          -- 主存标记，由主存大小、cache块数、块大小决定
    [*] bits_v = 1 (data valid)                 -- 为1表示有效
    [*] bits_d = 1 (data dirty)                 -- 为1表示脏数据，在替换时需要写入主存
    [*] bits_s = 2 (sequence)                   -- FIFO策略：初始化各路分别为0,1,2,3；替换时换掉为0的一路；并将顺序循环移动。
    [-] --- CACHE STORAGE，分两块存储，数据与标记。 
    [*] cache_data_bits = 4 * (16 * 512) = 32Kbit = 4KB
    [*] cache_info_bits = 4 * (16 * (2 + 1 + 1 + 22)) = 1664bit = 208B 
    [*] --- ADDRESS TRANSFORM
      1. 主存地址 32bit：
        以字节为单位；共2^32个单元；低6位是块内偏移；接着4位是块号；接着22位是tag
      2. 主存数据 8/16/32/64bit
        可以有多种访问方式
      3. cache_data地址:
        每一路用1片RAM，1KB=1024bit，总共有8片，ICache/DCache各4片，以下都是单独一路的配置。
        共4路                            -- 2bit
        以128bit为1行；共64行；           -- 6bit                
        每4个单元组成512bit的一个块；       -- 2bit         
        共16个块                         -- 4bit
      3. cache_info地址：
        共4路                            -- 2bit
        每路又分16行                      -- 4bit
        每行26bit，从高位到低位，2bit顺序，1bit脏位，1bit有效位，22bit主存标记
      4. 支持不对齐访问，需要处理跨行、跨页访问
        可能产生跨行、跨页，使用更高层的调用方式，产生两次cache调用。
        1>. byte访问不会产生跨页
        2>. half访问，可能产生1字节的跨页
        3>. word访问，可能产生1~3字节的跨页
        4>. dword访问，可能产生1~7字节的跨页
        所以，在本模块内，访问地址、访问字节数一定是有效的，不做检查。
*/

`include "defines.v"

module ysyx_210544_cache_basic (
  input   wire                clk,
  input   wire                rst,

  // 常规通道
  input   wire  [`BUS_64]     i_cache_basic_addr,         // 地址。保证与操作数大小相加后不能跨界。
  input   wire  [`BUS_64]     i_cache_basic_wdata,        // 写入的数据
  input   wire  [2 : 0]       i_cache_basic_bytes,        // 操作的字节数: 0~7表示1~8字节
	input   wire                i_cache_basic_op,           // 操作: 0:read, 1:write
	input   wire                i_cache_basic_req,          // 请求
  output  reg   [`BUS_64]     o_cache_basic_rdata,        // 读出的数据
	output  reg                 o_cache_basic_ack,          // 应答

  // 同步通道
  input   wire                i_cache_basic_sync_rreq,      // 读请求，需要一直保持，收到应答后撤销。
  output  wire                o_cache_basic_sync_rack,      // 读应答，操作完毕后应答
  output  wire                o_cache_basic_sync_rpackreq,  // 读包请求，DCache发出请求
  input   wire                i_cache_basic_sync_rpackack,  // 读包应答，DCache收到应答
  output  wire  [  1: 0]      o_cache_basic_sync_rwayid,    // 读取到的路id: 0~3
  output  wire  [  3: 0]      o_cache_basic_sync_rblkid,    // 读取到的块id: 0~15
  output  wire  [ 25: 0]      o_cache_basic_sync_rinfo,     // 读取到的cache_info
  output  wire  [511: 0]      o_cache_basic_sync_rdata,     // 读取到的cache_data
  input   wire                i_cache_basic_sync_wreq,      // 写请求，ICache收到请求
  output  wire                o_cache_basic_sync_wack,      // 写应答，ICache发出应答
  input   wire  [  1: 0]      i_cache_basic_sync_wwayid,    // 要写入的路id: 0~3
  input   wire  [  3: 0]      i_cache_basic_sync_wblkid,    // 要写入的块id: 0~15
  input   wire  [ 25: 0]      i_cache_basic_sync_winfo,     // 要写入的cache_info
  input   wire  [511: 0]      i_cache_basic_sync_wdata,     // 要写入的cache_data

  // AXI interface
  input   wire  [511:0]       i_axi_io_rdata,
  input   wire                i_axi_io_ready,
  output  wire                o_axi_io_valid,
  output  wire                o_axi_io_op,
  output  wire  [511:0]       o_axi_io_wdata,
  output  wire  [63:0]        o_axi_io_addr,
  output  wire  [2:0]         o_axi_io_size,
  output  wire  [7:0]         o_axi_io_blks
);

// 根据实际硬件模型设置有效电平
parameter bit CHIP_DATA_CEN = 0;        // cen有效的电平
parameter bit CHIP_DATA_WEN = 0;        // wen有效的电平
parameter bit CHIP_DATA_WMASK_EN = 0;   // 写掩码有效的电平

// =============== 状态机 ===============
//  英文名称          中文名称               含义
//  IDLE              空闲                 无活动。有用户请求则进入 READY / STORE_FROM_RAM / LOAD_FROM_BUS 这三种情况
//  READY             就绪                  命中，则直接读写。读写完毕回到IDLE。
//  STORE_FROM_RAM    存储(从RAM读取数据)    不命中并选择脏的数据块，则需要写回。先以128bit为单位分4次从RAM读入数据，读取完毕跳转到 StoreToBUS
//  STORE_TO_BUS      存储(写入总线)         不命中并选择脏的数据块，则需要写回。再将512bit数据写入总线，写入完毕跳转到 LoadFromBUS
//  LOAD_FROM_BUS     加载(从总线读取数据)    不命中并选择不脏的数据块，则需要读入新数据。先从总线读取512bit数据，读取完毕跳转到 LoadToRAM
//  LOAD_TO_RAM       加载(写入RAM)         不命中并选择不脏的数据块，则需要读入新数据。再以128bit为单位分4次写入RAM，写入完毕跳转到READY
//  FENCE_RD          同步读               有fence请求，读取vlaid的数据，送出
//  FENCE_WR          同步写               有fence请求，收到数据包，写入。
parameter [2:0] STATE_IDLE              = 3'd0;
parameter [2:0] STATE_READY             = 3'd1;
parameter [2:0] STATE_STORE_FROM_RAM    = 3'd2;
parameter [2:0] STATE_STORE_TO_BUS      = 3'd3;
parameter [2:0] STATE_LOAD_FROM_BUS     = 3'd4;
parameter [2:0] STATE_LOAD_TO_RAM       = 3'd5;
parameter [2:0] STATE_FENCE_RD          = 3'd6;
parameter [2:0] STATE_FENCE_WR          = 3'd7;

`define WAYS                  4             // 路数
`define BLKS                  16            // 块数
`define BUS_WAYS              0:3           // 各路的总线。4路

`define c_tag_BUS             21:0          // cache的tag所在的总线 
`define c_tag_msb_BUS         21            // cache的tag最高位所在的总线，若为1则是主存地址，即：8000_0000 ~ 4GB-1 
`define c_v_BUS               22            // cache的v所在的总线 
`define c_d_BUS               23            // cache的d所在的总线 
`define c_s_BUS               25:24         // cache的s所在的总线


reg                           o_cache_axi_req;            // 请求
reg   [63 : 0]                o_cache_axi_addr;           // 存储器地址（字节为单位），64字节对齐，低6位为0。
reg                           o_cache_axi_op;             // 操作类型：0读取，1写入
reg   [511 : 0]               o_cache_axi_wdata;          // 要写入的数据
wire  [511 : 0]               i_cache_axi_rdata;          // 已读出的数据
wire                          i_cache_axi_ack;            // 应答

// =============== 同步 ===============
wire                          sync_rreq;                  // 同步操作读请求
reg                           sync_rack;                  // 同步操作读应答
reg                           sync_rpackreq;              // 同步操作读包请求
wire                          sync_rpackack;              // 同步操作读包应答
wire                          sync_wreq;                  // 同步操作写包请求
reg                           sync_wack;                  // 同步操作写包应答

reg   [1  : 0]                sync_rwayid;                // 读取到的路id: 0~3
reg   [3  : 0]                sync_rblkid;                // 读取到的块id: 0~15
reg   [25 : 0]                sync_rinfo;                 // 读到到的cache_info
reg   [511: 0]                sync_rdata;                 // 读到到的cache_data
reg                           sync_rlast;                 // 读取达到最后一个单元
wire                          sync_r_need;                // 是否需要读取的条件：cache行有效，且地址是主存的地址

wire  [1  : 0]                sync_wwayid;                // 要写入的路id: 0~3
wire  [3  : 0]                sync_wblkid;                // 要写入的块id: 0~15
wire  [25 : 0]                sync_winfo;                 // 要写入的cache_info
wire  [511: 0]                sync_wdata;                 // 要写入的cache_data

// =============== 物理地址解码 ===============
wire  [63: 0]                 user_blk_aligned_bytes;     // 用户地址的按块对齐地址(按字节)（64字节对齐，低6位为0）
reg   [63: 0]                 user_wmask;                 // 用户数据的写入掩码，由bytes决定，高电平有效
wire  [3 : 0]                 mem_blkno;                  // mem块号，0~15
wire  [5 : 0]                 mem_offset_bytes;           // mem块内偏移(按字节)，0~63
wire  [8 : 0]                 mem_offset_bits;            // mem块内偏移(按位)，0~511
wire  [21: 0]                 mem_tag;                    // mem标记

// =============== Cache Info 缓存信息 ===============
reg   [25 : 0]                cache_info[`BUS_WAYS][0:`BLKS-1];   // cache信息块
wire  [5 : 0]                 c_data_lineno;                      // cache数据行号(0~63)
wire  [3 : 0]                 c_offset_bytes;                     // cache行内偏移(按字节)(0~15)
wire  [6 : 0]                 c_offset_bits;                      // cache行内偏移(按位)(0~127)
wire  [127:0]                 c_wdata;                            // cache行要写入的数据
wire  [127:0]                 c_wmask;                            // cache行要写入的掩码

wire                          c_v[`BUS_WAYS];                     // cache valid bit 有效位，1位有效
wire                          c_d[`BUS_WAYS];                     // cache dirty bit 脏位，1为脏
wire  [1 : 0]                 c_s[`BUS_WAYS];                     // cache seqence bit 顺序位，越大越需要先被替换走
wire  [21: 0]                 c_tag[`BUS_WAYS];                   // cache标记

// =============== cache选中 ===============
wire                          hit[`BUS_WAYS];     // 各路是否命中
wire                          hit_any;            // 是否有任意一路命中？
wire [1:0]                    wayID_smin;         // s最小的是哪一路？
wire [1:0]                    wayID_hit;          // 已命中的是哪一路（至多有一路命中） 
wire [1:0]                    wayID_select;       // 选择了哪一路？方法：若命中则就是命中的那一路；否则选择smax所在的那一路

// =============== Cache Data 缓存数据 ===============

reg                           chip_data_cen[`BUS_WAYS];               // RAM 使能，低电平有效
reg                           chip_data_wen[`BUS_WAYS];               // RAM 写使能，低电平有效
reg   [5  : 0]                chip_data_addr[`BUS_WAYS];              // RAM 地址
reg   [127: 0]                chip_data_wdata[`BUS_WAYS];             // RAM 写入数据
reg   [127: 0]                chip_data_wmask[`BUS_WAYS];             // RAM 写入掩码
wire  [127: 0]                chip_data_rdata[`BUS_WAYS];             // RAM 读出数据


reg [2:0] state;
reg   [1  : 0]                sync_step;                  // sync操作的不同阶段

// =============== 处理用户请求 ===============
reg   [2:0]         ram_op_cnt;                 // RAM操作计数器(0~3表示1~4次，剩余的位数用于大于4的计数)
wire  [8:0]         ram_op_offset_128;          // RAM操作的128位偏移量（延迟2个时钟周期后输出）
wire                hs_cache;                   // cache操作 握手
wire                hs_sync_rd;                 // sync读操作 握手
wire                hs_sync_rpack;              // sync读包操作 握手
wire                hs_sync_wr;                 // sync写操作 握手
wire                hs_cache_axi;               // cache_axi操作 握手
wire                hs_ramwrite;                // ram操作 握手（完成4行写入）
wire                hs_ramread;                 // ram操作 握手（完成4行读取）
wire                hs_ramline;                 // ram操作 握手（完成指定1行读写）
reg   [127: 0]      rdata_line;                 // 读取一行数据
reg   [63: 0]       rdata_out;                  // 输出的数据



assign sync_rreq                    = i_cache_basic_sync_rreq;
assign o_cache_basic_sync_rack      = sync_rack;
assign o_cache_basic_sync_rpackreq  = sync_rpackreq;
assign sync_rpackack                = i_cache_basic_sync_rpackack;
assign sync_wreq                    = i_cache_basic_sync_wreq;
assign o_cache_basic_sync_wack      = sync_wack;

assign sync_rinfo                   = cache_info[sync_rwayid][sync_rblkid];
assign o_cache_basic_sync_rwayid    = sync_rwayid;
assign o_cache_basic_sync_rblkid    = sync_rblkid;
assign o_cache_basic_sync_rinfo     = sync_rinfo;
assign o_cache_basic_sync_rdata     = sync_rdata;

assign sync_rlast                   = !sync_rreq ? 0 : (sync_rwayid == 2'd3) && (sync_rblkid == 4'd15);
assign sync_r_need                  = sync_rinfo[`c_v_BUS] & sync_rinfo[`c_tag_msb_BUS];

assign sync_wwayid                  = i_cache_basic_sync_wwayid;
assign sync_wblkid                  = i_cache_basic_sync_wblkid;
assign sync_winfo                   = i_cache_basic_sync_winfo;
assign sync_wdata                   = i_cache_basic_sync_wdata;

// assign sync_rblkid                  = !sync_rreq ? 0 : {sync_rlineid >> 2}[3:0];
// assign sync_rtag                    = !sync_rreq ? 0 : c_tag[sync_rwayid];
// assign o_cache_basic_sync_retag     = {sync_rtag, sync_rlineid};
// assign sync_rdata                   = !sync_rreq ? 0 : rdata_line;

// assign sync_wetag                   = !sync_wreq ? 0 : i_cache_basic_sync_wetag;
// assign sync_wtag                    = !sync_wreq ? 0 : sync_wetag[27:6];
// assign sync_wlineid                 = !sync_wreq ? 0 : sync_wetag[5:0];
// assign sync_wblkid                  = !sync_wreq ? 0 : {sync_wlineid >> 2}[3:0];
// assign sync_wdata                   = !sync_wreq ? 0 : i_cache_basic_sync_wdata;

assign user_blk_aligned_bytes = {32'd0, i_cache_basic_addr[31:6], 6'd0};

always @(*) begin
  case (i_cache_basic_bytes)
    0:    user_wmask = 64'hFF;
    1:    user_wmask = 64'hFFFF;
    2:    user_wmask = 64'hFFFF_FF;
    3:    user_wmask = 64'hFFFF_FFFF;
    4:    user_wmask = 64'hFFFF_FFFF_FF;
    5:    user_wmask = 64'hFFFF_FFFF_FFFF;
    6:    user_wmask = 64'hFFFF_FFFF_FFFF_FF;
    7:    user_wmask = 64'hFFFF_FFFF_FFFF_FFFF;
    default: user_wmask = 0;
  endcase
end

assign mem_offset_bytes   = i_cache_basic_addr[5:0];
assign mem_offset_bits    = {3'b0, i_cache_basic_addr[5:0]} << 3;
assign mem_blkno          = i_cache_basic_addr[9:6];
assign mem_tag            = i_cache_basic_addr[31:10];

assign c_data_lineno    = i_cache_basic_addr[9:4];
assign c_offset_bytes   = mem_offset_bits[6:3]; 
assign c_offset_bits    = mem_offset_bits[6:0];
assign c_wmask          = {64'd0, user_wmask} << c_offset_bits;
assign c_wdata          = {64'd0, i_cache_basic_wdata} << c_offset_bits;

// cache_info
genvar way,i;
generate
  for (way = 0; way < `WAYS; way = way + 1) 
  begin: CACHE_INFO_GEN1
    localparam [1:0] w = way;
    for (i = 0; i < `BLKS; i = i + 1) 
    begin: CAHCE_INFO_GEN2
      always @(posedge clk) begin
        if (rst) begin
          cache_info[w][i] <= {w, 1'b0, 1'b0, 22'b0};
        end
      end
    end
  end
endgenerate

// c_tag, c_v, c_d, c_s
generate
  for (way = 0; way < `WAYS; way = way + 1) 
  begin: CACHE_INFO_DETAILS_GEN
    localparam [1:0] w = way;
    assign c_tag[w]   = cache_info[w][mem_blkno][`c_tag_BUS];
    assign c_v[w]     = cache_info[w][mem_blkno][`c_v_BUS];
    assign c_d[w]     = cache_info[w][mem_blkno][`c_d_BUS];
    assign c_s[w]     = cache_info[w][mem_blkno][`c_s_BUS];
  end
endgenerate

// hit
generate
  for (way = 0; way < `WAYS; way = way + 1) 
  begin: HIT_GEN
    localparam [1:0] w = way;
    assign hit[w] = c_v[w] && (c_tag[w] == mem_tag);
  end
endgenerate

assign hit_any = hit[0] | hit[1] | hit[2] | hit[3];
assign wayID_hit = (hit[1] ? 1 : 0) | (hit[2] ? 2 : 0) | (hit[3] ? 3 : 0);
assign wayID_smin = (c_s[1] == 0 ? 1 : 0) | (c_s[2] == 0 ? 2 : 0) | (c_s[3] == 0 ? 3 : 0);
assign wayID_select = hit_any ? wayID_hit : wayID_smin;

// RAM instantiate
generate
  for (way = 0; way < `WAYS; way = way + 1) 
  begin: CACHE_DATA_GEN
    localparam [1:0] w = way;
    S011HD1P_X32Y2D128_BW  chip_data(
      .CLK                        (clk                  ),
      .CEN                        (chip_data_cen[w]     ),
      .WEN                        (chip_data_wen[w]     ),
      .A                          (chip_data_addr[w]    ),
      .D                          (chip_data_wdata[w]   ),
      .BWEN                       (chip_data_wmask[w]   ),
      .Q                          (chip_data_rdata[w]   )
    );
  end
endgenerate

// cen, addr
generate
  for (way = 0; way < `WAYS; way = way + 1) 
  begin: CHIP_DATA_CEN_WEN_GEN
    localparam [1:0] w = way;
    always @(posedge clk) begin
      if (rst) begin
        chip_data_cen[w] <= !CHIP_DATA_CEN;
        chip_data_wen[w] <= !CHIP_DATA_WEN;
        chip_data_addr[w] <= 0;
        chip_data_wdata[w] <= 0;
      end
    end
  end
endgenerate

// wire state_idle             = state == STATE_IDLE;
// wire state_ready            = state == STATE_READY;
// wire state_store_from_ram   = state == STATE_STORE_FROM_RAM;
// wire state_store_to_bus     = state == STATE_STORE_TO_BUS;
// wire state_load_from_bus    = state == STATE_LOAD_FROM_BUS;
// wire state_load_to_ram      = state == STATE_LOAD_TO_RAM;

assign ram_op_offset_128 = ({6'd0, ram_op_cnt} - 2) << 7;
assign hs_cache = i_cache_basic_req & o_cache_basic_ack;
assign hs_sync_rd = sync_rreq & sync_rack;
assign hs_sync_rpack = sync_rpackack & sync_rpackreq;
assign hs_sync_wr = sync_wreq & sync_wack;
assign hs_cache_axi = o_cache_axi_req & i_cache_axi_ack;
assign hs_ramwrite = ram_op_cnt == 3'd4;
assign hs_ramread = ram_op_cnt == 3'd6;
assign hs_ramline = ram_op_cnt == 3'd3;
assign rdata_line = chip_data_rdata[wayID_select];
assign rdata_out = rdata_line[c_offset_bits +:64] & user_wmask;

always @(posedge clk) begin
    if (rst) begin
        state <= STATE_IDLE;
    end
    else begin
      case (state)
          STATE_IDLE:   begin
            if (sync_rreq) begin
              state <= STATE_FENCE_RD;
            end
            else if (sync_wreq) begin
              state <= STATE_FENCE_WR;
            end
            else if (i_cache_basic_req) begin
              if (hit_any) begin
                state <= STATE_READY;
              end
              else begin
                if (c_d[wayID_select]) begin
                  state <= STATE_STORE_FROM_RAM;
                end
                else begin
                  state <= STATE_LOAD_FROM_BUS;
                end
              end
            end
          end
          
          STATE_READY:  begin
            if (hs_cache) begin
              // 处理剩余的读写请求
              state <= STATE_IDLE;
            end
          end

          STATE_STORE_FROM_RAM:     begin
            if (hs_ramread) begin
              state <= STATE_STORE_TO_BUS;
            end
          end

          STATE_STORE_TO_BUS:     begin
            if (hs_cache_axi) begin
              state <= STATE_LOAD_FROM_BUS;
            end
          end

          STATE_LOAD_FROM_BUS: begin
            if (hs_cache_axi) begin
              state <= STATE_LOAD_TO_RAM;
            end
          end

          STATE_LOAD_TO_RAM: begin
            if (hs_ramwrite) begin
              state <= STATE_READY;
            end
          end

          STATE_FENCE_RD: begin
            if (hs_sync_rd) begin
              state <= STATE_IDLE;
            end
          end

          STATE_FENCE_WR: begin
            if (hs_sync_wr) begin
              state <= STATE_IDLE;
            end
          end

          default: ;
      endcase
    end
end

always @(posedge clk) begin
  if (rst) begin
    o_cache_basic_ack <= 0;
    sync_rpackreq <= 0;
    sync_rack <= 0;
    sync_wack <= 0;
    sync_rwayid <= 0;
    sync_rblkid <= 0;
    sync_rdata <= 0;
  end
  else begin
    case (state)
      STATE_IDLE: begin;
        o_cache_basic_ack <= 0;
        sync_rack <= 0;
        sync_rpackreq <= 0;
        sync_wack <= 0;
      end

      STATE_READY: begin
        if (!hs_cache) begin
          if (i_cache_basic_op == `REQ_READ) begin
            // 读取RAM一个单元
            if (!hs_ramline) begin
              chip_data_cen[wayID_select] <= CHIP_DATA_CEN;
              chip_data_addr[wayID_select] <= c_data_lineno;
              ram_op_cnt <= ram_op_cnt + 1;
            end
            else begin
              chip_data_cen[wayID_select] <= !CHIP_DATA_CEN;
              o_cache_basic_rdata <= rdata_out; // ToDo: 在跳转指令时，这一步可以用组合电路实现，更早得到新的数据
              o_cache_basic_ack <= 1;
            end
          end
          else begin
            // 写入RAM一个单元
            if (!hs_ramline) begin
              chip_data_cen[wayID_select] <= CHIP_DATA_CEN;
              chip_data_wen[wayID_select] <= CHIP_DATA_WEN;
              chip_data_addr[wayID_select] <= c_data_lineno;
              chip_data_wdata[wayID_select] <= c_wdata;
              chip_data_wmask[wayID_select] <= ~c_wmask;  // 芯片的写入掩码低电平有效，需要取反
              ram_op_cnt <= ram_op_cnt + 1;
            end
            else begin
              chip_data_cen[wayID_select] <= !CHIP_DATA_CEN;
              chip_data_wen[wayID_select] <= !CHIP_DATA_WEN;
              o_cache_basic_ack <= 1;
              // cache更新记录
              cache_info[wayID_select][mem_blkno][`c_d_BUS]  <= 1;
            end
          end
        end
        else begin
          ram_op_cnt <= 0;
        end
      end

      STATE_LOAD_FROM_BUS: begin
        // 读取主存一个块
        o_cache_axi_req <= 1;
        o_cache_axi_addr <= user_blk_aligned_bytes;
        o_cache_axi_op <= `REQ_READ;
        if (hs_cache_axi) begin
          o_cache_axi_req <= 0;
        end
      end

      STATE_LOAD_TO_RAM: begin
        // 写入RAM一个块
        if (!hs_ramwrite) begin
          ram_op_cnt <= ram_op_cnt + 1;
          // 写入cache数据一行
          chip_data_cen[wayID_select] <= CHIP_DATA_CEN;
          chip_data_wen[wayID_select] <= CHIP_DATA_WEN;
          chip_data_addr[wayID_select] <= {{2'd0, mem_blkno} << 2} | {4'd0, ram_op_cnt[1:0]};
          chip_data_wdata[wayID_select] <= i_cache_axi_rdata[{{7'd0,ram_op_cnt[1:0]} << 7}+:128];   // 128的倍数
          chip_data_wmask[wayID_select] <= {128{CHIP_DATA_WMASK_EN}};
        end
        else begin
          ram_op_cnt <= 0;
          chip_data_cen[wayID_select] <= !CHIP_DATA_CEN;
          chip_data_wen[wayID_select] <= !CHIP_DATA_WEN;
          // 更新cache记录一行的 tag,v,d 位
          cache_info[wayID_select][mem_blkno][`c_tag_BUS]      <= mem_tag; // c_tag
          cache_info[wayID_select][mem_blkno][`c_v_BUS]        <= 1;       // 有效位
          cache_info[wayID_select][mem_blkno][`c_d_BUS]        <= 0;       // 脏位
          // 更新cache记录四行的 s 位，循环移动
          cache_info[3][mem_blkno][`c_s_BUS] <= cache_info[2][mem_blkno][`c_s_BUS];
          cache_info[2][mem_blkno][`c_s_BUS] <= cache_info[1][mem_blkno][`c_s_BUS];
          cache_info[1][mem_blkno][`c_s_BUS] <= cache_info[0][mem_blkno][`c_s_BUS];
          cache_info[0][mem_blkno][`c_s_BUS] <= cache_info[3][mem_blkno][`c_s_BUS];
        end
      end

      STATE_STORE_FROM_RAM: begin
        // 读取RAM一个块
        if (!hs_ramread) begin
          ram_op_cnt <= ram_op_cnt + 1;
          // RAM控制信号在前4个周期有效
          if (ram_op_cnt <= 3) begin
            chip_data_cen[wayID_select] <= CHIP_DATA_CEN;
            chip_data_addr[wayID_select] <= {{2'd0, mem_blkno} << 2} | {4'd0, ram_op_cnt[1:0]};
          end
          // 延迟2个周期后保存RAM读出的数据
          if (ram_op_cnt >= 2) begin
            o_cache_axi_wdata[ram_op_offset_128+:128] <= chip_data_rdata[wayID_select];   // 128的倍数
          end
        end
        else begin
          ram_op_cnt <= 0;
          chip_data_cen[wayID_select] <= !CHIP_DATA_CEN;
          // 更新cache记录一行的 d 位。
          cache_info[wayID_select][mem_blkno][`c_d_BUS]        <= 0;       // 脏位
        end
      end

      STATE_STORE_TO_BUS: begin
        // 写入主存一个块
        o_cache_axi_req <= 1;
        o_cache_axi_addr <= {32'd0, c_tag[wayID_select], mem_blkno, 6'd0 };
        o_cache_axi_op <= `REQ_WRITE;

        if (hs_cache_axi) begin
          o_cache_axi_wdata <= 0;
          o_cache_axi_req <= 0;
        end
      end

      STATE_FENCE_RD: begin
        if (!hs_sync_rd) begin
          // step0: 找到一个空位置
          if (sync_step == 0) begin
            // 若是主存地址，且存在，则开始搬运数据
            if (sync_r_need) begin
              sync_step <= 1;
            end
            // 若不命中则移动指针，或者完成任务
            else begin
              if (!sync_rlast) begin
                sync_rblkid <= sync_rblkid + 1;
                if (sync_rblkid == 4'd15) begin
                  sync_rblkid <= 0;
                  sync_rwayid <= sync_rwayid + 1;
                end
              end
              else begin
                sync_step <= 3;
              end
            end
          end
          // step1: 读取数据
          else if (sync_step == 1) begin
            // 读取RAM一个块
            if (!hs_ramread) begin
              ram_op_cnt <= ram_op_cnt + 1;
              // RAM控制信号在前4个周期有效
              if (ram_op_cnt <= 3) begin
                chip_data_cen[sync_rwayid]  <= CHIP_DATA_CEN;
                chip_data_addr[sync_rwayid] <= {{2'd0, sync_rblkid} << 2} | {4'd0, ram_op_cnt[1:0]};
              end
              // 延迟2个周期后保存RAM读出的数据
              if (ram_op_cnt >= 2) begin
                sync_rdata[ram_op_offset_128+:128] <= chip_data_rdata[sync_rwayid];   // 128的倍数
              end
            end
            else begin
              ram_op_cnt <= 0;
              chip_data_cen[sync_rwayid] <= !CHIP_DATA_CEN;
              sync_rpackreq <= 1;
              sync_step <= 2;
            end
          end
          // step2: 等待数据包应答
          else if (sync_step == 2) begin
            if (hs_sync_rpack) begin
              sync_rpackreq <= 0; // 撤销请求
              // 若不是最后一包，则移动指针继续工作，否则完成任务
              if (!sync_rlast) begin
                sync_rblkid <= sync_rblkid + 1;
                if (sync_rblkid == 4'd15) begin
                  sync_rblkid <= 0;
                  sync_rwayid <= sync_rwayid + 1;
                end
                sync_step <= 0;
              end
              else begin
                sync_step <= 3;
              end
            end
          end
          // step3: 完成任务
          else if (sync_step == 3) begin
            if (!hs_sync_rd) begin
              sync_rack <= 1;
            end
            else begin
              // 清零所有信号
              sync_step <= 0;
              sync_rack <= 0;
              sync_rblkid <= 0;
              sync_rwayid <= 0;
            end
          end
        end
      end

      STATE_FENCE_WR: begin
        if (!hs_sync_wr) begin

          // 写入RAM一个块
          if (!hs_ramwrite) begin
            ram_op_cnt <= ram_op_cnt + 1;
            // 写入cache数据一行
            chip_data_cen[sync_wwayid] <= CHIP_DATA_CEN;
            chip_data_wen[sync_wwayid] <= CHIP_DATA_WEN;
            chip_data_addr[sync_wwayid] <= {{2'd0, sync_wblkid} << 2} | {4'd0, ram_op_cnt[1:0]};
            chip_data_wdata[sync_wwayid] <= sync_wdata[{{7'd0,ram_op_cnt[1:0]} << 7}+:128];   // 128的倍数
            chip_data_wmask[sync_wwayid] <= {128{CHIP_DATA_WMASK_EN}};
          end
          else begin
            ram_op_cnt <= 0;
            chip_data_cen[sync_wwayid] <= !CHIP_DATA_CEN;
            chip_data_wen[sync_wwayid] <= !CHIP_DATA_WEN;
            // 更新cache记录一行，并强行置位dirty位，保证在调换时能被写入主存
            // 这里cache s位是否需要考虑？如果是DCache全部搬运，则不需要考虑。如果是搬运v=1的块，则要考虑吧
            cache_info[sync_wwayid][sync_wblkid] <= sync_winfo | (1 << `c_d_BUS);

            sync_wack <= 1;
          end
        end
      end

      default:;
    endcase
  end
end

// =============== cache_axi 从机端，请求传输数据 ===============

ysyx_210544_cache_axi Cache_axi(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_axi_req            (o_cache_axi_req            ),
	.i_cache_axi_addr           (o_cache_axi_addr           ),
	.i_cache_axi_op             (o_cache_axi_op             ),
	.i_cache_axi_wdata          (o_cache_axi_wdata          ),
	.o_cache_axi_rdata          (i_cache_axi_rdata          ),
	.o_cache_axi_ack            (i_cache_axi_ack            ),

  .i_axi_io_ready             (i_axi_io_ready             ),
  .i_axi_io_rdata             (i_axi_io_rdata             ),
  .o_axi_io_op                (o_axi_io_op                ),
  .o_axi_io_valid             (o_axi_io_valid             ),
  .o_axi_io_wdata             (o_axi_io_wdata             ),
  .o_axi_io_addr              (o_axi_io_addr              ),
  .o_axi_io_size              (o_axi_io_size              ),
  .o_axi_io_blks              (o_axi_io_blks              )
);

wire _unused_ok = &{1'b0,
  i_cache_basic_addr[63:32],
  mem_offset_bytes,
  mem_offset_bits[8:7],
  c_offset_bytes,
  1'b0};

endmodule
