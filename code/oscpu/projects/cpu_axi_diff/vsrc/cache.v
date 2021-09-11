
// ZhengpuShi

// Cache Unit

/*
  Cache Disign (2021.09.08, by ZhengpuShi):
    [-] --- BASIC CONFIG
    [*] word_size = 32bit (4 bytes)             -- 指令是32bit的
    [*] block_size = 512bit (64 bytes)          -- 块大小，AXI总线burst最大传输8次*8字节=64字节
    [*] offset index bits = 6 (2^6 = 64)        -- 由块大小决定
    [*] cache bytes max = 4096 bytes            -- 后端资源决定
    [*] main memory bytes = 2GB = 2^31          -- 主存地址空间2GB
    [*] raw-memory width = 128bit               -- 后端决定
    [*] raw-memory depth = 64                   -- 后端决定
    [-] --- CACHE CONFIG，2路16组
    [*] cache ways = 2way                       -- 2/4/8/...
    [*] cache blocks per way = 16blocks         -- 8/16/32/...
    [*] cache block index bits = 4 (2^4 = 16)   -- 由块数决定
    [*] cache data bytes = 2 * 16 * 64B = 2KB   -- 由路数、块数、块大小决定
    [*] bits_mem_tag = 31 - 4 - 6 = 21          -- 主存标记，由主存大小、cache块数、块大小决定
    [*] bits_v = 1 (data valid)                 -- 为1表示有效
    [*] bits_d = 1 (data dirty)                 -- 为1表示脏数据，在替换时需要写入主存
    [*] bits_s = 1 (sequence)                   -- FIFO策略：初始化两路分别为0,1；替换时换掉为0的一路；并将所有s翻转。
    [*] bits_align = 8 (aligned to 32bit)       -- 为了
    [-] --- CACHE STORAGE，分两块存储，数据与标记。 
    [*] cache_data_bits = 2 * (16 * 512) = 16Kbit = 2KB
    [*] cache_info_bits = 2 * (16 * (8 + 1 + 1 + 1 + 21)) = 1024bit = 128B 
    [*] --- ADDRESS TRANSFORM
      1. 主存地址 32bit：
        以字节为单位；共2^31个单元；只保留低31位；低6位是块内偏移；接着4位是块号；接着21位是tag
      2. 主存数据 8/16/32/64bit
        可以有多种访问方式
      3. cache_data地址 7bit：
        以128bit为单位；共128个单元（块）；       -- 6bit                
        每4个单元组成512bit的一个块；             -- 2bit         
        共16个块                               -- 4bit
        共两路，way0，way1；                    -- 1bit
      3. cache_info地址 4bit：
        分2片来存储2路信息；每片内，以32bit为单位，共16个单元；
        每32bit从高位到低位，8bit保留，1bit顺序，1bit脏位，1bit有效位，21bit主存标记
      4. 跨页访问
        可能产生的跨页，需要处理第二块cache区域
        1. byte访问不会产生跨页
        2. half访问，可能产生1字节的跨页
        3. word访问，可能产生1~3字节的跨页
        4. dword访问，可能产生1~7字节的跨页
*/

`include "defines.v"

module cache (
  input   wire                clk,
  input   wire                rst,
  input   wire  [`BUS_64]     i_cache_addr,               // 地址
  input   reg   [`BUS_64]     i_cache_wdata,              // 写入的数据
  input   reg   [1 : 0]       i_cache_size,               // 操作数大小: 00:byte, 01:half, 10:word, 11:dword
	input                       i_cache_op,                 // 操作: 0:read, 1:write
	input                       i_cache_req,                // 请求
  output  reg   [`BUS_64]     o_cache_rdata,              // 读出的数据
	output                      o_cache_ack,                // 应答

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

// =============== cache_rw 从机端，请求传输数据 ===============

reg                           o_cache_rw_req;             // 请求
reg   [63 : 0]                o_cache_rw_addr;            // 存储器地址（字节为单位），64字节对齐，低6位为0。
reg                           o_cache_rw_op;              // 操作类型：0读取，1写入
reg   [511 : 0]               o_cache_rw_wdata;           // 要写入的数据
wire  [511 : 0]               i_cache_rw_rdata;           // 已读出的数据
wire                          i_cache_rw_ack;             // 应答

cache_rw Cache_rw(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_rw_req             (o_cache_rw_req             ),
	.i_cache_rw_addr            (o_cache_rw_addr            ),
	.i_cache_rw_op              (o_cache_rw_op              ),
	.i_cache_rw_wdata           (o_cache_rw_wdata           ),
	.o_cache_rw_rdata           (i_cache_rw_rdata           ),
	.o_cache_rw_ack             (i_cache_rw_ack             ),

  .i_cache_rw_axi_ready       (i_cache_rw_axi_ready       ),
  .i_cache_rw_axi_rdata       (i_cache_rw_axi_rdata       ),
  .o_cache_rw_axi_op          (o_cache_rw_axi_op          ),
  .o_cache_rw_axi_valid       (o_cache_rw_axi_valid       ),
  .o_cache_rw_axi_wdata       (o_cache_rw_axi_wdata       ),
  .o_cache_rw_axi_addr        (o_cache_rw_axi_addr        ),
  .o_cache_rw_axi_size        (o_cache_rw_axi_size        ),
  .o_cache_rw_axi_blks        (o_cache_rw_axi_blks        )
);


// =============== 物理地址解码 ===============

wire  [63: 0]                 addr_no_offset;             // 输入地址（字节，64字节对齐）
wire  [63: 0]                 mem_addr;                   // mem相对地址，减去0x8000_0000
wire  [3 : 0]                 mem_blkno;                  // mem块号，0~15
wire  [5 : 0]                 mem_offset_bytes;           // mem字节偏移量，0~63
wire  [8 : 0]                 mem_offset_bits;            // mem位偏移量，0~511
wire  [20: 0]                 mem_tag;                    // mem标记，21位

assign addr_no_offset = {33'd0, i_cache_addr[30:6], 6'd0};
assign mem_addr = {33'd0, i_cache_addr[30:0]};
assign mem_offset_bytes = mem_addr[5:0];
assign mem_offset_bits = {3'b0, mem_addr[5:0]} << 3;
assign mem_blkno = mem_addr[9:6];
assign mem_tag = mem_addr[30:10];


// =============== Cache Info 缓存信息 ===============

reg   [63 : 0]                cache_info_old [0:15];          // 即将弃用
reg   [31 : 0]                cache_info [0:1][0:15];         // 第0路 缓存信息
// reg   [31 : 0]                cache_info0 [0:15];         // 第0路 缓存信息
// reg   [31 : 0]                cache_info1 [0:15];         // 第1路 缓存信息
wire  [5 : 0]                 cline_no;                   // cache行号(0~15)
wire  [6 : 0]                 cline_offset_bits;          // cache行内偏移量bit(0~127)
wire  [5 : 0]                 tag_pos;                    // tag位置(0~31)
wire  [5 : 0]                 v_pos;                      // v位置(0~31)
wire  [5 : 0]                 d_pos;                      // d位置(0~31)
wire  [5 : 0]                 s_pos;                      // s位置(0~31)
wire  [20: 0]                 tag[0:1];                   // tag 内容
wire                          v[0:1];                     // valid bit 内容
wire                          d[0:1];                     // dirty bit 内容
wire                          s[0:1];                     // seqence bit 内容

// cache_info初始化
generate
  for (genvar i = 0; i < 16; i += 1) begin
    always @(posedge clk) begin
      if (rst) begin
        assign cache_info[0][i] = 32'h00000000;   // s0=0
        assign cache_info[1][i] = 32'h00800000;   // s1=1
      end
    end
  end
endgenerate

assign cline_no = {2'b0, mem_blkno} << 2;
assign cline_offset_bits = mem_offset_bits[6:0];
assign tag_pos = 0;
assign v_pos = 21;
assign d_pos = 22;
assign s_pos = 23;
assign tag[0]   = cache_info[0][mem_blkno][20:0];
assign v[0]     = cache_info[0][mem_blkno][21];
assign d[0]     = cache_info[0][mem_blkno][22];
assign s[0]     = cache_info[0][mem_blkno][23];
assign tag[1]   = cache_info[1][mem_blkno][20:0];
assign v[1]     = cache_info[1][mem_blkno][21];
assign d[1]     = cache_info[1][mem_blkno][22];
assign s[1]     = cache_info[1][mem_blkno][23];


// =============== 命中判定 ===============

wire                          hit[0:1];           // 各路是否命中
wire                          hit_any;            // 是否有任意一路命中？
reg                           hit_wayID;          // 命中了哪一路？

assign hit[0] = v[0] && (tag[0] == mem_tag);
assign hit[1] = v[1] && (tag[1] == mem_tag);
assign hit_any = hit[0] | hit[1];

// 命中判定方法：
// 1.若命中（至多1路），则返回该路序号；
// 2.都未命中，则选择s为0的
always @(*) begin
  if (hit[0] | hit[1]) begin
    hit_wayID = hit[1]; // hit[1]==1则命中1，否则命中0。二选一
  end
  else begin
    hit_wayID = (s[0] == 0 ? 0 : 1);
  end
end


// =============== Cache Data 缓存数据 ===============

reg   [127: 0]                cache_data_old [0:127];         // 即将弃用
wire                          cachedata0_cen;             // 第0片RAM 使能，低电平有效
wire                          cachedata0_wen;             // 第0片RAM 写使能，低电平有效
wire  [5  : 0]                cachedata0_addr;            // 第0片RAM 地址
wire  [127: 0]                cachedata0_wdata;           // 第0片RAM 写入数据
wire  [127: 0]                cachedata0_rdata;           // 第0片RAM 读出数据
wire                          cachedata1_cen;             // 第1片RAM 使能，低电平有效
wire                          cachedata1_wen;             // 第1片RAM 写使能，低电平有效
wire  [5  : 0]                cachedata1_addr;            // 第1片RAM 地址
wire  [127: 0]                cachedata1_wdata;           // 第1片RAM 写入数据
wire  [127: 0]                cachedata1_rdata;           // 第1片RAM 读出数据
reg                           cachedata_wen;              // 选中的RAM 写使能，低电平有效
reg   [5  : 0]                cachedata_addr;             // 选中的RAM 地址
reg   [127: 0]                cachedata_wdata;            // 选中的RAM 写入数据
wire  [127: 0]                cachedata_rdata;            // 选中的RAM 读出数据

// way0, 1KB
S011HD1P_X32Y2D128  cache_data0(
  .CLK                        (clk                  ),
  .CEN                        (cachedata0_cen       ),
  .WEN                        (cachedata0_wen       ),
  .A                          (cachedata0_addr      ),
  .Q                          (cachedata0_wdata     ),
	.D                          (cachedata0_rdata     )
);
// way1, 1KB
S011HD1P_X32Y2D128  cache_data1(
  .CLK                        (clk                  ),
  .CEN                        (cachedata1_cen       ),
  .WEN                        (cachedata1_wen       ),
  .A                          (cachedata1_addr      ),
  .Q                          (cachedata1_wdata     ),
	.D                          (cachedata1_rdata     )
);

assign cachedata0_cen = 1;
assign cachedata1_cen = 1;
assign cachedata_wen = hit_wayID ? cachedata1_wen : cachedata0_wen;
assign cachedata_addr = hit_wayID ? cachedata1_addr : cachedata0_addr;
assign cachedata_wdata = hit_wayID ? cachedata1_wdata : cachedata0_wdata;
assign cachedata_rdata = hit_wayID ? cachedata1_rdata : cachedata0_rdata;


// =============== 读写数据 ===============

wire  [5 : 0]       w0_addr;          // 数据所在的索引（ 0~15字节）

// wire  [6 : 0]     data_idx0;          // 数据所在的索引（ 0~15字节）
// wire  [6 : 0]     data_idx1;          // 数据所在的索引（16~31字节）
// wire  [6 : 0]     data_idx2;          // 数据所在的索引（32~47字节）
// wire  [6 : 0]     data_idx3;          // 数据所在的索引（48~63字节）
// wire  [511: 0]    rdata_blk;              // 读取的数据块内容
// wire  [8 : 0]       rdata_unit_start_bit;   // 读取的数据单元的起始位(0~127)
wire  [127: 0]      rdata_unit;             // 读取的数据单元内容
reg   [63: 0]       rdata_out;              // 根据用户需求的尺寸输出数据   

assign cachedata_addr = cline_no;


// cache_data解码     

// assign data_idx0  = {3'd0, mem_blkno} << 3 | 7'd0;
// assign data_idx1  = {3'd0, mem_blkno} << 3 | 7'd1;
// assign data_idx2  = {3'd0, mem_blkno} << 3 | 7'd2;
// assign data_idx3  = {3'd0, mem_blkno} << 3 | 7'd3;
// assign rdata_blk = {
//   cache_data[data_idx3],
//   cache_data[data_idx2],
//   cache_data[data_idx1],
//   cache_data[data_idx0]
// };
// assign rdata_unit_start_bit = {mem_offset, 3'b0};
assign rdata_unit = (!hit_wayID) ? cachedata0_rdata : cachedata1_rdata;

// 读取数据
always @(*) begin
  if (rst) begin
    rdata_out = 0;
  end
  else begin
    case (i_cache_size)
      // `SIZE_B:    rdata_out = {56'd0, rdata_unit[7:0]};
      // `SIZE_H:    rdata_out = {48'd0, rdata_unit[15:0]};
      // `SIZE_W:    rdata_out = {32'd0, rdata_unit[31:0]};
      `SIZE_D:    rdata_out = rdata_unit[cline_offset_bits +:64];
      default:    rdata_out = 0;
    endcase
  end
end

// 测试数据
always @(posedge clk) begin
  if (rst) begin
    //$readmemh("cache_test1.txt", cache_data);
  end
end
// 观察点
// wire [127:0] data_preview[0:15];
// generate
//   for (genvar i = 0; i < 16; i += 1) begin
//     assign data_preview[i] = cache_data[i];    
//   end
// endgenerate


// 状态机
//  英文名称          中文名称             含义
//  IDLE            空闲                 无活动。有用户请求则进入 READY / STORE_FROM_RAM / LOAD_FROM_BUS 这三种情况
//  READY           就绪                  命中，则直接读写。读写完毕回到IDLE。
//  STORE_FROM_RAM  存储(从RAM读取数据)    不命中并选择脏的数据块，则需要写回。先以128bit为单位分4次从RAM读入数据，读取完毕跳转到 StoreToBUS
//  STORE_TO_BUS    存储(写入总线)         不命中并选择脏的数据块，则需要写回。再将512bit数据写入总线，写入完毕跳转到 LoadFromBUS
//  LOAD_FROM_BUS   加载(从总线读取数据)    不命中并选择不脏的数据块，则需要读入新数据。先从总线读取512bit数据，读取完毕跳转到 LoadToRAM
//  LOAD_TO_RAM     加载(写入RAM)         不命中并选择不脏的数据块，则需要读入新数据。再以128bit为单位分4次写入RAM，写入完毕跳转到READY

parameter [2:0] STATE_IDLE              = 3'b000;
parameter [2:0] STATE_READY             = 3'b001;
parameter [2:0] STATE_STORE_FROM_RAM    = 3'b010;
parameter [2:0] STATE_STORE_TO_BUS      = 3'b011;
parameter [2:0] STATE_LOAD_FROM_BUS     = 3'b100;
parameter [2:0] STATE_LOAD_TO_RAM       = 3'b101;

reg [2:0] state;
wire state_idle             = state == STATE_IDLE;
wire state_ready            = state == STATE_READY;
wire state_store_from_ram   = state == STATE_STORE_FROM_RAM;
wire state_store_to_bus     = state == STATE_STORE_TO_BUS;
wire state_load_from_bus    = state == STATE_LOAD_FROM_BUS;
wire state_load_to_ram      = state == STATE_LOAD_TO_RAM;

always @(posedge clk) begin
    if (rst) begin
        state <= STATE_IDLE;
    end
    else begin
      case (state)
          STATE_IDLE:   begin
            if (i_cache_req) begin
              if (hit_any)          state <= STATE_READY;
              else begin
                if (d[hit_wayID])   state <= STATE_STORE_FROM_RAM;
                else                state <= STATE_LOAD_FROM_BUS;
              end
            end
          end
          
          STATE_READY:  begin
            if (hs_cache) begin
              o_cache_rw_req    <= 0;

              // 处理剩余的读写请求
              state <= STATE_IDLE;
            end
          end

          STATE_STORE_FROM_RAM:     begin
            if (hs_cache_rw) begin
              o_cache_rw_req    <= 0;
              state <= STATE_STORE_TO_BUS;
            end
          end

          STATE_STORE_TO_BUS:     begin
            if (hs_cache_rw) begin
              o_cache_rw_req    <= 0;
              state <= STATE_LOAD_FROM_BUS;
            end
          end

          STATE_LOAD_FROM_BUS: begin
            if (hs_cache_rw) begin
              state <= STATE_LOAD_TO_RAM;
            end
          end

          STATE_LOAD_TO_RAM: begin
            if (hs_cache_rw) begin
              state <= STATE_READY;
            end
          end

          default: ;
      endcase
    end
end

wire hs_cache = i_cache_req & o_cache_ack;
wire hs_cache_rw = o_cache_rw_req & i_cache_rw_ack;

// 处理用户请求
always @(posedge clk) begin
  if (rst) begin
    o_cache_ack <= 0;
  end
  else begin
    case (state)
      STATE_IDLE: begin;
        o_cache_ack <= 0;
      end

      STATE_READY: begin
        if (i_cache_op == `REQ_READ) begin
          o_cache_rdata <= rdata_out;
          o_cache_ack <= 1;
        end
        else begin
          // cache更新数据
          // case (i_cache_size)
          //   `SIZE_B:    rdata_out = {56'd0, rdata_unit[7:0]};
          //   `SIZE_H:    rdata_out = {48'd0, rdata_unit[15:0]};
          //   `SIZE_W:    rdata_out = {32'd0, rdata_unit[31:0]};
          //   `SIZE_D:    rdata_out = rdata_unit;
          //   default:    rdata_out = 0;
          // endcase
          // cache_data[data_idx3_hit] <= i_cache_rw_rdata[384+:128];
          // cache_data[data_idx2_hit] <= i_cache_rw_rdata[256+:128];
          // cache_data[data_idx1_hit] <= i_cache_rw_rdata[128+:128];
          // cache_data[data_idx0_hit] <= i_cache_rw_rdata[  0+:128];
          // cache更新记录
          // cache_info[mem_blkno][info_d_offset]  <= 1;
          o_cache_ack <= 1;
        end
      end

      STATE_LOAD_FROM_BUS: begin
        // 发送内部读请求
        o_cache_rw_req <= 1;
        o_cache_rw_addr <= addr_no_offset;
        o_cache_rw_op <= `REQ_READ;
        // cache更新
        if (hs_cache_rw) begin
          // cache更新数据
          // cache_wdata
          // cache_data[data_idx3_hit] <= i_cache_rw_rdata[384+:128];
          // cache_data[data_idx2_hit] <= i_cache_rw_rdata[256+:128];
          // cache_data[data_idx1_hit] <= i_cache_rw_rdata[128+:128];
          // cache_data[data_idx0_hit] <= i_cache_rw_rdata[  0+:128];
          // // cache更新记录
          // cache_info[mem_blkno][info_tag_offset+:21]  <= mem_tag; // tag
          // cache_info[mem_blkno][info_v_offset]        <= 1;       // 有效位
          // cache_info[mem_blkno][info_d_offset]        <= 0;       // 脏位
          // cache_info[mem_blkno][23] <= cache_info[mem_blkno][55]; // sequence 翻转
          // cache_info[mem_blkno][55] <= cache_info[mem_blkno][23];
        end
      end

      STATE_LOAD_TO_RAM: begin
        
      end

      STATE_STORE_FROM_RAM: begin
      end

      STATE_STORE_TO_BUS: begin
        // 发送内部写请求
        o_cache_rw_req <= 1;
        o_cache_rw_addr <= addr_no_offset;
        o_cache_rw_op <= `REQ_WRITE;
        // o_cache_rw_wdata  <= rdata_blk;
        // // cache更新
        // if (hs_cache_rw) begin
        //   // cache更新记录
        //   cache_info[mem_blkno][info_tag_offset+:21]  <= 0;       // tag
        //   cache_info[mem_blkno][info_v_offset]        <= 0;       // 有效位
        //   cache_info[mem_blkno][info_d_offset]        <= 0;       // 脏位
        // end
      end

      default:;
    endcase
  end
end


endmodule
