
// ZhengpuShi

// Cache Unit
// ICache,DCache都可以用这个模块，虽然ICache不需要写，更简化。

/*
  Cache Disign (2021.09.08, by ZhengpuShi):
    [-] --- BASIC CONFIG
    [*] word_size = 32bit (4 bytes)             -- 指令是32bit的
    [*] block_size = 512bit (64 bytes)          -- 块大小，AXI总线burst最大传输8次*8字节=64字节
    [*] offset index bits = 6 (2^6 = 64)        -- 由块大小决定
    [*] cache bytes max = 4KB * 2               -- ICache/DCache各4KB
    [*] main memory bytes = 2GB = 2^31          -- 主存地址空间2GB
    [*] raw-memory width = 128bit               -- 后端决定
    [*] raw-memory depth = 64                   -- 后端决定
    [-] --- CACHE CONFIG，4路16组
    [*] cache ways = 4way                       -- 2/4/8/...
    [*] cache blocks per way = 16blocks         -- 8/16/32/...
    [*] cache block index bits = 4 (2^4 = 16)   -- 由块数决定
    [*] cache data bytes = 2 * 16 * 64B = 2KB   -- 由路数、块数、块大小决定
    [*] bits_mem_tag = 31 - 4 - 6 = 21          -- 主存标记，由主存大小、cache块数、块大小决定
    [*] bits_v = 1 (data valid)                 -- 为1表示有效
    [*] bits_d = 1 (data dirty)                 -- 为1表示脏数据，在替换时需要写入主存
    [*] bits_s = 2 (sequence)                   -- FIFO策略：初始化各路分别为0,1,2,3；替换时换掉为3的一路；并将顺序加1。
    [-] --- CACHE STORAGE，分两块存储，数据与标记。 
    [*] cache_data_bits = 4 * (16 * 512) = 32Kbit = 4KB
    [*] cache_info_bits = 4 * (16 * (2 + 1 + 1 + 21)) = 1600bit = 200B 
    [*] --- ADDRESS TRANSFORM
      1. 主存地址 31bit：
        以字节为单位；共2^31个单元；只保留低31位；低6位是块内偏移；接着4位是块号；接着21位是tag
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
        每行25bit，从高位到低位，2bit顺序，1bit脏位，1bit有效位，21bit主存标记
      4. 跨页访问
        可能产生的跨页，需要处理第二块cache区域
        1. byte访问不会产生跨页
        2. half访问，可能产生1字节的跨页
        3. word访问，可能产生1~3字节的跨页
        4. dword访问，可能产生1~7字节的跨页
*/

`include "defines.v"

`define WAYS        4         // 路数
`define ROWS        16        // 行数
`define BUS_WAYS    0:3       // 各路的总线。4路
`define BUS_ROWS    0:15      // 各行的总线。16行

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

wire  [5 : 0]                 tag_pos;                            // tag位置(0~31)
wire  [5 : 0]                 v_pos;                              // v位置(0~31)
wire  [5 : 0]                 d_pos;                              // d位置(0~31)
wire  [5 : 0]                 s_pos;                              // s位置(0~31)
reg   [24 : 0]                cache_info[`BUS_WAYS][`BUS_ROWS];   // 缓存信息
wire  [5 : 0]                 cline_no[`BUS_WAYS];                // cache行号(0~63)
wire  [6 : 0]                 cline_offset_bits[`BUS_WAYS];       // cache行内偏移量bit(0~127)
wire  [20: 0]                 tag[`BUS_WAYS];                     // tag 内容
wire                          v[`BUS_WAYS];                       // valid bit 内容
wire                          d[`BUS_WAYS];                       // dirty bit 内容
wire  [1 : 0]                 s[`BUS_WAYS];                       // seqence bit 内容


assign tag_pos = 0;
assign v_pos = 21;
assign d_pos = 22;
assign s_pos = 23;

// cache_info
generate
  for (genvar way = 0; way < `WAYS; way += 1) begin
    parameter [1:0] w = way;
    for (genvar r = 0; r < `ROWS; r += 1) begin
      always @(posedge clk) begin
        if (rst) begin
          assign cache_info[w][r] = {w, 1'b0, 1'b0, 21'b0};
        end
      end
    end
  end
endgenerate

// cline_no, cline_offset_bits, tag, v, d, s
generate
  for (genvar way = 0; way < `WAYS; way += 1) begin
    parameter [1:0] w = way;
    assign cline_no[w] = ({2'b0, mem_blkno} << 2) | (mem_offset_bytes >> 2);
    assign cline_offset_bits[w] = mem_offset_bits[6:0];
    assign tag[w]   = cache_info[w][mem_blkno][20:0];
    assign v[w]     = cache_info[w][mem_blkno][21];
    assign d[w]     = cache_info[w][mem_blkno][22];
    assign s[w]     = cache_info[w][mem_blkno][24:23];
  end
endgenerate


// =============== 命中判定 ===============

wire                          hit[`BUS_WAYS];     // 各路是否命中
wire                          hit_any;            // 是否有任意一路命中？
wire [1:0]                    wayID_smax;         // s最大的是哪一路？
wire [1:0]                    wayID_hit;          // 已命中的是哪一路（至多有一路命中） 
wire [1:0]                    wayID_select;       // 选择了哪一路？方法：若命中则就是命中的那一路；否则选择smax所在的那一路

// hit
generate
  for (genvar way = 0; way < `WAYS; way += 1) begin
    parameter [1:0] w = way;
    for (genvar r = 0; r < `ROWS; r += 1) begin
      assign hit[w] = v[w] && (tag[w] == mem_tag);
    end
  end
endgenerate

assign hit_any = hit[0] | hit[1] | hit[2] | hit[3];
assign wayID_hit = (hit[1] ? 1 : 0) | (hit[2] ? 2 : 0) | (hit[3] ? 3 : 0);
assign wayID_smax = (s[1] == 3 ? 1 : 0) | (s[2] == 3 ? 2 : 0) | (s[3] == 3 ? 3 : 0);
assign wayID_select = hit_any ? wayID_hit : wayID_smax;


// =============== Cache Data 缓存数据 ===============

reg                           cachedata_cen[`BUS_WAYS];         // RAM 使能，低电平有效
reg                           cachedata_wen[`BUS_WAYS];         // RAM 写使能，低电平有效
reg   [5  : 0]                cachedata_addr[`BUS_WAYS];        // RAM 地址
reg   [127: 0]                cachedata_wdata[`BUS_WAYS];       // RAM 写入数据
wire  [127: 0]                cachedata_rdata[`BUS_WAYS];       // RAM 读出数据

// RAM instantiate
generate
  for (genvar way = 0; way < `WAYS; way += 1) begin: gen_cache_data
    parameter [1:0] w = way;
    S011HD1P_X32Y2D128  cache_data(
      .CLK                        (clk                  ),
      .CEN                        (cachedata_cen[w]     ),
      .WEN                        (cachedata_wen[w]     ),
      .A                          (cachedata_addr[w]    ),
      .D                          (cachedata_wdata[w]   ),
      .Q                          (cachedata_rdata[w]   )
    );
  end
endgenerate

// cen, addr
generate
  for (genvar way = 0; way < `WAYS; way += 1) begin
    parameter [1:0] w = way;
    always @(posedge clk) begin
      if (rst) begin
        assign cachedata_cen[w] = 0;
        assign cachedata_wen[w] = 1;
      end
    end
  end
endgenerate

wire [5:0] s5 = cline_no[3] | {4'd0, ram_op_cnt[1:0]};

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
assign rdata_unit = cachedata_rdata[wayID_select];

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
      `SIZE_D:    rdata_out = rdata_unit[cline_offset_bits[wayID_select]+:64];
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
parameter [2:0] STATE_IDLE              = 3'd0;
parameter [2:0] STATE_READY             = 3'd1;
parameter [2:0] STATE_STORE_FROM_RAM    = 3'd2;
parameter [2:0] STATE_STORE_TO_BUS      = 3'd3;
parameter [2:0] STATE_LOAD_FROM_BUS     = 3'd4;
parameter [2:0] STATE_LOAD_TO_RAM       = 3'd5;

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
              if (hit_any)            state <= STATE_READY;
              else begin
                if (d[wayID_select])  state <= STATE_STORE_FROM_RAM;
                else                  state <= STATE_LOAD_FROM_BUS;
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
            if (hs_ram) begin
              state <= STATE_READY;
            end
          end

          default: ;
      endcase
    end
end

reg   [2:0]   ram_op_cnt;           // RAM操作计数器(0~3表示1~4次)
wire  [8:0]   ram_op_offset_bits;   // RAM操作的偏移位数
wire          hs_cache;             // cache操作 握手
wire          hs_cache_rw;          // cache_rw操作 握手
wire          hs_ram;               // ram操作 握手

assign ram_op_offset_bits = {7'd0, ram_op_cnt[1:0]} << 7;
assign hs_cache = i_cache_req & o_cache_ack;
assign hs_cache_rw = o_cache_rw_req & i_cache_rw_ack;
assign hs_ram = ram_op_cnt == 3'd4;

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
            // `SIZE_D:    rdata_out = rdata_unit;
            // default:    rdata_out = 0;
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
        ram_op_cnt <= 0;
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
        // cachedata_wdata[hit_wayID][63:0] <=  64'h01234567_89ABCDEF << ram_op_cnt;
        // cachedata_wdata[hit_wayID][127:64] <= 64'h00112233_44556677 << ram_op_cnt;
        if (!hs_ram) begin
          cachedata_wen[wayID_select] <= 0;
          cachedata_addr[wayID_select] <= cline_no[wayID_select] | {3'd0, ram_op_cnt};
          cachedata_wdata[wayID_select] <= i_cache_rw_rdata[ram_op_offset_bits+:128];// (ram_op_cnt) << 7 +:128];
          ram_op_cnt <= ram_op_cnt + 1;
        end
        else begin
          cachedata_wen[wayID_select] <= 1;
          cachedata_addr[wayID_select] <= cline_no[wayID_select];
          ram_op_cnt <= 0;
        end
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

wire [127:0] s1 = i_cache_rw_rdata[0  +:128];
wire [127:0] s2 = i_cache_rw_rdata[128+:128];
wire [127:0] s3 = i_cache_rw_rdata[256+:128];
wire [127:0] s4 = i_cache_rw_rdata[384+:128];


endmodule
