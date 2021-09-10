
// ZhengpuShi

// Cache Unit

/*
  Cache Disign (2021.09.08, by ZhengpuShi):
    [-] --- BASIC CONFIG
    [*] word_size = 32bit (4 bytes)             -- 指令是32bit的
    [*] block_size = 512bit (64 bytes)          -- AXI总线burst最大传输8次*8字节=64字节
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
    [*] cache_data_bits = 16 * 2 * 512 = 16Kbit = 2KB
    [*] cache_info_bits = 16 * (2 * (8 + 1 + 1 + 1 + 21)) = 1024bit = 128B 
    [*] --- ADDRESS TRANSFORM
      1. 主存地址 32bit：
        以字节为单位；共2^31个单元；只保留低31位；低6位是块内偏移；接着4位是块号；接着21位是tag
      2. 主存数据 8/16/32/64bit
        可以有多种访问方式
      3. cache_data地址 7bit：
        以128bit为单位；共128个单元（块）；                       
        每4个单元组成512bit的一个块；                -- 2bit         
        两个块组成两路，第一路是way0，第二路是way1；   -- 1bit
        每两路是一个组，共16组                       -- 4bit
      3. cache_info地址 4bit：
        以64bit为单位；共16个单元（块）；每个单元的高32位是way1，低32位是way0；
        每32bit从高位到低位，8bit保留，1bit顺序，1bit脏位，1bit有效位，21bit主存标记
    
*/

`include "defines.v"

module cache (
  input   wire                      clk,
  input   wire                      rst,
  input   wire  [`BUS_64]           i_cache_addr,         // 地址
  input   reg   [`BUS_64]           i_cache_wdata,        // 写入的数据
  input   reg   [1 : 0]             i_cache_size,         // 操作数大小: 00:byte, 01:half, 10:word, 11:dword
	input                             i_cache_op,           // 操作: 0:read, 1:write
	input                             i_cache_req,          // 请求
  output  reg   [`BUS_64]           o_cache_rdata,        // 读出的数据
	output                            o_cache_ack,          // 应答

  // cache_rw 接口
  input   wire  [511:0]             i_cache_rw_axi_rdata,
  input   wire                      i_cache_rw_axi_ready,
  output  wire                      o_cache_rw_axi_valid,
  output  wire                      o_cache_rw_axi_op,
  output  wire  [511:0]             o_cache_rw_axi_wdata,
  output  wire  [63:0]              o_cache_rw_axi_addr,
  output  wire  [1:0]               o_cache_rw_axi_size,
  output  wire  [7:0]               o_cache_rw_axi_blks
);

// ====== cache_rw 从机端，请求传输数据 ===============
reg                                 o_cache_rw_req;    // 请求
reg   [63 : 0]                      o_cache_rw_addr;   // 存储器地址（字节为单位），64字节对齐，低6位为0。
reg                                 o_cache_rw_op;     // 操作类型：0读取，1写入
reg   [511 : 0]                     o_cache_rw_wdata;  // 要写入的数据
wire  [511 : 0]                     i_cache_rw_rdata;  // 已读出的数据
wire                                i_cache_rw_ack;    // 应答

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

// ====== cache 业务逻辑 ===============

reg   [127: 0]    cache_data [0:127];
reg   [63 : 0]    cache_info [0:15];

// 物理地址解码
wire  [63: 0]     addr_no_offset = {33'd0, i_cache_addr[30:6], 6'd0};   // 去掉offset后的对齐的地址
wire  [63: 0]     mem_addr = {33'd0, i_cache_addr[30:0]};
wire  [5 : 0]     mem_offset = mem_addr[5:0];
wire  [3 : 0]     mem_blkno = mem_addr[9:6];
wire  [20: 0]     mem_tag = mem_addr[30:10];

// cache_info解码
wire  [20: 0]     tag[0:1];           // 各路的 tag
wire              v[0:1];             // 各路的 valid bit
wire              d[0:1];             // 各路的 dirty bit
wire              s[0:1];             // 各路的 seqence bit
wire              hit[0:1];           // 各路是否命中
wire              hit_any;            // 是否有任意一路命中？
reg               hit_wayID;          // 命中了哪一路？
wire  [5 : 0]     info_tag_offset;    // 命中记录的tag偏移量
wire  [5 : 0]     info_v_offset;      // 命中记录的v偏移量
wire  [5 : 0]     info_d_offset;      // 命中记录的d偏移量
wire  [5 : 0]     info_s_offset;      // 命中记录的s偏移量

assign tag[0]       = cache_info[mem_blkno][20:0];
assign v[0]         = cache_info[mem_blkno][21];
assign d[0]         = cache_info[mem_blkno][22];
assign s[0]         = cache_info[mem_blkno][23];
assign tag[1]       = cache_info[mem_blkno][52:32];
assign v[1]         = cache_info[mem_blkno][53];
assign d[1]         = cache_info[mem_blkno][54];
assign s[1]         = cache_info[mem_blkno][55];
assign hit[0]       = v[0] && (tag[0] == mem_tag);
assign hit[1]       = v[1] && (tag[1] == mem_tag);
assign hit_any      = hit[0] | hit[1];

// 命中策略：1.若命中1路（至多1路）则返回；2.都未命中，则选择s为0的
always @(*) begin
  if (hit[0] | hit[1]) begin
    hit_wayID = hit[1]; // hit[1]==1则命中1，否则命中0。二选一
  end
  else begin
    hit_wayID = (s[0] == 0 ? 0 : 1);
  end
end

assign info_tag_offset  = hit_wayID ? 32 : 0;
assign info_v_offset    = hit_wayID ? 53 : 21;
assign info_d_offset    = hit_wayID ? 54 : 22;
assign info_s_offset    = hit_wayID ? 55 : 23;

// cache_data解码
wire  [6 : 0]     data_idx0[0:1];         // 数据所在的索引（ 0~15字节）
wire  [6 : 0]     data_idx1[0:1];         // 数据所在的索引（16~31字节）
wire  [6 : 0]     data_idx2[0:1];         // 数据所在的索引（32~47字节）
wire  [6 : 0]     data_idx3[0:1];         // 数据所在的索引（48~63字节）
wire  [6 : 0]     data_idx0_hit;          // 数据所在的索引（ 0~15字节）已选中的
wire  [6 : 0]     data_idx1_hit;          // 数据所在的索引（16~31字节）已选中的
wire  [6 : 0]     data_idx2_hit;          // 数据所在的索引（32~47字节）已选中的
wire  [6 : 0]     data_idx3_hit;          // 数据所在的索引（48~63字节）已选中的
wire  [511: 0]    rdata_blk;              // 读取的数据块内容
wire  [8 : 0]     rdata_unit_start_bit;   // 读取的数据单元的起始位(0~511)
wire  [63: 0]     rdata_unit;             // 读取的数据单元内容
reg   [63: 0]     rdata_out;              // 根据用户需求的尺寸输出数据        

assign data_idx0[0]  = {3'd0, mem_blkno} << 3;
assign data_idx1[0]  = {3'd0, mem_blkno} << 3 | 7'd1;
assign data_idx2[0]  = {3'd0, mem_blkno} << 3 | 7'd2;
assign data_idx3[0]  = {3'd0, mem_blkno} << 3 | 7'd3;
assign data_idx0[1]  = {3'd0, mem_blkno} << 3 | 7'd4;
assign data_idx1[1]  = {3'd0, mem_blkno} << 3 | 7'd5;
assign data_idx2[1]  = {3'd0, mem_blkno} << 3 | 7'd6;
assign data_idx3[1]  = {3'd0, mem_blkno} << 3 | 7'd7;
assign data_idx0_hit = data_idx0[hit_wayID];
assign data_idx1_hit = data_idx1[hit_wayID];
assign data_idx2_hit = data_idx2[hit_wayID];
assign data_idx3_hit = data_idx3[hit_wayID];
assign rdata_blk = {
  cache_data[data_idx3_hit],
  cache_data[data_idx2_hit],
  cache_data[data_idx1_hit],
  cache_data[data_idx0_hit]
};
assign rdata_unit_start_bit = {mem_offset, 3'b0};
assign rdata_unit = rdata_blk[rdata_unit_start_bit+:64];

always @(*) begin
  if (rst) begin
    rdata_out = 0;
  end
  else begin
    case (i_cache_size)
      `SIZE_B:    rdata_out = {56'd0, rdata_unit[7:0]};
      `SIZE_H:    rdata_out = {48'd0, rdata_unit[15:0]};
      `SIZE_W:    rdata_out = {32'd0, rdata_unit[31:0]};
      `SIZE_D:    rdata_out = rdata_unit;
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
wire [127:0] data_preview[0:15];
generate
  for (genvar i = 0; i < 16; i += 1) begin
    assign data_preview[i] = cache_data[i];    
  end
endgenerate

// 状态机
//  英文名称     中文名称       含义
//  IDLE        空闲          无活动
//  READY       就绪          命中，则直接读写。读写完毕回到IDLE。
//  WB          写回          不命中并选择脏的数据块，则需要写回。写回完毕跳转到LOADDATA
//  LOAD        读取          不命中并选择不脏的数据块，则需要读入新数据。读取完毕跳转到READY

parameter [1:0] STATE_IDLE = 2'b00, STATE_READY = 2'b01, STATE_WB = 2'b10, STATE_LOAD = 2'b11;

reg [1:0] state;
wire state_idle = state == STATE_IDLE;
wire state_ready = state == STATE_READY;
wire state_wb = state == STATE_WB;
wire state_load = state == STATE_LOAD;

always @(posedge clk) begin
    if (rst) begin
        state <= STATE_IDLE;
    end
    else begin
      case (state)
          STATE_IDLE:   begin
            if (i_cache_req) begin
              if (hit_any)  state <= STATE_READY;
              else          state <= STATE_LOAD;
            end
          end
          STATE_READY:  begin
            if (hs_cache) begin
              state <= STATE_IDLE;
            end 
          end
          STATE_WB:     begin
            
          end
          STATE_LOAD:   begin
            if (hs_load) begin
              state <= STATE_READY;
            end
            
          end
          default: ;
      endcase
    end
end


wire hs_cache = i_cache_req & o_cache_ack;
wire hs_cache_read  = hs_cache & (i_cache_op == `REQ_READ);
wire hs_cache_write = hs_cache & (i_cache_op == `REQ_WRITE);

wire hs_load = o_cache_rw_req & i_cache_rw_ack;

// 处理用户请求
always @(posedge clk) begin
  if (rst) begin
    o_cache_ack <= 0;
  end
  else begin
    case (state)
      STATE_IDLE:     begin;
        o_cache_ack <= 0;     // 撤销cache应答
      end
      STATE_READY:    begin
        o_cache_rw_req    <= 0;   // 撤销内部读写请求
        if (i_cache_op == `REQ_READ) begin
          o_cache_rdata  <= rdata_out;
          o_cache_ack    <= 1;    // 发送cache应答
        end
      end
      STATE_LOAD:     begin
        o_cache_rw_req    <= 1;   // 发送内部读写请求
        o_cache_rw_addr   <= addr_no_offset;
        o_cache_rw_op     <= `REQ_READ;
        if (hs_load) begin
          // cache保存数据
          cache_data[data_idx3_hit] <= i_cache_rw_rdata[384+:128];
          cache_data[data_idx2_hit] <= i_cache_rw_rdata[256+:128];
          cache_data[data_idx1_hit] <= i_cache_rw_rdata[128+:128];
          cache_data[data_idx0_hit] <= i_cache_rw_rdata[  0+:128];
          // cache更新记录
          cache_info[mem_blkno][info_tag_offset+:21]  <= mem_tag; // tag
          cache_info[mem_blkno][info_v_offset]        <= 1;       // 有效位
          cache_info[mem_blkno][info_d_offset]        <= 0;       // 脏位
          cache_info[mem_blkno][23] <= cache_info[mem_blkno][55]; // sequence 翻转
          cache_info[mem_blkno][55] <= cache_info[mem_blkno][23];
        end
      end
      default:;
    endcase
  end
end

// cache_info初始化
generate
  for (genvar i = 0; i < 16; i += 1) begin

    always @(posedge clk) begin
      if (rst) begin
        assign cache_info[i] = 64'h00800000_00000000;   // s1=1, s0=0
      end
    end

  end
endgenerate


endmodule
