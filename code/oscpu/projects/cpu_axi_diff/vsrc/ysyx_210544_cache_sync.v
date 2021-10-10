
// ZhengpuShi

// Cache Synchronous，处理DCache到ICache的一致性

// 典型应用：DCache存储了程序，将PC指针指向此地址时，默认只会从ICache取指，娶不到这些数据。
// 方法，fence.i 指令。作用：请求将DCache中的数据同步到ICache中，以便能够取到指令。
// 由于在Flash中执行程序时，会将Memory地址看做是数据，所有搬运完的数据除非装填不下，否则都会在DCache中，
// 此时需要将DCache中的数据处理掉，两种方法：
// 1. 最笨的方法，让DCache中的脏数据全部写回到Memory。
// 2. 聪明的方法，将DCache中的脏数据全部同步到ICache中，虽然可能会使ICache中的有些指令会冲掉，但影响有限。
// 采用方法2，具体做法（这里不检测是否为脏数据，先做一个全部同步的版本）
// 1. 收到fence请求，
// 2. 模拟一套8字节为大小的搬运请求
//   a. 时钟继续运行
//   b. dcache读取一包数据
//   c. icache写入一包数据
//   d. 循环b/c操作，直到完成任务。

`include "defines.v"

module ysyx_210544_cache_sync(
  input                       clk,
  input                       rst,
  
  // fence.i
  input   wire                i_fencei_req,
  output  reg                 o_fencei_ack,
  
  // DCache
  output  reg                 o_sync_dcache_rreq,     // 读请求
  input   wire                i_sync_dcache_rack,     // 读应答
  input   wire                i_sync_dcache_rpackreq, // 读包请求
  output  reg                 o_sync_dcache_rpackack, // 读包应答
  input   wire  [  1: 0]      i_sync_dcache_rwayid,   // read way_id
  input   wire  [  3: 0]      i_sync_dcache_rblkid,   // read blk_id
  input   wire  [ 25: 0]      i_sync_dcache_rinfo,    // read cache_info
  input   wire  [511: 0]      i_sync_dcache_rdata,    // read cache_data

  // ICache
  output  reg                 o_sync_icache_wreq,     // 写请求
  input   wire                i_sync_icache_wack,     // 写应答
  output  reg   [  1: 0]      o_sync_icache_wwayid,   // write way_id
  output  reg   [  3: 0]      o_sync_icache_wblkid,   // write blk_id
  output  reg   [ 25: 0]      o_sync_icache_winfo,    // write cache_info
  output  reg   [511: 0]      o_sync_icache_wdata     // write cache_data
);

// =============== 状态机 ===============
//  英文名称          中文名称    含义
//  IDLE            空闲        无活动。有fencei请求进入 SYNC_READ
//  SYNC_READ       读          读DCache。读到一包数据，进入 SYNC_WRITE；读取完成，进入 IDLE
//  SYNC_WRITE      写          写ICache。写入ICache完成，进入 SYNC_RPACK_ACK
//  SYNC_RPACK_ACK  读包应答     读包应答的写入和清除。清除后，进入 SYNC_READ
parameter [1:0] STATE_IDLE              = 2'd0;
parameter [1:0] STATE_SYNC_READ         = 2'd1;
parameter [1:0] STATE_SYNC_WRITE        = 2'd2;
parameter [1:0] STATE_SYNC_RPACK_ACK    = 2'd3;

reg [1:0] state;
wire hs_rd;
wire hs_wr;



assign hs_rd          = o_sync_dcache_rreq & i_sync_dcache_rack;
// wire hs_rd_pack     = o_sync_dcache_rpackack & i_sync_dcache_rpackreq;
assign hs_wr          = o_sync_icache_wreq & i_sync_icache_wack;

always @(posedge clk) begin
  if (rst) begin
    state <= STATE_IDLE;
  end
  else begin
    case (state)
      STATE_IDLE:   begin
        if (i_fencei_req & (!o_fencei_ack)) begin
          state <= STATE_SYNC_READ;
        end
      end
      
      STATE_SYNC_READ:  begin
        if (i_sync_dcache_rpackreq) begin
          state <= STATE_SYNC_WRITE;
        end
        else if (hs_rd) begin
          state <= STATE_IDLE;
        end
      end

      STATE_SYNC_WRITE:     begin
        if (hs_wr) begin
          state <= STATE_SYNC_RPACK_ACK;
        end
      end

      STATE_SYNC_RPACK_ACK:     begin
        // 等待 rapckreq 信号撤销
        if (!i_sync_dcache_rpackreq) begin
          state <= STATE_SYNC_READ;
        end
      end

      default: ;
    endcase
  end
end

always @(posedge clk) begin
  if (rst) begin
    o_fencei_ack <= 0;
    o_sync_dcache_rreq <= 0;
    o_sync_icache_wwayid <= 0;
    o_sync_icache_wblkid <= 0;
    o_sync_icache_winfo <= 0;
    o_sync_icache_wdata <= 0;
    o_sync_icache_wreq <= 0;
    o_sync_dcache_rpackack <= 0;
  end
  else begin
    case (state)
      STATE_IDLE: begin;
        o_fencei_ack <= 0;
      end

      STATE_SYNC_READ: begin
        if (!hs_rd) begin
          o_sync_dcache_rreq <= 1;
        end
        else begin
          o_fencei_ack <= 1;
          o_sync_dcache_rreq <= 0;
        end

        if (i_sync_dcache_rpackreq) begin
          o_sync_icache_wwayid  <= i_sync_dcache_rwayid;
          o_sync_icache_wblkid  <= i_sync_dcache_rblkid;
          o_sync_icache_winfo   <= i_sync_dcache_rinfo;
          o_sync_icache_wdata   <= i_sync_dcache_rdata;
        end
      end

      STATE_SYNC_WRITE: begin
        if (!hs_wr) begin
          o_sync_icache_wreq <= 1;
        end
        else begin
          o_sync_icache_wreq <= 0;
          o_sync_dcache_rpackack <= 1;
        end
      end

      STATE_SYNC_RPACK_ACK: begin
        // rapckack只保持一个周期，自动清除
        o_sync_dcache_rpackack <= 0; 
      end

      default:;
    endcase
  end
end

endmodule
