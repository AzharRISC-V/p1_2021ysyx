
// ZhengpuShi

/*
  Cache

  2021.09.08 的第一版设计方案
  1. 组相连方式，4way（四路）, 64set, 存储32bit的字，也就是存储单元为4Byte
    换言之，有4个物理上相同的cache块，每块有64线，每线是4字节，即每块是256字节。
    假设cpu访存的某个地址区域在256字节范围内，有4个这样的活动区块。
  2. 物理内存空间考虑4GB，32bit
  3. cache存储结构如下

        way3        way2        way1        way0
        ----------  ----------  ----------  ----------
        v tag data  v tag data  v tag data  v tag data   
  set0
  set1
  ...
  set63

  其中：
  (1). data占32bit，v占1bit
  (2). 由于64set * 4Byte=256Byte，即Cache块的大小是256Byte
  (3). 物理地址4GB划分为256Byte的块，共2^24个块，所以tag占24bit（若是64bit的物理地址，则为2^(24+32)个块，占用56bit）
  (4). 所以cache的大小是：64 * 4 * (1 + 24 + 32) / 8 = 1842 Bytes

  4. cache替换策略：FIFO。
    假设四路都已占用后又有新的存储需求，则按照FIFO策略替换最先进入的区块。
    ---------(第一次设计)------------
    为此单独记录4路的进入顺序。
    第一次占满后的顺序：seq0=00,seq1=01,seq2=10,seq3=11
    第一次替换，撤出seq0，顺序变更为：seq0=11,seq1=00,seq2=01,seq3=10
    第二次替换，撤出seq1，顺序变更为：seq0=10,seq1=11,seq2=00,seq3=01
    （规律：00-01-10-11 循环右移两位）
    （如何快速找到 00 所在的组号？可以换个思路，按照顺序来保存组号，而不是按照组号来保存顺序）
    ---------(第二次设计)------------
    按照需要被替换掉的顺序记录way号，共4个数据，第0个数据是最先需要被替换掉的way号
    初始的way号： 00,01,10,11   最左侧的数据是00，表示要替换第0个way
    写入一次：    11,00,01,10   下次替换第1-way
    写入一次：    10,11,00,01   下次替换第2-way
    写入一次：    01,10,11,00   下次替换第3-way
    写入一次：    00,01,10,11   下次替换第4-way
*/

`include "defines.v"

module cache #(
  parameter CDATAWIDTH = 32,
  parameter CWAYS = 4,
  parameter CSETS = 64,
  parameter CMEMORYBITS = 64
) (
  input   wire                      clk,
  input   wire                      rst,
  input   wire  [`BUS_32]           i_cache_raddr,            // 读地址
  output  reg   [CDATAWIDTH-1:0]    o_cache_rdata,            // 读出的数据

  input  reg                        i_cache_req,              // 请求cache的握手信号
  output reg                        o_cache_ack,

  ///////////////////////////////////////////////
  // AXI interface
	input                             i_cache_axi_ready,
  input         [`BUS_64]           i_cache_axi_rdata,
  input         [1:0]               i_cache_axi_resp,
	output reg                        o_cache_axi_valid,
  output reg    [`BUS_64]           o_cache_axi_addr,
  output        [1:0]               o_cache_axi_size,
  
  ///////////////////////////////////////////////
  input   wire                i_if_pc_jmp,
  input   wire  [`BUS_64]     i_if_pc_jmpaddr,
  output  reg   [`BUS_64]     o_if_pc,
  output  wire  [`BUS_64]     o_if_pc_pred,

);

endmodule
