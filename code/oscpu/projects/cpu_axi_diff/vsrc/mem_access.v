// ZhengpuShi

`include "defines.v"


// 内存读取控制器，将1字节访问转换为8字节对齐的一次或两次访问
module mem_access (
  input   wire  [`BUS_64]       clk_cnt,
  input   wire                  clk,
  input   wire  [`BUS_64]       addr,     // 以字节为单位的访存地址
  input   wire  [2 : 0]         funct3,

  input   wire                  ren,      // 读使能
  output  reg   [`BUS_64]       rdata,    // 读到的数据

  input   wire  [`BUS_64]       wdata,    // 写入数据
  input   wire                  wen       // 写使能
);

// -------------------------- 读写共有的信号 --------------------------
// 读或写信号至少有一个有效
wire  en = ren | wen;

// 除去基地址后的相对地址
wire  [`BUS_64]   addr_rel = (!en) ? 0 : addr - 64'h00000000_80000000;

// 第1/2次访存地址
wire  [`BUS_64]   addr1 = (!en) ? 0 : addr_rel >> 3;
wire  [`BUS_64]   addr2 = (!en) ? 0 : addr1 + 64'b1;

// 字节偏移量（由地址低3位决定）：0 ~ 7
wire  [2 : 0]     byte_offset1 = {{5{1'b0}}, addr[2:0]};
wire  [2 : 0]     byte_offset2 = 8 - byte_offset1;

// 位偏移：0 ~ 63
wire [5 : 0]      bit_offset1 = byte_offset1 << 3;
wire [5 : 0]      bit_offset2 = 64 - bit_offset1;

// 字节数（由funct3[1:0]决定）：1/2/4/8
// Byte 00, Half 01, Word 10, Dword 11
wire [7:0] bytes = 2 ** funct3[1:0];

// 是否需要访问第二个64bit单元
reg unit2_req = byte_offset1 + bytes > 8;

// 数据的位掩码
// byte   00000000_000000FF
// half   00000000_0000FFFF
// word   00000000_FFFFFFFF
// dword  FFFFFFFF_FFFFFFFF
reg [`BUS_64] bit_mask;
always @(*) begin
  if (!en) begin
    bit_mask = 0;
  end
  else begin
    case (funct3[1:0])
      2'b00   : bit_mask = 64'h00000000_000000FF;
      2'b01   : bit_mask = 64'h00000000_0000FFFF;
      2'b10   : bit_mask = 64'h00000000_FFFFFFFF;
      2'b11   : bit_mask = 64'hFFFFFFFF_FFFFFFFF;
      default : bit_mask = 0;
    endcase
  end
end

// 是否打印调试信息？
wire show_dbg = 0;// (clk_cnt >= `CLK_CNT_VAL);

// -------------------------- 读取 --------------------------

// 读取使能信号
wire ren_unit1 = ren & (!unit2_req);
wire ren_unit2 = ren & unit2_req;

// 读取两份数据
wire [`BUS_64] rdata1 = (!ren_unit1) ? 0 : ram_read_helper(show_dbg, ren_unit1, addr1);
wire [`BUS_64] rdata2 = (!ren_unit2) ? 0 : ram_read_helper(show_dbg, ren_unit2, addr2);

// 读取到的两份数据合并位一份
wire [`BUS_64] rdata_0 = (rdata1 >> bit_offset1) | (rdata2 << bit_offset2);

// 过滤出摘出需要读取的数据
always @(*) begin
  if (ren) begin
    case (funct3)
    `FUNCT3_LB    : rdata = $signed(rdata_0[7:0]);
    `FUNCT3_LH    : rdata = $signed(rdata_0[15:0]);
    `FUNCT3_LW    : rdata = $signed(rdata_0[31:0]);
    `FUNCT3_LD    : rdata = rdata_0[63:0];
    `FUNCT3_LBU   : rdata = rdata_0[7:0];
    `FUNCT3_LHU   : rdata = rdata_0[15:0];
    `FUNCT3_LWU   : rdata = rdata_0[31:0];
    default       : rdata = 0;
    endcase
  end
  else begin
    rdata = 0;
  end
end

// 打印调试信息
always @(*) begin
  if (ren_unit1 && show_dbg)
    $displayh("  MEMACC: raddr1=", addr1, " rdata1=", rdata1, " rdata=", rdata);
end
always @(*) begin
  if (ren_unit2 && show_dbg) 
    $displayh("  MEMACC: raddr2=", addr2, " rdata2=", rdata2, " rdata=", rdata); 
end

// -------------------------- 写入 --------------------------

// 写使能
wire wen_unit1 = wen & (!unit2_req);
wire wen_unit2 = wen & unit2_req;

// 写掩码
reg [`BUS_64] wmask1 = (!wen_unit1) ? 0 : bit_mask << bit_offset1;
reg [`BUS_64] wmask2 = (!wen_unit2) ? 0 : bit_mask >> bit_offset2;

// 写数据
wire [`BUS_64] wdata1 = (!wen_unit1) ? 0 : wdata << bit_offset1;
wire [`BUS_64] wdata2 = (!wen_unit2) ? 0 : wdata >> bit_offset2;

// 写入
always @(negedge clk) begin
  if (wen_unit1) begin
    ram_write_helper(show_dbg, addr1, wdata1, wmask1, wen_unit1);
    if (show_dbg) begin
      $displayh("  MEMACC: waddr1=", addr1, " wdata1=", wdata1, " wmask1=", wmask1); 
    end
  end

  if (wen_unit2) begin
    ram_write_helper(show_dbg, addr2, wdata2, wmask2, wen_unit2);
    if (show_dbg) begin
      $displayh("  MEMACC: waddr2=", addr2, " wdata2=", wdata2, " wmask2=", wmask2);
    end
  end

end


endmodule