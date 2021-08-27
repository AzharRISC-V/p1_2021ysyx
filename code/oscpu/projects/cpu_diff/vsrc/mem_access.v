// ZhengpuShi

`include "defines.v"


// 内存读取控制器，将1字节访问转换为8字节对齐的一次或两次访问
module mem_access (
  input   wire  [`BUS_64]       clk_cnt,
  input   wire                  clk,
  input   wire  [`BUS_64]       addr,     // 以字节为单位的访存地址
  input   wire  [2 : 0]         funct3,

  output  reg                   sig_memread_ok,
  output  reg                   sig_memwrite_ok,

  input   wire                  ren,      // 读使能
  output  wire  [`BUS_64]       rdata,    // 读到的数据

  input   wire  [`BUS_64]       wdata,    // 写入数据
  input   wire  [`BUS_64]       wmask,    // 写入数据的掩码
  input   wire                  wen       // 写使能
);


// 是否需要访问第二个64bit单元
wire ena2 = (addr[2:0] == 3'b000) ? 0 : 1;

// 除去基地址后的相对地址
wire [`BUS_64] addr_rel = addr - 64'h00000000_80000000;

// 第1/2次访存地址
wire [`BUS_64] addr1 = addr_rel >> 3;
wire [`BUS_64] addr2 = addr1 + 64'b1;

// 8字节编址的内部偏移量（字节数）
wire [2:0] byte_offset = addr[2:0];         

// 是否打印调试信息？
wire show_dbg = (clk_cnt >= `CLK_CNT_VAL);

// 读取数据
wire [`BUS_64] rdata1 = ram_read_helper(show_dbg, ren, addr1);
wire [`BUS_64] rdata2 = ram_read_helper(show_dbg, ren & ena2, addr2);

always @(*) begin
  if (ren && show_dbg)
    $displayh("  MEMACC: raddr1=", addr1, " rdata1=", rdata1, " rdata=", rdata, " ren=", ren);
end
always @(*) begin
  if ((ren & ena2) && show_dbg) 
    $displayh("  MEMACC: raddr2=", addr2, " rdata2=", rdata2, " rdata=", rdata, " ren=", ren, " ena2=", ena2); 
end

// 合成读取数据
reg [`BUS_64] rdata_0;
always @(*) begin
  if (ren) begin
    case (byte_offset)
      0'b000  : begin rdata_0 = {rdata1}; end
      0'b001  : begin rdata_0 = {rdata2[ 7:0], rdata1[63: 8]}; end
      0'b010  : begin rdata_0 = {rdata2[15:0], rdata1[63:16]}; end
      0'b011  : begin rdata_0 = {rdata2[23:0], rdata1[63:24]}; end
      0'b100  : begin rdata_0 = {rdata2[31:0], rdata1[63:32]}; end
      0'b101  : begin rdata_0 = {rdata2[39:0], rdata1[63:40]}; end
      0'b110  : begin rdata_0 = {rdata2[47:0], rdata1[63:48]}; end
      0'b111  : begin rdata_0 = {rdata2[55:0], rdata1[63:56]}; end
      default : begin rdata_0 = 64'd0; end
    endcase
    sig_memread_ok = 1; 
  end
  else begin
    rdata_0 = 0;
    sig_memread_ok = 0;
  end
end

// 从8字节中摘出需要读取的数据
always @(*) begin
  if (ren) begin
    case (funct3)
    `FUNCT3_LB    : rdata = $signed(rdata_0[7:0]);
    `FUNCT3_LH    : rdata = $signed(rdata_0[15:0]);
    `FUNCT3_LW    : rdata = $signed(rdata_0[31:0]);
    `FUNCT3_LD    : rdata = $signed(rdata_0[63:0]);
    `FUNCT3_LBU   : rdata = rdata_0[7:0];
    `FUNCT3_LHU   : rdata = rdata_0[15:0];
    default       : rdata = 0;
    endcase
  end
  else begin
    rdata = 0;
  end
end
assign rdata = rdata_0;

// 计算写入掩码1/2
reg [`BUS_64] wmask1;
reg [`BUS_64] wmask2;
always @(*) begin
  case (byte_offset)
    0'b000  : begin wmask1 = 64'hFFFFFFFF_FFFFFFFF; wmask2 = 64'h00000000_00000000; end
    0'b001  : begin wmask1 = 64'hFFFFFFFF_FFFFFF00; wmask2 = 64'h00000000_000000FF; end
    0'b010  : begin wmask1 = 64'hFFFFFFFF_FFFF0000; wmask2 = 64'h00000000_0000FFFF; end
    0'b011  : begin wmask1 = 64'hFFFFFFFF_FF000000; wmask2 = 64'h00000000_00FFFFFF; end
    0'b100  : begin wmask1 = 64'hFFFFFFFF_00000000; wmask2 = 64'h00000000_FFFFFFFF; end
    0'b101  : begin wmask1 = 64'hFFFFFF00_00000000; wmask2 = 64'h000000FF_FFFFFFFF; end
    0'b110  : begin wmask1 = 64'hFFFF0000_00000000; wmask2 = 64'h0000FFFF_FFFFFFFF; end
    0'b111  : begin wmask1 = 64'hFF000000_00000000; wmask2 = 64'h00FFFFFF_FFFFFFFF; end
    default : begin wmask1 = 64'h00000000_00000000; wmask2 = 64'h00000000_00000000; end
  endcase
end

// 写入数据
always @(posedge clk) begin
    ram_write_helper(show_dbg, addr1, wdata, wmask1, wen);
    ram_write_helper(show_dbg, addr2, wdata, wmask2, wen & ena2);

    if (wen)
      sig_memwrite_ok = 1;

    if (wen && (clk_cnt >= `CLK_CNT_VAL))
      $displayh("  MEMACC: waddr1=", addr1, " wdata1=", wdata, " wmask1=", wmask1, " wen=", wen); 
    if ((wen & ena2) && (clk_cnt >= `CLK_CNT_VAL))
      $displayh("  MEMACC: waddr2=", addr2, " wdata2=", wdata, " wmask2=", wmask2, " wen=", wen, " ena2=", ena2);
end


endmodule