// ZhengpuShi

`include "defines.v"


// 内存读取控制器，将1字节访问转换为8字节对齐的一次或两次访问
module mem_access (
  input   wire              clk,
  input   wire  [`BUS_64]   addr,     // 以字节为单位的访存地址

  input   wire              ren,      // 读使能
  output  wire  [`BUS_64]   rdata,    // 读到的数据

  input   wire  [`BUS_64]   wdata,    // 写入数据
  input   wire  [`BUS_64]   wmask,    // 写入数据的掩码
  input   wire              wen       // 写使能
);


// 是否需要访问第二个64bit单元
wire ena2 = (addr[2:0] == 3'b000) ? 1 : 0;

// 除去基地址后的相对地址
wire [`BUS_64] addr_rel = addr - 64'h00000000_80000000;

// 第1/2次访存地址
wire [`BUS_64] addr1_dbg = addr_rel >> 3;
wire [`BUS_64] addr2_dbg = addr1_dbg | 64'b1; 
wire [`BUS_64] addr1 = 0;//addr_rel >> 3;
wire [`BUS_64] addr2 = 0;// addr1 | 64'b1;

// 8字节编址的内部偏移量（字节数）
wire [2:0] byte_offset = addr[2:0];         

// 读取数据
wire [`BUS_64] rdata1 = ram_read_helper(ren, addr1);
wire [`BUS_64] rdata2 = ram_read_helper(ren & ena2, addr2);

// 合成读取数据
reg [`BUS_64] rdata_0;
always @(*) begin
  case (byte_offset)
    0'b000  : begin rdata_0 = {rdata1}; end
    0'b001  : begin rdata_0 = {rdata2[ 7:0], rdata1[63: 8]}; end
    0'b010  : begin rdata_0 = {rdata2[15:0], rdata1[63:16]}; end
    0'b011  : begin rdata_0 = {rdata2[31:0], rdata1[63:32]}; end
    0'b100  : begin rdata_0 = {rdata2[39:0], rdata1[63:40]}; end
    0'b101  : begin rdata_0 = {rdata2[47:0], rdata1[63:48]}; end
    0'b110  : begin rdata_0 = {rdata2[55:0], rdata1[63:56]}; end
    0'b111  : begin rdata_0 = {rdata2}; end
    default : begin rdata_0 = 64'd0; end
  endcase
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
    ram_write_helper(addr1, wdata, wmask1, wen);
    ram_write_helper(addr2, wdata, wmask2, wen & ena2);
end


endmodule