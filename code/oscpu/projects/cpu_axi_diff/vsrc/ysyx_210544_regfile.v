
// ZhengpuShi

`include "defines.v"

module ysyx_210544_regfile(
  input   wire                  clk,
  input   wire                  rst,

  input   wire  [`YSYX210544_BUS_RIDX]     i_rs1,
  input   wire                  i_rs1_ren,
  input   wire  [`YSYX210544_BUS_RIDX]     i_rs2,
  input   wire                  i_rs2_ren,
  input   wire  [`YSYX210544_BUS_RIDX]     i_rd,
  input   wire                  i_rd_wen,
  input   wire  [`YSYX210544_BUS_64]       i_rd_data,
  output  reg   [`YSYX210544_BUS_64]       o_rs1_data,
  output  reg   [`YSYX210544_BUS_64]       o_rs2_data

`ifdef YSYX210544_DIFFTEST_FLAG
    ,
  output  wire  [`YSYX210544_BUS_64]       o_regs[0:31]
`endif
);

reg [`YSYX210544_BUS_64] regs[0:31];

`ifdef YSYX210544_DIFFTEST_FLAG

// difftest regs接口
genvar i;
generate
    for (i = 0; i < 32; i = i + 1) 
    begin: O_REGS_GEN
        assign o_regs[i] = ((i_rd_wen) && (i_rd == i) && (i != 0)) ? i_rd_data : regs[i];
    end
endgenerate

// register alias name
wire  [`YSYX210544_BUS_64]   x00_zero;
wire  [`YSYX210544_BUS_64]   x01_ra;
wire  [`YSYX210544_BUS_64]   x02_sp;
wire  [`YSYX210544_BUS_64]   x03_gp;
wire  [`YSYX210544_BUS_64]   x04_tp;
wire  [`YSYX210544_BUS_64]   x05_t0;
wire  [`YSYX210544_BUS_64]   x06_t1;
wire  [`YSYX210544_BUS_64]   x07_t2;
wire  [`YSYX210544_BUS_64]   x08_s0;
wire  [`YSYX210544_BUS_64]   x09_s1;
wire  [`YSYX210544_BUS_64]   x10_a0;
wire  [`YSYX210544_BUS_64]   x11_a1;
wire  [`YSYX210544_BUS_64]   x12_a2;
wire  [`YSYX210544_BUS_64]   x13_a3;
wire  [`YSYX210544_BUS_64]   x14_a4;
wire  [`YSYX210544_BUS_64]   x15_a5;
wire  [`YSYX210544_BUS_64]   x16_a6;
wire  [`YSYX210544_BUS_64]   x17_a7;
wire  [`YSYX210544_BUS_64]   x18_s2;
wire  [`YSYX210544_BUS_64]   x19_s3;
wire  [`YSYX210544_BUS_64]   x20_s4;
wire  [`YSYX210544_BUS_64]   x21_s5;
wire  [`YSYX210544_BUS_64]   x22_s6;
wire  [`YSYX210544_BUS_64]   x23_s7;
wire  [`YSYX210544_BUS_64]   x24_s8;
wire  [`YSYX210544_BUS_64]   x25_s9;
wire  [`YSYX210544_BUS_64]   x26_s10;
wire  [`YSYX210544_BUS_64]   x27_s11;
wire  [`YSYX210544_BUS_64]   x28_t3;
wire  [`YSYX210544_BUS_64]   x29_t4;
wire  [`YSYX210544_BUS_64]   x30_t5;
wire  [`YSYX210544_BUS_64]   x31_t6;

assign x00_zero = regs[00];
assign x01_ra   = regs[01];
assign x02_sp   = regs[02];
assign x03_gp   = regs[03];
assign x04_tp   = regs[04];
assign x05_t0   = regs[05];
assign x06_t1   = regs[06];
assign x07_t2   = regs[07];
assign x08_s0   = regs[08];
assign x09_s1   = regs[09];
assign x10_a0   = regs[10];
assign x11_a1   = regs[11];
assign x12_a2   = regs[12];
assign x13_a3   = regs[13];
assign x14_a4   = regs[14];
assign x15_a5   = regs[15];
assign x16_a6   = regs[16];
assign x17_a7   = regs[17];
assign x18_s2   = regs[18];
assign x19_s3   = regs[19];
assign x20_s4   = regs[20];
assign x21_s5   = regs[21];
assign x22_s6   = regs[22];
assign x23_s7   = regs[23];
assign x24_s8   = regs[24];
assign x25_s9   = regs[25];
assign x26_s10  = regs[26];
assign x27_s11  = regs[27];
assign x28_t3   = regs[28];
assign x29_t4   = regs[29];
assign x30_t5   = regs[30];
assign x31_t6   = regs[31];

`endif

// i_rd 写入
always @(posedge clk) begin
  if (rst) begin
    regs[ 0] <= `YSYX210544_ZERO_WORD;
    regs[ 1] <= `YSYX210544_ZERO_WORD;
    regs[ 2] <= `YSYX210544_ZERO_WORD;
    regs[ 3] <= `YSYX210544_ZERO_WORD;
    regs[ 4] <= `YSYX210544_ZERO_WORD;
    regs[ 5] <= `YSYX210544_ZERO_WORD;
    regs[ 6] <= `YSYX210544_ZERO_WORD;
    regs[ 7] <= `YSYX210544_ZERO_WORD;
    regs[ 8] <= `YSYX210544_ZERO_WORD;
    regs[ 9] <= `YSYX210544_ZERO_WORD;
    regs[10] <= `YSYX210544_ZERO_WORD;
    regs[11] <= `YSYX210544_ZERO_WORD;
    regs[12] <= `YSYX210544_ZERO_WORD;
    regs[13] <= `YSYX210544_ZERO_WORD;
    regs[14] <= `YSYX210544_ZERO_WORD;
    regs[15] <= `YSYX210544_ZERO_WORD;
    regs[16] <= `YSYX210544_ZERO_WORD;
    regs[17] <= `YSYX210544_ZERO_WORD;
    regs[18] <= `YSYX210544_ZERO_WORD;
    regs[19] <= `YSYX210544_ZERO_WORD;
    regs[20] <= `YSYX210544_ZERO_WORD;
    regs[21] <= `YSYX210544_ZERO_WORD;
    regs[22] <= `YSYX210544_ZERO_WORD;
    regs[23] <= `YSYX210544_ZERO_WORD;
    regs[24] <= `YSYX210544_ZERO_WORD;
    regs[25] <= `YSYX210544_ZERO_WORD;
    regs[26] <= `YSYX210544_ZERO_WORD;
    regs[27] <= `YSYX210544_ZERO_WORD;
    regs[28] <= `YSYX210544_ZERO_WORD;
    regs[29] <= `YSYX210544_ZERO_WORD;
    regs[30] <= `YSYX210544_ZERO_WORD;
    regs[31] <= `YSYX210544_ZERO_WORD;
  end
  else begin
    // if ((w_ena) && (w_addr != 5'h00))    
    //     regs[w_addr] <= w_data;
      
    if (i_rd_wen && (i_rd != 5'h00))
      regs[i_rd] <= i_rd_data;
  end
end

// i_rs1 读取
always @(*) begin
  if (rst)
    o_rs1_data = `YSYX210544_ZERO_WORD;
  else if (i_rs1_ren)
    o_rs1_data = regs[i_rs1];
  else
    o_rs1_data = `YSYX210544_ZERO_WORD;
end

// i_rs2 读取
always @(*) begin
  if (rst)
    o_rs2_data = `YSYX210544_ZERO_WORD;
  else if (i_rs2_ren)
    o_rs2_data = regs[i_rs2];
  else
    o_rs2_data = `YSYX210544_ZERO_WORD;
end

//wire _unused_ok = &{1'b0,
//  x00_zero,
//  x01_ra,
//  x02_sp,
//  x03_gp,
//  x04_tp,
//  x05_t0,
//  x06_t1,
//  x07_t2,
//  x08_s0,
//  x09_s1,
//  x10_a0,
//  x11_a1,
//  x12_a2,
//  x13_a3,
//  x14_a4,
//  x15_a5,
//  x16_a6,
//  x17_a7,
//  x18_s2,
//  x19_s3,
//  x20_s4,
//  x21_s5,
//  x22_s6,
//  x23_s7,
//  x24_s8,
//  x25_s9,
//  x26_s10,
//  x27_s11,
//  x28_t3,
//  x29_t4,
//  x30_t5,
//  x31_t6,
//  1'b0};

endmodule
