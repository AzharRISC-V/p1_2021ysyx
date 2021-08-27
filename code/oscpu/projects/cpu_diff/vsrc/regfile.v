
`include "defines.v"

module regfile(
  input   wire              clk,
  input   wire              rst,
  
  input   wire  [4  : 0]    rs1,
  input   wire              rs1_ren,
  input   wire  [4  : 0]    rs2,
  input   wire              rs2_ren,
  input   wire  [4  : 0]    rd,
  input   wire  [`BUS_64]   rd_data,
  input   wire              rd_wen,

  output  reg   [`BUS_64]   rs1_data,
  output  reg   [`BUS_64]   rs2_data,
  output  wire  [`BUS_64]   regs_o[0 : 31],        // difftest

  output  wire              sig_wb_ok
);

// 32 registers
reg [`BUS_64]   regs[0 : 31];

always @(posedge clk) 
begin
  if ( rst == 1'b1 ) 
  begin
    regs[ 0] <= `ZERO_WORD;
    regs[ 1] <= `ZERO_WORD;
    regs[ 2] <= `ZERO_WORD;
    regs[ 3] <= `ZERO_WORD;
    regs[ 4] <= `ZERO_WORD;
    regs[ 5] <= `ZERO_WORD;
    regs[ 6] <= `ZERO_WORD;
    regs[ 7] <= `ZERO_WORD;
    regs[ 8] <= `ZERO_WORD;
    regs[ 9] <= `ZERO_WORD;
    regs[10] <= `ZERO_WORD;
    regs[11] <= `ZERO_WORD;
    regs[12] <= `ZERO_WORD;
    regs[13] <= `ZERO_WORD;
    regs[14] <= `ZERO_WORD;
    regs[15] <= `ZERO_WORD;
    regs[16] <= `ZERO_WORD;
    regs[17] <= `ZERO_WORD;
    regs[18] <= `ZERO_WORD;
    regs[19] <= `ZERO_WORD;
    regs[20] <= `ZERO_WORD;
    regs[21] <= `ZERO_WORD;
    regs[22] <= `ZERO_WORD;
    regs[23] <= `ZERO_WORD;
    regs[24] <= `ZERO_WORD;
    regs[25] <= `ZERO_WORD;
    regs[26] <= `ZERO_WORD;
    regs[27] <= `ZERO_WORD;
    regs[28] <= `ZERO_WORD;
    regs[29] <= `ZERO_WORD;
    regs[30] <= `ZERO_WORD;
    regs[31] <= `ZERO_WORD;
  end
  else 
  begin
    if (rd_wen && (rd != 5'h00))
      regs[rd] <= rd_data;
  end
end

assign sig_wb_ok = (!rst) & (rd_wen) & (rd != 5'h00);

always @(*) begin
  if (rst == 1'b1)
    rs1_data = `ZERO_WORD;
  else if (rs1_ren == 1'b1)
    rs1_data = regs[rs1];
  else
    rs1_data = `ZERO_WORD;
end

always @(*) begin
  if (rst == 1'b1)
    rs2_data = `ZERO_WORD;
  else if (rs2_ren == 1'b1)
    rs2_data = regs[rs2];
  else
    rs2_data = `ZERO_WORD;
end

genvar i;
generate
  for (i = 0; i < 32; i = i + 1) begin
    assign regs_o[i] = (rd_wen & rd == i & i != 0) ? rd_data : regs[i];
  end
endgenerate

endmodule
