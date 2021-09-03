
`include "defines.v"

module regfile(
    input  wire clk,
	input  wire rst,
	
	input  wire  [4  : 0] w_addr,
	input  wire  [`REG_BUS] w_data,
	input  wire 		  w_ena,
	
	input  wire  [4  : 0] r_addr1,
	output reg   [`REG_BUS] r_data1,
	input  wire 		  r_ena1,
	
	input  wire  [4  : 0] r_addr2,
	output reg   [`REG_BUS] r_data2,
	input  wire 		  r_ena2,

	output wire [`REG_BUS] regs_o[0 : 31]        // difftest
    );

    // 32 registers
	reg [`REG_BUS] 	regs[0 : 31];

  // register alias name
  wire [`REG_BUS] x01_zero  = regs[01];
  wire [`REG_BUS] x02_ra    = regs[02];
  wire [`REG_BUS] x03_sp    = regs[03];
  wire [`REG_BUS] x04_gp    = regs[04];
  wire [`REG_BUS] x05_tp    = regs[05];
  wire [`REG_BUS] x06_t0    = regs[06];
  wire [`REG_BUS] x07_t1    = regs[07];
  wire [`REG_BUS] x08_s0    = regs[08];
  wire [`REG_BUS] x09_s1    = regs[09];
  wire [`REG_BUS] x10_a0    = regs[10];
  wire [`REG_BUS] x11_a1    = regs[11];
  wire [`REG_BUS] x12_a2    = regs[12];
  wire [`REG_BUS] x13_a3    = regs[13];
  wire [`REG_BUS] x14_a4    = regs[14];
  wire [`REG_BUS] x15_a5    = regs[15];
  wire [`REG_BUS] x16_a6    = regs[16];
  wire [`REG_BUS] x17_a7    = regs[17];
  wire [`REG_BUS] x18_s2    = regs[18];
  wire [`REG_BUS] x19_s3    = regs[19];
  wire [`REG_BUS] x20_s4    = regs[20];
  wire [`REG_BUS] x21_s5    = regs[21];
  wire [`REG_BUS] x22_s6    = regs[22];
  wire [`REG_BUS] x23_s7    = regs[23];
  wire [`REG_BUS] x24_s8    = regs[24];
  wire [`REG_BUS] x25_s9    = regs[25];
  wire [`REG_BUS] x26_s10   = regs[26];
  wire [`REG_BUS] x27_s11   = regs[27];
  wire [`REG_BUS] x28_t3    = regs[28];
  wire [`REG_BUS] x29_t4    = regs[29];
  wire [`REG_BUS] x30_t5    = regs[30];
  wire [`REG_BUS] x31_56    = regs[31];

	
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
			if ((w_ena == 1'b1) && (w_addr != 5'h00))	
				regs[w_addr] <= w_data;
		end
	end
	
	always @(*) begin
		if (rst == 1'b1)
			r_data1 = `ZERO_WORD;
		else if (r_ena1 == 1'b1)
			r_data1 = regs[r_addr1];
		else
			r_data1 = `ZERO_WORD;
	end
	
	always @(*) begin
		if (rst == 1'b1)
			r_data2 = `ZERO_WORD;
		else if (r_ena2 == 1'b1)
			r_data2 = regs[r_addr2];
		else
			r_data2 = `ZERO_WORD;
	end

	genvar i;
	generate
		for (i = 0; i < 32; i = i + 1) begin
			assign regs_o[i] = (w_ena & w_addr == i & i != 0) ? w_data : regs[i];
		end
	endgenerate

endmodule
