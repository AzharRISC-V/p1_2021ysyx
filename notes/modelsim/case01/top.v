module top (
	input	clk,
	input	rst,
	output	reg [3:0] out);

	always @(posedge clk) begin
		out <= rst ? 0 : out + 1;
	end
	
endmodule
