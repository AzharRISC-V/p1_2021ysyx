`timescale 1ns/1ns		// time unit / time precision

module flow_led_tb();

// parameter define
parameter T = 20;		// time cycle, 20ns

// reg define
reg sys_clk;
reg sys_rst_n;

// wire define
wire [3:0] led;

/**********************************************************
	main code
**********************************************************/

// initial input signal
initial begin
	sys_clk				= 1'b0;
	sys_rst_n			= 1'b0;
	#(T+1) sys_rst_n	= 1'b1;		// reset finished at 21ns 
end

// sys_clk generator
// freq = 50Mhz, cycle = 1/50Mhz = 20ns, so, every turn over every 10ns
always #(T/2) sys_clk = ~sys_clk;

// initialize flow_led
flow_led u0_flow_led (
	.sys_clk		(sys_clk),
	.sys_rst_n		(sys_rst_n),
	.led			(led)
);


endmodule
