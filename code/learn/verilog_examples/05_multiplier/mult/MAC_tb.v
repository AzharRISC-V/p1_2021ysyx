`timescale 1ns/1ns
`include "MAC.v"
module MAC_tb;
    reg [7:0] a,b;
    reg clr,clk;
    wire [15:0] out;
    parameter DELAY = 20;

    MAC u1(out,a,b,clk,clr);

    always #(DELAY) clk = ~clk;

    // 激励信号定义
    initial begin
        clr = 1; clk = 0; a = 8'd0; b = 8'd0;
        #DELAY clr = 0; a = 8'd1; b = 8'd10;
        #DELAY a = 8'd2;
        #DELAY a = 8'd3;
        #DELAY a = 8'd4;
        #DELAY a = 8'd5;
        #DELAY a = 8'd6;
        #DELAY a = 8'd7;
        #DELAY a = 8'd8;
        #DELAY a = 8'd9;
        #DELAY a = 8'd10;
        #DELAY $finish;
    end

    // 打印信号
    initial 
        $monitor($time, ": clr=%b clk=%b a=%d b=%d out=%d", clr,clk,a,b,out);

    // 生成vcd波形文件
    initial begin
        $dumpfile("./build/MAC_tb_wave.vcd");
        $dumpvars(0, MAC_tb);
    end
endmodule //MAC_tb