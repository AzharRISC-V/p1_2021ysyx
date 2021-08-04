// 4位计数器的仿真程序
`timescale 1ns/1ns
`include "counter4_3.v"
module counter4_3_tb;
reg clk,rst,r,s,en;
reg [3:0] d;
wire [3:0] q;
wire co;

parameter DELAY = 20;

counter4_3 uc4(co,q,clk,r,s,en,d);

// 模拟时钟信号
always #(DELAY/2) clk = ~clk;

// 模拟控制信号
initial begin
            clk = 0; r = 0; s = 0; en = 0; d = 4'b1010;
    #DELAY  en = 1;
    #DELAY  r = 1; s = 0;
    #DELAY  r = 1; s = 1;
    #DELAY  r = 0; s = 1;
    #DELAY  r = 0; s = 0;
    #(DELAY*40) $finish;
end

// 打印信号
initial 
    $monitor($time, " :en=%b rst=%b set=%b init-val=%d cout=%b qout=%d", en,r,s,d,co,q);

// 生成vcd波形文件
initial begin
    $dumpfile("./build/counter4_3_wave.vcd");
    $dumpvars(0, counter4_3_tb);  // 指定层次数为0，顶层模块为 xx
end

endmodule

