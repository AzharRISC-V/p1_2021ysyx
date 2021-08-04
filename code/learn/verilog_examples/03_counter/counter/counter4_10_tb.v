// 仿真程序
`timescale 1ns/1ns
`include "counter4_10.v"
module counter4_10_tb;
reg clk,clr;        // 时钟、复位
reg [7:0] m;        // 模值
wire [7:0] q;       // 输出
parameter DELAY = 20;

mchange_1 uc(q,clk,clr,m);

always #(DELAY/2) clk = ~clk;

initial begin
            m = 10; clk = 0; clr = 0;
    // 模拟 clr 信号
    #DELAY  clr = 1;
    #DELAY  clr = 0;
    // 模拟 不同的模值
    #(DELAY*20) m = 20;
    #(DELAY*40) m = 30;
    #(DELAY*50) $finish;
end

// 打印信号
initial 
    $monitor($time, ": clk=%b clr=%b m=%d q=%d", 
        clk,clr,m,q);

// 生成vcd波形文件
initial begin
    $dumpfile("./build/counter4_10_wave.vcd");
    $dumpvars(0, counter4_10_tb);  // 指定层次数为0，顶层模块为 xx
end

endmodule
