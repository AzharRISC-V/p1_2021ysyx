// 4位计数器的仿真程序
`timescale 1ns/1ns
`include "counter4_1.v"
module counter4_1_tb;
reg clk,rst;
wire [3:0] out;
parameter DELAY = 20;

counter4_1 uc4(out,clk,rst);


always #(DELAY/2) clk = ~clk;

initial begin
            clk = 0; rst = 0;
    #DELAY  rst = 1;
    #DELAY  rst = 0;
    #(DELAY*20)
            $finish;
end

// 打印信号
initial 
    $monitor($time, ":rst=%b clk=%b out=%d", rst,clk,out);

// 生成vcd波形文件
initial begin
    $dumpfile("./build/counter4_1_wave.vcd");
    $dumpvars(0, counter4_1_tb);  // 指定层次数为0，顶层模块为 counter4_tb
    #10000 $finish;
end

endmodule

