// 4位计数器的仿真程序
`timescale 1ns/1ns
`include "counter4_7.v"
module counter4_7_tb;
reg clk,clr;
wire [3:0] ten,one;
wire co;
parameter DELAY = 20;

cnt24 uc(ten,one,co,clk,clr);

always #(DELAY/2) clk = ~clk;

initial begin
            clk = 0;
            clr = 0;
    #DELAY  clr = 1;
    #DELAY  clr = 0;
    #(DELAY*50)
            $finish;
end

// 打印信号
initial 
    $monitor($time, ": clr=%b clk=%b co=%d ten=%d one=%d", clr,clk,co,ten,one);

// 生成vcd波形文件
initial begin
    $dumpfile("./build/counter4_7_wave.vcd");
    $dumpvars(0, counter4_7_tb);  // 指定层次数为0，顶层模块为 counter4_tb
    #10000 $finish;
end

endmodule

