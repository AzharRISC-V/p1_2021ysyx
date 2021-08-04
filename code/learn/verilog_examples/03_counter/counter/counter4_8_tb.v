// 仿真程序
`timescale 1ns/1ns
`include "counter4_8.v"
module counter4_8_tb;
reg clk,rst,load,cin;       // 时钟、复位、装填、进位输入
reg [7:0] data;
wire [7:0] qout;
wire cout;
parameter DELAY = 20;

cnt60 uc(qout,cout,data,load,cin,rst,clk);

always #(DELAY/2) clk = ~clk;

// 模拟 cin 信号
always #(DELAY*5) cin = ~cin;

initial begin
            clk = 0; rst = 0; load = 0; cin = 0; data = 8'h24;
    #DELAY  rst = 1;
    #DELAY  rst = 0;
    #(DELAY*11) load = 1;   // 运行一阵子后，模拟load信号
    #DELAY  load = 0;
    #(DELAY*200) $finish;    // 常规计数时序
end

// 打印信号
initial 
    $monitor($time, ": rst=%b clk=%b load=%b data=%d cin=%b cout=%b qout=0x%X", 
        rst,clk,load,data,cin,cout,qout);

// 生成vcd波形文件
initial begin
    $dumpfile("./build/counter4_8_wave.vcd");
    $dumpvars(0, counter4_8_tb);  // 指定层次数为0，顶层模块为 xx
end

endmodule
