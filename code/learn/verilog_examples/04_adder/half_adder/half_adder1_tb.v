`timescale 1ns/1ns
`include "half_adder1.v"
module half_adder1_tb;
reg a,b;
wire sum,cout;
parameter DELAY = 20;

half_adder1 u1(a,b,sum,cout);

initial begin
            a = 0; b = 0;
    #DELAY  a = 0; b = 1;
    #DELAY  a = 1; b = 0;
    #DELAY  a = 1; b = 1;
    #DELAY  $finish;
end

// 打印信号
initial 
    $monitor($time, ": (a,b)=(%d,%d), (sum,cout)=(%d,%d)",a,b,sum,cout);

// 生成vcd波形文件
initial begin
    $dumpfile("./build/half_adder1_wave.vcd");
    $dumpvars(0, half_adder1_tb);
end

endmodule
