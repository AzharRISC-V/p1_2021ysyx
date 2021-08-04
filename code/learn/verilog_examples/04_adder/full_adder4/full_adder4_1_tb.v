`timescale 1ns/1ns
`include "full_adder4_1.v"

module full_adder4_1_tb;
reg [3:0] a,b;
reg cin;
wire [3:0] sum;
wire cout;
parameter DELAY = 20;

full_adder4_1 u1(sum,cout,a,b,cin);

always #(DELAY)     cin = ~cin;

always #(DELAY*2)   a = a + 1;

always #(DELAY*5)   b = b + 1;

initial begin
            a = 0; b = 0; cin = 0;
    #(DELAY*100)  $finish;
end

// 打印信号
initial 
    $monitor($time, ": (a,b,cin)=(%d,%d,%d), (cout,sum)=(%d,%d)",
        a,b,cin,cout,sum);

// 生成vcd波形文件
initial begin
    $dumpfile("./build/full_adder4_1_wave.vcd");
    $dumpvars(0, full_adder4_1_tb);
end

endmodule

