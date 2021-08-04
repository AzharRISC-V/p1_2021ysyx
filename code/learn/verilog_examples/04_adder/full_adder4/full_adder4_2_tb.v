`timescale 1ns/1ns
`include "full_adder4_2.v"

module full_adder4_2_tb;
reg [3:0] a,b;
reg cin;
wire [3:0] sum;
wire cout;
integer i,j;
parameter DELAY = 20;

full_adder4_2 u1(sum,cout,a,b,cin);

always #(DELAY)     cin = ~cin;

initial begin
    a = 0; b = 0; cin = 0;
    for (i = 1; i < 16; i = i + 1)
        #DELAY a = i;
end

initial begin
    for (j = 1; j < 16; j = j + 1)
        #(DELAY*2) b = j;
end

// 打印信号
initial begin 
    $monitor($time, ": %d + %d + %b = {%b,%d}",
        a,b,cin,cout,sum);
    
    #(DELAY*100) $finish;
end

// 生成vcd波形文件
initial begin
    $dumpfile("./build/full_adder4_2_wave.vcd");
    $dumpvars(0, full_adder4_2_tb);
end

endmodule

