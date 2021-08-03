`timescale 1ns/1ns      // 时间单位1ns，时间精度1ns
module tb_mut2;
    reg a,b,s;  // 激励变量为reg，以保证激励持续保持不变
    wire out;

    // 实例化
    mut2 u1(.out(out), .a(a), .b(b), .sel(s));

    // 行为描述语句
    // 描述输入信号
    initial begin
        a = 0; b = 0; s = 0;
    #10 a = 0; b = 1; s = 0;
    #10 a = 1; b = 0; s = 0;
    #10 a = 1; b = 1; s = 0;
    #10 a = 0; b = 0; s = 1;
    #10 a = 0; b = 1; s = 1;
    #10 a = 1; b = 0; s = 1;
    #10 a = 1; b = 1; s = 1;
    end

    // 描述输出信号
    initial 
        $monitor($time, ":a=%b b=%b s=%b out=%b", a, b, s, out);
    
    // 生成vcd波形文件
    initial begin
        $dumpfile("./build/wave.vcd");
        $dumpvars(0, tb_mut2);  // 指定层次数为0，顶层模块为tb_code
        #10000 $finish;
    end

endmodule //tb_mut2