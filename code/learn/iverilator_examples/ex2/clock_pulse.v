`timescale 10ns/1ns      // 时间单位10ns，时间精度1ns
module clock_pulse;
    reg clk;

    initial begin
        $display("start a clock pulse");
        $dumpfile("wave.vcd");
        $dumpvars(0, clock_pulse);
        clk <= 1;     // 初始 clock 信号为1
        #6000 $finish;      // 延时后结束模拟
    end

    always begin
        #20 clk = !clk;
    end
    
endmodule //clock_pulse