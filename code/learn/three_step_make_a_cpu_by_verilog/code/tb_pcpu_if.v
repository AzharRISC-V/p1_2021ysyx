// 测试 IF 

`timescale 1ns/1ns
`include "pcpu.v"

module pcpu_tb();

    parameter DELAY = 20;

    reg clk, ena, rst_n, start;
    reg [15:0] i_datain, d_datain;
    wire [7:0] i_addr, d_addr;
    wire d_we;
    wire [15:0] d_dataout;

    pcpu u1(
        .clk            (clk        ),
        .ena            (ena        ),
        .rst_n          (rst_n      ),
        .start          (start      ),
        .i_datain       (i_datain   ),
        .d_datain       (d_datain   ),
        .i_addr         (i_addr     ),
        .d_addr         (d_addr     ),
        .d_we           (d_we       ),
        .d_dataout      (d_dataout  )
        );

    always #(DELAY/2) clk = ~clk;

    initial begin
        clk = 0; ena = 0; rst_n = 0; start = 0;
        i_datain = 0; d_datain = 0;
        
        #DELAY rst_n = 1;   // 复位完成
        #DELAY ena = 1; start = 1;  // 开机
        
        #(DELAY*20) $finish;
    end

    // 打印信号
    initial 
        $monitor($time, ":rst=%b clk=%b ena=%d start=%d", rst_n,clk,ena,start);

    // 生成vcd波形文件
    initial begin
        $dumpfile("./build/tb_pcpu_IF.vcd");
        $dumpvars(0, pcpu_tb);
        #10000 $finish;
    end
    
endmodule