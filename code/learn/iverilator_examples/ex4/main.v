`include "v1.v"
`include "v2.v"
`include "v3.v"
`include "./folder/v4.v"

`timescale 10ns/10ns

module main ();
    reg clk;

    initial begin
        clk <= 0;
        #100 $finish;
    end

    v1 u_v1();
    v2 u_v2();
    v3 u_v3();
    v4 u_v4(clk);

    always
        #10 clk = !clk;
endmodule //main