// 8 位并行乘法器
module mult(outcome,a,b);
    parameter size = 8;
    input [size:1] a,b;     // 两个操作数
    output [2*size:1] outcome;  // 结果
    assign outcome = a * b;
endmodule
