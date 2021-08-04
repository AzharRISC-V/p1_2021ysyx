// for语句乘法器
module mult_for(outcome,a,b);
    parameter size = 8;
    input [size:1] a,b;         // 两个操作数
    output [2*size:1] outcome;  // 结果
    reg [2*size:1] outcome;
    integer i;
    always @(a or b) begin
        outcome = 0;
        for (i = 1; i < size; i = i + 1)
            if (b[i])
                outcome = outcome + (a << (i - 1));
    end

endmodule
