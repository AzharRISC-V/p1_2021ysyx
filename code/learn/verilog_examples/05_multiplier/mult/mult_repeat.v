// repeat语句乘法器 （注意，repeat不能综合）
module mult_repeat(outcome,a,b);
    parameter size = 8;
    input [size:1] a,b;         // 两个操作数
    output [2*size:1] outcome;  // 结果
    reg [2*size:1] outcome;
    integer i;
    always @(a or b) begin
        outcome = 0;
        i = 0;
        repeat (8) begin
            if (b[i])
                outcome = outcome + (a << (i - 1));
            i = i + 1;
        end
    end

endmodule
