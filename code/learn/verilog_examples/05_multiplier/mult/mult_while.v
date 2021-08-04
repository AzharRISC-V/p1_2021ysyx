// while语句乘法器
module mult_while(outcome,a,b);
    parameter size = 8;
    input [size:1] a,b;         // 两个操作数
    output [2*size:1] outcome;  // 结果
    reg [2*size:1] outcome;
    integer i;
    always @(a or b) begin
        outcome = 0;
        i = 1;
        while (i <= size) begin
            if (b[i]) begin
                outcome = outcome + (a << (i - 1));
            end
            i = i + 1;
        end
    end

endmodule
