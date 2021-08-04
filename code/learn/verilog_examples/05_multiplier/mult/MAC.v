// 乘累加器（MAC : Multiply-ACcumulator)
module MAC(out,a,b,clk,clr);
    output [15:0] out;
    input [7:0] a,b;
    input clk,clr;
    wire [15:0] sum;
    reg [15:0] out;

    // mult函数完成乘法操作
    function [15:0] mult;
        input [7:0] a,b;
        reg [15:0] result;
        integer i;

        begin
            result = a[0] ? b : 0;
            for (i = 1; i <= 7; i = i + 1) begin
                if (a[i]) result = result + (b << (i - 1));
            end
            mult = result;
        end
    endfunction

    // 乘累加
    assign sum = mult(a,b) + out;

    // 送出数据
    always @(posedge clk or posedge clr) begin
        if (clr) out <= 0;
        else out <= sum;
    end
endmodule
