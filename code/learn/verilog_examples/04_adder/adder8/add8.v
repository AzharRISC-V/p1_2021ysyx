// 8 位全加器
module add8(sum,cout,a,b,cin);
    output [7:0] sum;
    output cout;
    input [7:0] a,b;
    input cin;

    assign {cout,sum} = a + b + cin;
endmodule
