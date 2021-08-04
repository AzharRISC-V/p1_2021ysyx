// 4 位级联全加器 - 数据流描述的
module full_adder4_2(sum,cout,a,b,cin);
output [3:0] sum;
output cout;
input [3:0] a,b;
input cin;

assign {cout,sum} = a + b + cin;

endmodule

