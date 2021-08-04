// 4 位级联全加器 - 结构描述的
`include "../full_adder/full_adder1.v"

module full_adder4_1(sum,cout,a,b,cin);
output [3:0] sum;
output cout;
input [3:0] a,b;
input cin;
wire cin1,cin2,cin3;

full_adder1 f0(a[0],b[0],cin,   sum[0],cin1);
full_adder1 f1(a[1],b[1],cin1,  sum[1],cin2);
full_adder1 f2(a[2],b[2],cin2,  sum[2],cin3);
full_adder1 f3(a[3],b[3],cin3,  sum[3],cout);

endmodule

