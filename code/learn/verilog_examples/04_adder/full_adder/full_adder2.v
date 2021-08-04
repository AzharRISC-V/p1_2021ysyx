// 1 位全加器 - 数据流描述的
module full_adder2(a,b,cin,sum,cout);
input a,b,cin;
output sum,cout;
assign sum = a ^ b ^ cin;
assign cout = (a & b) | (b & cin) | (a & cin);
endmodule

