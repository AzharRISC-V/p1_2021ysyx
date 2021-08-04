// 1 位半加器 - 数据流方式描述的
module half_adder2(a,b,sum,cout);
input a,b;
output sum,cout;
assign sum = a ^ b;
assign cout = a & b;
endmodule

