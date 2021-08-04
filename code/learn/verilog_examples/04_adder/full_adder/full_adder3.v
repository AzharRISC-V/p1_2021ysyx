// 1 位全加器 - 数据流描述的
module full_adder3(a,b,cin,sum,cout);
input a,b,cin;
output sum,cout;
assign {cout,sum} = a + b + cin;
endmodule

