// 4 选 1 MUX - 用条件运算符描述的
module mux4_3(out,in1,in2,in3,in4,ctrl1,ctrl2);
input in1,in2,in3,in4,ctrl1,ctrl2;
output out;

assign out = ctrl1 ? (ctrl2 ? in4 : in3) : (ctrl2 ? in2 : in1);

endmodule
