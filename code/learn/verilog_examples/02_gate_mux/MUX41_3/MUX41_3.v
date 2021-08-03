// 4 选 1 MUX - 数据流方式描述的
module mux4_3(out,in1,in2,in3,in4,ctrl1,ctrl2);
input in1,in2,in3,in4,ctrl1,ctrl2;
output out;

assign out = (in1 & ~ctrl1 & ~ctrl2) |
    (in2 & ~ctrl1 & ctrl2) |
    (in3 & ctrl1 & ~ctrl2) |
    (in4 & ctrl1 & ctrl2);

endmodule
