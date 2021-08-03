// 4 选 1 MUX - 用门元件实现的
module mux4_2(out,in1,in2,in3,in4,ctrl1,ctrl2);
input in1,in2,in3,in4,ctrl1,ctrl2;
output out;

wire ctrl1n, ctrl2n, w, x, y, z;
not (ctrl1n,ctrl1), 
    (ctrl2n,ctrl2);
and (w,in1,ctrl1n,ctrl2n),
    (x,in2,ctrl1n,ctrl2),
    (y,in3,ctrl1,ctrl2n),
    (z,in4,ctrl1,ctrl2);
or (out,w,x,y,z);

endmodule
