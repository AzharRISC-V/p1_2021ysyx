// 4 选 1 MUX (多路复用器、数据选择器) - 用 case 语句描述
module mux4_1(out,in1,in2,in3,in4,ctrl1,ctrl2);
input in1,in2,in3,in4,ctrl1,ctrl2;
output out;
reg out;

always @(in1 or in2 or in3 or in4 or ctrl1 or ctrl2)   // 敏感信号列表
    case ({ctrl1,ctrl2})
    2'b00: out = in1;
    2'b01: out = in2;
    2'b10: out = in3;
    2'b11: out = in4;
    default : out = 2'bx;
    endcase

endmodule
