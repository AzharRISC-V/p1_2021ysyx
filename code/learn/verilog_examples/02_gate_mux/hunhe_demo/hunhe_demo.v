// 与非门 -- 结构 与 描述 的混合
module hunhe_demo(A,B,C);
input A,B;
output C;
// 定义中间变量
wire T;
// 调用结构化的与门
and A1(T,A,B);      // T = A & B;
// 描述形式的非门
assign C = ~T;

endmodule
