// 带置位和复位端的 电平敏感的 1 位 数据锁存器
module latch_2(q,d,clk,set,rst);
input d,clk,set,rst;
output q;
assign q = rst ? 0 : (set ? 1 : (clk ? d : q));

endmodule
