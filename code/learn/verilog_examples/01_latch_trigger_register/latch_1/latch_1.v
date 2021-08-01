// 电平敏感的 1 位数据锁存器
module latch_1(q,d,clk);
input d,clk;
output q;
assign q = clk ? d : q;     // 时钟信号高电平时，将输入端数据锁存

endmodule
