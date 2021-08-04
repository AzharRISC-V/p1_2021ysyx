`include "add8.v"

// 累加器顶层连接文本描述
module acc(accout,cout,accin,cin,clk,clear);
    output [7:0] accout;        // acc输出
    output cout;                // 进位输出
    input [7:0] accin;          // acc输入
    input cin,clk,clear;        // 进位输入，时钟，清除
    wire [7:0] sum;

    add8 accadd8(sum,cout,accout,accin,cin);
    reg8 accreg8(accout,sum,clk,clear);

endmodule
