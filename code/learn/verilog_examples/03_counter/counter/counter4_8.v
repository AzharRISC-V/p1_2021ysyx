// 模为60的BCD码加法计数器
module cnt60(qout,cout,data,load,cin,rst,clk);
output [7:0] qout;      // 数据输出
output cout;            // 进位标志
input [7:0] data;      // 初始数据
input load,cin,rst,clk; // 装填标志，进位输入，复位，时钟
reg [7:0] qout;

always @(posedge clk) begin
    if (rst)
        qout <= 0;      // 同步复位
    else if (load)
        qout <= data;   // 同步置位
    else if (cin) begin
        if (qout[3:0]===9) begin    // 低4位是否为9，是则
            qout[3:0] <= 0;     // 置0，并判断高4位是否为5
            if (qout[7:4] === 5)
                qout[7:4] <= 0;
            else
                qout[7:4] <= qout[7:4] + 1;
        end
        else    // 低4位不为9，则增加
            qout[3:0] <= qout[3:0] + 1;    
    end
end

assign cout = ((qout == 8'h59) & cin) ? 1 : 0;  // 产生进位输出信号

endmodule


