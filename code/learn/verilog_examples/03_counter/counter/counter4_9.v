// 减法计数器，9~0
module sub_cnt10(qout,clk,rst);
output [3:0] qout;      // 数据输出
input rst,clk;          // 复位，时钟
reg [3:0] qout;

always @(posedge clk) begin
    if (rst)
        qout <= 0;      // 同步复位
    else if (qout === 4'b0000)
        qout <= 4'b1001;
    else
        qout <= qout - 1;
end

endmodule


