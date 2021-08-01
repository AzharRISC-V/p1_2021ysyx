// 8 位数据锁存器
module latch_8(qout,data,clk);
input [7:0] data;
output [7:0] qout;
input clk;
reg [7:0] qout;
always @(clk or data) begin
    if (clk)
        qout <= data;
end

endmodule
