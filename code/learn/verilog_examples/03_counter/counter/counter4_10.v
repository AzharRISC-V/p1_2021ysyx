// 模值可变计数器
module mchange_1(q,clk,clr,m);
output [7:0] q;         // 数据输出
input clk,clr;          // 时钟，复位
input [7:0] m;          // 模值
reg [7:0] q;
reg [7:0] md;           // 模值-1

always @(posedge clk) begin
    md <= m - 1;
    if (clr)
        q <= 0;
    else begin
        if (q == md)
            q <= 0;
        else
            q <= q + 1;
    end
end

endmodule


