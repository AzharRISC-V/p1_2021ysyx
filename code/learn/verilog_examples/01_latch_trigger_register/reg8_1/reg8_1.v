// D 触发器 -- 三态控制端 8 位
module reg8_1(q,d,oe,clk);
output [7:0] q;     // 输出输出端
input [7:0] d;      // 数据输入端
input oe,clk;       // 三态控制端（输出使能）、时钟信号
reg [7:0] q;

always @(posedge clk) begin
    if (oe) begin
        q <= 8'bz;
    end
    else begin
        q <= d;
    end
        
end

endmodule
