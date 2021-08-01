// D 触发器 -- 三态控制端 8 位
module d_reg(q,d,oe,g);
output [7:0] q;     // 输出输出端
input [7:0] d;      // 数据输入端
input oe,g;       // 三态控制端（输出使能）、控制信号
reg [7:0] q;

always @(*) begin
    if (oe) begin
        q <= 8'bz;
    end
    else begin
        if (g) begin
            q <= d;
        end
    end
        
end

endmodule
