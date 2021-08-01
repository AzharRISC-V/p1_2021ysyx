// T 触发器
module t(q,t,clk);
input t,clk;
output q;
reg q;

always @(posedge clk) begin
    if (t) begin
        q <= ~q;
    end
end

endmodule
