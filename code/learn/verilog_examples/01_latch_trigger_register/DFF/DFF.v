// 基本 D 触发器
module DFF(Q,D,clk);
output Q;
input D,clk;
reg Q;

always @(posedge clk) begin
    Q <= D;
end

endmodule
