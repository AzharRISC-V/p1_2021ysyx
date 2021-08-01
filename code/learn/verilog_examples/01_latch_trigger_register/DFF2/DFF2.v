// 带同步清 0 、同步置 1 的 D 触发器
module DFF2(q,qn,d,clk,setn,rstn);
input d,clk,setn,rstn;
output q,qn;
reg q,qn;

always @(posedge clk) begin
    // 同步清 0，低电平有效
    if (!rstn) begin
        q <= 0;
        qn <= 1;
    end
    // 同步置 1，低电平有效
    else if (!setn) begin
        q <= 1;
        qn <= 0;
    end
    // 时钟上升沿输出改变
    else begin
        q <= d;
        qn <= ~d;
    end
end

endmodule
