// 带异步清 0 、异步置 1 的 JK 触发器
module JK_FF(clk,J,K,q,rstn,setn);
input clk,J,K,setn,rstn;
output q;
reg q;

always @(posedge clk or negedge setn or negedge rstn) begin
    // 异步清 0，低电平有效
    if (!rstn) begin
        q <= 1'b0;
    end
    // 异步置 1，低电平有效
    else if (!setn) begin
        q <= 1;
    end
    // 时钟上升沿输出改变
    else case ({J,K})
        2'b00: q <= q;
        2'b01: q <= 1'b0;
        2'b10: q <= 1'b1;
        2'b11: q <= ~q;
        default: q <= 1'bx; // 当J,K信号不是0或1时
    endcase
end

endmodule
