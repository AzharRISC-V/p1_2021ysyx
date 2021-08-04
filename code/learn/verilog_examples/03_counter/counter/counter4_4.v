// 4位计数器

// 带复位、置位、使能、进位信号、预置数据、计数方向的
module counter4_4(co,q,clk,r,s,en,d,updn);
output [3:0] q;     // 计数输出端
output co;          // 进位信号
input clk,r,s,en,updn;   // 时钟、复位、置位、使能、计数方向(1:增大,0:减小)
input [3:0] d;      // 预置数据
reg [3:0] q;
reg co;

always @(posedge clk) begin
    if (en) begin
        if (r) begin
            q = 4'd0; co = 0;
        end 
        else if (s) begin
            q = d; co = 0;
        end 
        else begin
            if (updn) begin
                q = q + 1;
                if (q == 0)
                    co = 1;
                else
                    co = 0;
            end
            else begin
                q = q - 1;
                if (q == 4'b1111)
                    co = 1;
                else
                    co = 0;
            end
        end
    end
    else begin
        q = 'bx;
        co = 'bx;
    end
end

endmodule


