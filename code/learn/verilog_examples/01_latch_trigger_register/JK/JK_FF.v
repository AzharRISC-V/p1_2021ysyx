// JK 触发器 （同步复位、同步置位）
module JK(q,qn,J,K,clk,rstn,setn);
input clk,J,K,setn,rstn;
output q,qn;
reg q,qn;

always @(posedge clk) begin
    if ({rstn,setn} == 2'b01) begin
        q <= 0; qn <= 1;
    end
    else if ({rstn,setn} == 2'b10) begin
        q <= 1; qn <= 0;
    end
    else if ({rstn,setn} == 2'b00) begin
        q <= q; qn <= qn;
    end
    else if ({rstn,setn} == 2'b11) begin
        if ({J,K} == 2'b00) begin
            q <= q; qn <= qn;
        end
        else if ({J,K} == 2'b01) begin
            q <= 0; qn <= 1;
        end
        else if ({J,K} == 2'b10) begin
            q <= 1; qn <= 0;
        end
        else if ({J,K} == 2'b11) begin
            q <= ~q; qn <= ~qn;
        end
    end
end

endmodule
