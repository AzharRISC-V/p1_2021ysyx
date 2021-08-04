// 4 位 Johnson 计数器（异步复位）
module counter4_6(clk,clr,out);
output [3:0] out;
input clk,clr;
reg [3:0] out;
always @(posedge clk or posedge clr) begin
    if (!clr) out <= 4'h0;
    else begin
        /*
            0000
            0001
            0011
            0111
            1111
            1110
            1100
            1000
            ...
        */
        out <= out + 1;
        out[0] <= ~out[3];
    end
end
endmodule


