// 十进制模24计数器
module cnt24(ten,one,co,clk,clr);
output [3:0] ten,one;
output co;
input clk,clr;
reg [3:0] ten,one;
reg co;

always @(posedge clk) begin
    if (clr) begin
        ten <= 0; one <= 0; co <= 0;
    end
    else begin
        if ({ten,one} == 8'b0010_0011) begin
            ten <= 0; one <= 0; co <= 1;
        end
        else if (one == 4'b1001) begin
            ten <= ten + 1; one <= 0; co <= 0;
        end
        else begin
            one = one + 1; co <= 0;
        end
    end
end
endmodule


