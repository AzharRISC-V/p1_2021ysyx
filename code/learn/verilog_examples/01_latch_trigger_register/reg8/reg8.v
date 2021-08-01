// 8 位数据寄存器
module reg8(out_data,in_data,clk,clr);
input [7:0] in_data;
output [7:0] out_data;
input clk,clr;
reg [7:0] out_data;

always @(posedge clk or posedge clr) begin
    if (clr)
        out_data <= 0;
    else
        out_data <= in_data;
end

endmodule
