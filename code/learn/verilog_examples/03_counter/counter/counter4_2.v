// 4位计数器

// 异步复位，电平触发，行为描述的
module counter4_2(out,clk,rst);
output [3:0] out;
input clk,rst;
reg [3:0] out;

always @(clk or rst) begin
    if (rst) out = 0;
    else out = out + 1;
end

endmodule
