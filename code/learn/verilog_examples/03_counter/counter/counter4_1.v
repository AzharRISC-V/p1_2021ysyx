// 4位计数器

// 同步复位，边沿触发，行为描述的
module counter4_1(out,clk,rst);
output [3:0] out;
input clk,rst;
reg [3:0] out;

always @(posedge clk) begin
    if (rst) out <= 0;
    else out <= out + 1;
end

endmodule
