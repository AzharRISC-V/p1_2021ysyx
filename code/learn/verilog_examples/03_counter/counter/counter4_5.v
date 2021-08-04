// 同步复位、同步置位的 8 位计数器
module counter4_5(out,data,set,rst,clk);
output [7:0] out;
input [7:0] data;
input set,rst,clk;      // 置位、复位、时钟
reg [7:0] out;
always @(posedge clk) begin
    if (!rst) out = 8'h00;  // 同步清零，低电平有效
    else if (set) out = data;  // 同步预置
    else out = out + 1;
end
endmodule


