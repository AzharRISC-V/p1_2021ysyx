// 8 位移位寄存器（移位器 shifter）
module reg8(din,clk,clr,dout);
input din,clk,clr;
output [7:0] dout;
reg [7:0] dout;

always @(posedge clk) begin
    if (clr)
        dout <= 8'b0;   // 同步清零
    else begin
        dout <= dout << 1;  // 输出左移一位
        dout[0] <= din;     // 输入信号补充到输出信号的最低端
        // 思考一个问题，这里会不会出现：上面两句执行期间被访问到？
    end
end

endmodule
