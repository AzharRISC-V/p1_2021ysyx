// ZhengpuShi

// 延时一定的时钟后输出信号，并带有清零和设置

module delay #(
  parameter WIDTH = 2,
  parameter DELAY = 1)
  (
  input   wire                  rst,
  input   wire                  clk,
  input   wire                  clear,    // 清除数据
  input   wire  [WIDTH-1 : 0]   idata,
  output  reg   [WIDTH-1 : 0]   odata
);

reg [7:0] delay_cnt;

always @(posedge clk) begin
  // reset
  if (rst) begin
    delay_cnt   <= 0;
    odata       <= 0;
  end

  // clear or delay output
  if (clear) begin
    odata       <= 0;
  end
  else begin
    odata   
  end
end

endmodule

