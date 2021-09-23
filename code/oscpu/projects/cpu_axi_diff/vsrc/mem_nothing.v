
// ZhengpuShi

`include "defines.v"

module mem_nothing(
  input   wire                clk,
  input   wire                rst,

  input   wire                start,
  input   wire                ack,
  output  reg                 req
);

always @(posedge clk) begin
  if (rst) begin
    req <= 0;
  end
  else begin
    // set request
    if (start) begin
      req <= 1;
    end
    // clear request
    else if (ack) begin
      req <= 0;
    end
  end
end


endmodule
