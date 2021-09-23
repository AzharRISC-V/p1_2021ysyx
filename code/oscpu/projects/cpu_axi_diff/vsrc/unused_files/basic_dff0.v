
// ZhengpuShi

// D Flip Flop (DFF) with default value 0

`include "defines.v"

module basic_dff0 # (
  parameter DW = 32
) (
  input               clk,
  input               rst,
  input               en, 
  input      [DW-1:0] d,
  output     [DW-1:0] q
);

reg [DW-1:0] q_r;

always @(posedge clk or negedge rst) begin
  if (rst)
    q_r <= {DW{1'b0}};
  else if (en)
    q_r <= d;
end

assign q = q_r;

endmodule
