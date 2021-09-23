
// ZhengpuShi

// Latch

`include "defines.v"

module basic_latch # (
  parameter DW = 32
) (
  input               en, 
  input      [DW-1:0] d,
  output     [DW-1:0] q
);

reg [DW-1:0] q_r;

always_latch @(*) begin
  if (en)
    q_r <= d;
end

assign q = q_r;

endmodule

