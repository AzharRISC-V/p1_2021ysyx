
// ZhengpuShi

`include "../defines.v"

module basic_counter # (
  parameter DW = 32
) (
  input   wire              clk,
  input   wire              rst,
  input   wire  [DW-1:0]    min,
  input   wire  [DW-1:0]    max,
  input   wire              clear,
  output  reg   [DW-1:0]    val
);

always @(posedge clk or negedge rst) begin
  if (rst) begin
    val <= 0;
  end
  else begin
    if (clear) begin
      val <= 0;
    end
    else begin
      if (val < max)
        val <= val + 1;
      else
        val <= min;
    end
  end
end

endmodule
