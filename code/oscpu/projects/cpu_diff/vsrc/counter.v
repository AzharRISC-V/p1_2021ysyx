
// ZhengpuShi

`include "defines.v"

module counter(
  input   wire              clk,
  input   wire              rst,
  input   wire  [`BUS_8]    max,
  input   wire              clear,
  output  reg   [`BUS_8]    val
);

always @(negedge clk or negedge rst) begin
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
        val <= 2;
    end
  end
end


endmodule