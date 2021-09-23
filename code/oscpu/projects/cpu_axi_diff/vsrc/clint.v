
// ZhengpuShi

// Core Local Interrupt Controller

`include "defines.v"

module clint(
  input   wire                clk,
  input   wire                rst,

  input   wire                i_clint_mtimecmp_ren,
  output  reg  [`BUS_64]      o_clint_mtimecmp_rdata,
  input   wire                i_clint_mtimecmp_wen,
  input   reg  [`BUS_64]      i_clint_mtimecmp_wdata,
  output  wire                o_clint_mtime_overflow
);

reg   [7:0]       reg_mtime_cnt;
reg   [`BUS_64]   reg_mtime;
reg   [`BUS_64]   reg_mtimecmp;


always @(posedge clk) begin
  if (rst) begin
    reg_mtime <= 0;
    reg_mtimecmp <= 5000;
  end
  else begin
    if (reg_mtime_cnt < 100) begin
      reg_mtime_cnt <= reg_mtime_cnt + 1;
    end
    else begin
      reg_mtime_cnt <= 0;
      reg_mtime <= reg_mtime + 1;
    end

    if (i_clint_mtimecmp_wen) begin
      reg_mtimecmp <= i_clint_mtimecmp_wdata;
    end
  end
end

assign o_clint_mtimecmp_rdata = (rst | !i_clint_mtimecmp_ren) ? 0 : reg_mtimecmp;
assign o_clint_mtime_overflow = reg_mtime > reg_mtimecmp;


endmodule
