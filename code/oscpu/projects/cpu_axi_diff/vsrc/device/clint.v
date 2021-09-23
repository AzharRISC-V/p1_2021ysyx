// ZhengpuShi

// Core Local Interrupt Controller

`include "../defines.v"

module clint(
  input   wire                clk,
  input   wire                rst,

  input   wire                i_clint_mtimecmp_ren,
  output  reg  [`BUS_64]      o_clint_mtimecmp_rdata,
  input   wire                i_clint_mtimecmp_wen,
  input   reg  [`BUS_64]      i_clint_mtimecmp_wdata,
  output  wire                o_clint_mtime_overflow
);

reg   [`BUS_64]   reg_mtime;
reg   [`BUS_64]   reg_mtimecmp;

always @(posedge clk) begin
  if (rst) begin
    reg_mtime <= 0;
    reg_mtimecmp <= 5000;
    o_clint_mtimecmp_rdata <= 0;
  end
  else begin
    reg_mtime <= reg_mtime + 1;

    if (reg_mtime > reg_mtimecmp + 2000) begin
      reg_mtime <= reg_mtimecmp - 2000;
    end
    else begin
      reg_mtime <= reg_mtime + 1;
    end

    if (i_clint_mtimecmp_ren) o_clint_mtimecmp_rdata <= reg_mtimecmp;
    else                      o_clint_mtimecmp_rdata <= 0;
      
    if (i_clint_mtimecmp_wen) reg_mtimecmp <= i_clint_mtimecmp_wdata;
  end
end

assign o_clint_mtime_overflow = reg_mtime > reg_mtimecmp;


endmodule
