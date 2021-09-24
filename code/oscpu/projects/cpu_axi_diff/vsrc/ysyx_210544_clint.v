
// ZhengpuShi

// Core Local Interrupt Controller

`include "defines.v"

module ysyx_210544_clint(
  input   wire                clk,
  input   wire                rst,

  input   wire [`BUS_64]      i_clint_addr,
  input   wire                i_clint_ren,
  output  reg  [`BUS_64]      o_clint_rdata,
  input   wire                i_clint_wen,
  input   reg  [`BUS_64]      i_clint_wdata,
  output  wire                o_clint_mtime_overflow
);

reg   [7:0]       reg_mtime_cnt;
reg   [`BUS_64]   reg_mtime;
reg   [`BUS_64]   reg_mtimecmp;

wire addr_mtime = i_clint_addr == `DEV_MTIME;
wire addr_mtimecmp = i_clint_addr == `DEV_MTIMECMP;

always @(posedge clk) begin
  if (rst) begin
    reg_mtime <= 0;
    reg_mtimecmp <= 5000;
  end
  else begin
    if (reg_mtime_cnt < 1) begin
      reg_mtime_cnt <= reg_mtime_cnt + 1;
    end
    else begin
      reg_mtime_cnt <= 0;
      reg_mtime <= reg_mtime + 20;
    end

    if (i_clint_wen & addr_mtimecmp) begin
      reg_mtimecmp <= i_clint_wdata;
    end
  end
end

assign o_clint_rdata = (rst | (!i_clint_ren)) ? 0 : 
  (addr_mtime ? reg_mtime :
  (addr_mtimecmp ? reg_mtimecmp : 0));

assign o_clint_mtime_overflow = reg_mtime > reg_mtimecmp;


endmodule
