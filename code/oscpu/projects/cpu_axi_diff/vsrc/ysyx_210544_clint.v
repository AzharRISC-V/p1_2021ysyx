
// ZhengpuShi

// Core Local Interrupt Controller

`include "defines.v"

module ysyx_210544_clint(
  input   wire                clk,
  input   wire                rst,

  input   wire [`YSYX210544_BUS_64]      i_clint_addr,
  input   wire                i_clint_ren,
  output  wire [`YSYX210544_BUS_64]      o_clint_rdata,
  input   wire                i_clint_wen,
  input   wire [`YSYX210544_BUS_64]      i_clint_wdata,
  output  wire                o_clint_mtime_overflow
);

// reg   [7:0]       reg_mtime_cnt;
reg   [`YSYX210544_BUS_64]   reg_mtime;
reg   [`YSYX210544_BUS_64]   reg_mtimecmp;
wire addr_mtime;
wire addr_mtimecmp;



assign addr_mtime = i_clint_addr == `YSYX210544_DEV_MTIME;
assign addr_mtimecmp = i_clint_addr == `YSYX210544_DEV_MTIMECMP;

always @(posedge clk) begin
  if (rst) begin
    reg_mtime <= 0;
    reg_mtimecmp <= 5000;
  end
  else begin
    // if (reg_mtime_cnt < 1) begin
    //   reg_mtime_cnt <= reg_mtime_cnt + 1;
    // end
    // else begin
    //   reg_mtime_cnt <= 0;
    //   reg_mtime <= reg_mtime + 500;
    // end
    reg_mtime <= reg_mtime + 1;
    
    if (i_clint_wen & addr_mtimecmp) begin
      // $display("reg_mtimecmp, old: ", reg_mtimecmp, ", new: ", i_clint_wdata, ". reg_mtime: ", reg_mtime);
      // $write("^");
      reg_mtimecmp <= i_clint_wdata;
    end
  end
end

assign o_clint_rdata = (rst | (!i_clint_ren)) ? 0 : 
  (addr_mtime ? reg_mtime :
  (addr_mtimecmp ? reg_mtimecmp : 0));

assign o_clint_mtime_overflow = reg_mtime > reg_mtimecmp;


endmodule
