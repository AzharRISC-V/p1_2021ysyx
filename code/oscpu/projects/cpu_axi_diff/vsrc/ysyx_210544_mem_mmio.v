
// ZhengpuShi

`include "defines.v"


module ysyx_210544_mem_mmio(
  input   wire                clk,
  input   wire                rst,

  input   wire                start,
  input   wire                ack,
  output  reg                 req,
  input   wire                ren,
  input   wire                wen,
  input   wire [`BUS_64]      addr,
  input   wire [`BUS_64]      wdata,
  output  reg  [`BUS_64]      rdata,
  output  wire                o_clint_mtime_overflow
);

// rtc设备
wire  [`BUS_64]               rtc_rdata;
wire  [`BUS_64]               i_clint_rdata;



ysyx_210544_rtc Rtc(
  .clk                (clk              ),
  .rst                (rst              ),
  .ren                (ren & (addr == `DEV_RTC)),
  .rdata              (rtc_rdata        )
);

// CLINT (Core Local Interrupt Controller)
ysyx_210544_clint Clint(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_clint_addr               (addr                       ),
  .i_clint_ren                (ren                        ),
  .o_clint_rdata              (i_clint_rdata              ),
  .i_clint_wen                (wen                        ),
  .i_clint_wdata              (wdata                      ),
  .o_clint_mtime_overflow     (o_clint_mtime_overflow     )
);

always @(posedge clk) begin
    if (rst) begin
        req   <= 0;
        rdata <= 0;
    end
    else begin
        // set request
        if (start) begin
            if (ren) begin
                if (addr == `DEV_RTC)             rdata <= rtc_rdata;
                else if (addr == `DEV_MTIME)      rdata <= i_clint_rdata;
                else if (addr == `DEV_MTIMECMP)   rdata <= i_clint_rdata;
                req <= 1;
            end
            else begin
                req <= 1;
            end
        end
        // clear request
        else if (ack) begin
            req   <= 0;
            rdata <= 0;
        end
    end
end

endmodule
