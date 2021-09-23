
// ZhengpuShi

`include "defines.v"

module mem_mmio(
  input   wire                clk,
  input   wire                rst,

  input   wire                start,
  input   wire                ack,
  output  reg                 req,
  input   wire                ren,
  input   wire                wen,
  input   wire [`BUS_64]      addr,
  input   reg  [`BUS_64]      wdata,
  output  reg  [`BUS_64]      rdata,
  output  wire                o_clint_mtime_overflow
);

// rtc设备
wire                rtc_ren;
wire  [`BUS_64]     rtc_rdata;

assign rtc_ren = (rst | !ren) ? 0 : addr == `DEV_RTC;

rtc Rtc(
  .clk                (clk              ),
  .rst                (rst              ),
  .ren                (rtc_ren          ),
  .rdata              (rtc_rdata        )
);

reg                           o_clint_mtimecmp_ren;
reg  [`BUS_64]                i_clint_mtimecmp_rdata;
reg                           o_clint_mtimecmp_wen;
reg  [`BUS_64]                o_clint_mtimecmp_wdata;

assign o_clint_mtimecmp_ren = (rst | !ren) ? 0 : addr == `DEV_MTIMECMP;

// CLINT (Core Local Interrupt Controller)
clint Clint(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_clint_mtimecmp_ren       (o_clint_mtimecmp_ren       ),
  .o_clint_mtimecmp_rdata     (i_clint_mtimecmp_rdata     ),
  .i_clint_mtimecmp_wen       (o_clint_mtimecmp_wen       ),
  .i_clint_mtimecmp_wdata     (o_clint_mtimecmp_wdata     ),
  .o_clint_mtime_overflow     (o_clint_mtime_overflow     )
);

always @(posedge clk) begin
  if (rst) begin
    req <= 0;
    rdata <= 0;
    o_clint_mtimecmp_wen <= 0;
    o_clint_mtimecmp_wdata <= 0;
  end
  else begin
    // set request
    if (start) begin
      if (ren) begin
        case (addr)
          `DEV_RTC        : rdata <= rtc_rdata;
          `DEV_MTIMECMP   : rdata <= i_clint_mtimecmp_rdata;
          default         : ;
        endcase
        req <= 1;
      end
      else begin
        case (addr)
          `DEV_MTIMECMP  : begin
            o_clint_mtimecmp_wdata <= wdata;
            o_clint_mtimecmp_wen <= wen;
          end
        endcase
        req <= 1;
      end
    end
    // clear request
    else if (ack) begin
      req <= 0;
      rdata <= 0;
      o_clint_mtimecmp_wdata <= 0;
      o_clint_mtimecmp_wen <= 0;
    end
  end
end


endmodule
