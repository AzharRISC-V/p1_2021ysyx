// ZhengpuShi

`include "../defines.v"

module mem_mmio(
  input   wire                clk,
  input   wire                rst,

  input   wire                ena,
  input   wire                start,
  input   wire                ack,
  output  reg                 req,
  input   wire                ren,
  input   wire [`BUS_64]      raddr,
  output  reg  [`BUS_64]      rdata
);

// rtc设备
wire                rtc_ren;
wire  [`BUS_64]     rtc_rdata;

assign rtc_ren = (rst | !ren) ? 0 : raddr == `DEV_RTC;

rtc Rtc(
  .clk                (clk              ),
  .rst                (rst              ),
  .ren                (rtc_ren          ),
  .rdata              (rtc_rdata        )
);

always @(posedge clk) begin
  if (rst) begin
    req <= 0;
    rdata <= 0;
  end
  else begin
    if (!ena) begin
      req <= 0;
      rdata <= 0;
    end
    else begin
      // set request
      if (ren & start) begin
        case (raddr)
          `DEV_RTC      :   rdata <= rtc_rdata;
          default       : ;
        endcase
        req <= 1;
      end
      // clear request
      else if (ack) begin
        req <= 0;
      end
    end
  end
end


endmodule
