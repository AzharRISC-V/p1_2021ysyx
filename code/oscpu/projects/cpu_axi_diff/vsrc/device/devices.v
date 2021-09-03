// ZhengpuShi

`include "../defines.v"

module devices(
  input   wire              clk,
  input   wire              rst,

  input   wire              ren,
  input   wire [`BUS_64]    raddr,
  output  reg  [`BUS_64]    rdata,
  output  wire              read_ok
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


// 所有设备的数据汇总
always @(*) begin
  if (rst) begin
    rdata = 0;
    read_ok = 0;
  end
  else begin
    if (ren) begin
      case (raddr)
        `DEV_RTC      :   rdata = rtc_rdata;
        default       : ;
      endcase
      read_ok = 1;
    end
    else begin
      rdata = 0;
      read_ok = 0;
    end
  end
end


endmodule
