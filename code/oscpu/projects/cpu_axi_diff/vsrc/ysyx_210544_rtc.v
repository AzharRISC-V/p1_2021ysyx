
// ZhengpuShi

// Simple RTC module

`include "defines.v"

module ysyx_210544_rtc(
  input   wire              clk,
  input   wire              rst,

  input   wire              ren,
  output  [`YSYX210544_BUS_64]         rdata
);

reg   [`YSYX210544_BUS_64] clk_cnt     ;   // 内部计时器，用于控制秒的变化
reg   [15: 0]   year        ;   // year: 0000 ~ 9999    2^16-1=65535
reg   [3 : 0]   month       ;   // 2^4-1=15
reg   [4 : 0]   day         ;   // 2^5-1=31
reg   [5 : 0]   hour        ;   // 2^6-1=63
reg   [5 : 0]   minute      ;   // 2^6-1=63
reg   [5 : 0]   second      ;   // 2^6-1=63

wire  [`YSYX210544_BUS_64] rtc_val;


assign rtc_val = {21'b0, year, month, day, hour, minute, second};

// rtc simulate
always @(posedge clk) begin
  if (rst) begin
    clk_cnt  <= 0;
    year    <= 16'd2021;
    month   <= 4'd1;
    day     <= 5'd2;
    hour    <= 6'd3;
    minute  <= 6'd4;
    second  <= 6'd5;
  end
  else begin
    clk_cnt <= clk_cnt + 1;
    if (clk_cnt == `YSYX210544_CLOCKS_PER_SECOND) begin
      clk_cnt <= 0;
      second <= second + 6'd1;
      if (second == 60) begin
        second <= 6'd0;

        minute <= minute + 6'd1;
        if (minute == 60) begin
          minute <= 6'd0;

          hour <= hour + 6'd1;
          if (hour == 24) begin
            hour <= 6'd0;

            day <= day + 5'd1;
            if (day == 30) begin
              day <= 5'd0;

              month <= month + 4'd1;
              if (month == 12) begin
                month <= 4'd0;

                year <= year + 16'd1;
              end
            end
          end
        end
      end
    end
  end
end

// rtc read
assign rdata = (rst | !ren) ? 0 : rtc_val;

endmodule
