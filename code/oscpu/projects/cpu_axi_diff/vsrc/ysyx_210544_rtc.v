
// ZhengpuShi

// Simple RTC module

`include "defines.v"

module ysyx_210544_rtc(
  input   wire              clk,
  input   wire              rst,

  input   wire              ren,
  output  [`BUS_64]         rdata
);

reg   [`BUS_64] clk_cnt     ;   // 内部计时器，用于控制秒的变化

reg   [15: 0]   year        ;   // year: 0000 ~ 9999    2^16-1=65535
reg   [3 : 0]   month       ;   // 2^4-1=15
reg   [4 : 0]   day         ;   // 2^5-1=31
reg   [5 : 0]   hour        ;   // 2^6-1=63
reg   [5 : 0]   minute      ;   // 2^6-1=63
reg   [5 : 0]   second      ;   // 2^6-1=63

wire  [`BUS_64] rtc_val = {21'b0, year, month, day, hour, minute, second};

// rtc simulate
always @(posedge clk) begin
  if (rst) begin
    year = 2021;
    month = 1;
    day = 2;
    hour = 3;
    minute = 4;
    second = 5;
  end
  else begin
    clk_cnt += 1;
    if (clk_cnt == `CLOCKS_PER_SECOND) begin
      clk_cnt = 0;
      second += 1;
      if (second == 60) begin
        second = 0;

        minute += 1;
        if (minute == 60) begin
          minute = 0;

          hour += 1;
          if (hour == 24) begin
            hour = 0;

            day += 1;
            if (day == 30) begin
              day = 0;

              month += 1;
              if (month == 12) begin
                month = 0;

                year += 1;
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
