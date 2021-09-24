
// ZhengpuShi

// 带有缓冲区的 putch 改进版，在收到 \n 时输出，否则存入缓冲区

`include "defines.v"

module ysyx_210544_putch(
  input   wire                  clk,
  input   wire                  rst,
  input   wire                  wen,
  input   wire  [`BUS_8]        wdata
);

parameter SIZE = 255;
reg [7:0]   cnt;
reg [7:0]   str [0 : SIZE - 1];

always @(posedge clk) begin
  if (rst) begin
    cnt = 0;
  end
  else begin
    if (wen) begin
      // 存入数据
      if (cnt < (SIZE - 1)) begin
        str[cnt] = wdata;
        cnt++;
      end
      // 输出
      if (wdata == 10) begin
        str[cnt] = 0;
        for (integer i = 0; (i < 255 && str[i] != 0); i++) begin
          $write("%s", str[i]);
        end
        cnt = 0;
      end
    end
  end
end


endmodule
