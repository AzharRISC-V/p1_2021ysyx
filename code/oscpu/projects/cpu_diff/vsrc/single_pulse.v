// ZhengpuShi

/*
  产生单脉冲，常用于启动信号
*/

module single_pulse (
  input    clk,
  input    rst,
  input    signal_in,
  output   pluse_out
);

reg delay_reg1;
reg delay_reg2;

always@(posedge clk)
  if(rst) begin
    delay_reg1  <=  0;
    delay_reg2  <=  0;
  end
  else begin
    delay_reg1  <= signal_in  ;
    delay_reg2  <= delay_reg1 ;
  end

assign pluse_out = delay_reg1 & (!delay_reg2);

endmodule
