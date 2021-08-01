// 电平敏感的 1 位数据锁存器 UDP 元件
primitive latch(Q,clk,rst,D);
input clk,rst,D;
output Q;
reg Q;
initial Q = 1'b1;
    table
    // clk rst D : state : Q
    ? 1 ? : ? : 0;  // if rst = 1, output is 0
    0 0 0 : ? : 0;  // clk = 0, output is D
    0 0 1 : ? : 1;
    1 0 ? : ? : -;  // clk = 1, output keep same
    endtable

endprimitive
