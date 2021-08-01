// 上升沿触发的 D 触发器 UDP 元件 (D Flip-Flop)
primitive DFF(Q,clk,D);
output Q;
input clk,D;
reg Q;
    table
    // clk D : state : Q
    (01) 0 : ? : 0;     // posedge, Q = D
    (01) 1 : ? : 1;
    (0x) 1 : 1 : 1;
    (0x) 0 : 0 : 0;
    (?0) ? : ? : -;     // 没有上升沿，输出Q保持原值
    ? (??) : ? : -;     // 时钟不变，输出也不变
    endtable

endprimitive