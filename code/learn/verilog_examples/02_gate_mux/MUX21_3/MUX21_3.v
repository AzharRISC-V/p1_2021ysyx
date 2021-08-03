// 2 选 1 多路选择器 - 门级结构描述
module MUX21_3(out,a,b,sel);
input a,b,sel;
output out;

not (sel_,sel);         // sel_ = ~sel
and (a1,a,sel_), (a2,b,sel);    // a1 = a & sel_,  a2 = b & sel
or (out,a1,a2);         // out = a1 | a2

endmodule
