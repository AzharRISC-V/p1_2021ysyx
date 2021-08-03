// 2 选 1 多路选择器 - 持续赋值方式的 （也称 数据流描述的）
module MUX21_1(out,a,b,sel);
input a,b,sel;
output out;

assign out = (sel == 0) ? a : b;
    
endmodule

module MUX21_1b(out,a,b,sel);
input a,b,sel;
output out;

assign out = sel ? b : a;
    
endmodule
