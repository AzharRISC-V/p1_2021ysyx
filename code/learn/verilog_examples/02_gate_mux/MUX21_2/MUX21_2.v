// 2 选 1 多路选择器 - 阻塞赋值方式定义
module MUX21_2(out,a,b,sel);
input a,b,sel;
output out;
reg out;

always @(a or b or sel) begin
    if (sel == 0)
        out = a;
    else
        out = b;
end
    
endmodule

module MUX21_2b(out,a,b,sel);
input a,b,sel;
output out;
reg out;

always @(a or b or sel) begin
    if (sel)
        out = b;
    else
        out = a;
end
    
endmodule

