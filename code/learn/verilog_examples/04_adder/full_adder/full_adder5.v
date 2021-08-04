// 1 位全加器 - 混合描述的
module full_adder5(a,b,cin,sum,cout);
input a,b,cin;
output sum,cout;
reg cout,m1,m2,m3;
wire s1;

// 调用门元件
xor x1(s1,a,b);

// always块语句
always @(a or b or cin) begin
    m1 = a & b;
    m2 = b & cin;
    m3 = a & cin;
    cout = (m1 | m2) | m3;
end

// assign持续赋值语句
assign
    sum = s1 ^ cin;
    
endmodule

