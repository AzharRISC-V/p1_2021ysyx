// 1 位半加器 - 行为描述的
module half_adder3(a,b,sum,cout);
input a,b;
output sum,cout;
reg sum,cout;

always @(a or b) begin
    sum = a ^ b;
    cout = a & b;
end

endmodule

