// 1 位半加器 - 门元件实现的
module half_adder1(a,b,sum,cout);
input a,b;
output sum,cout;
and(cout,a,b);  // cout = a & b;
xor(sum,a,b);   // sum = a ^ b;
endmodule
