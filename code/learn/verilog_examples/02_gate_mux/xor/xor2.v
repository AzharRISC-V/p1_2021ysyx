// xor2 - 二输入异或门

// 结构描述
module xor2_1(y,a,b);
input a,b;
output y;
xor(y,a,b);
endmodule

// 行为描述（case语句）
module xor2_2(y,a,b);
input a,b;
output y;
reg y;
always @(a,b) begin
    case ({a,b})
    2'b00: y <= 0;
    2'b01: y <= 1;
    2'b10: y <= 1;
    2'b11: y <= 0;
    default: y <='bx;
    endcase
end
endmodule

