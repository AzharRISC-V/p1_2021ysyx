// nand2 - 二输入与非门

// 结构描述
module nand2_1(y,a,b);
input a,b;
output y;
nand(y,a,b);
endmodule

// 行为描述（case语句）
module nand2_2(y,a,b);
input a,b;
output y;
reg y;
always @(a,b) begin
    case ({a,b})
    2'b00: y = 1;
    2'b01: y = 1;
    2'b10: y = 1;
    2'b11: y = 0;
    default: y ='bx;
    endcase
end
endmodule

