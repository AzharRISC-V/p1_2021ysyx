// 1 位半加器 - 行为描述的
module half_adder3(a,b,sum,cout);
input a,b;
output sum,cout;
reg sum,cout;

always @(a or b) begin
    case ({a,b})    // 真值表描述
    2'b00: begin sum = 0; cout = 0; end
    2'b01: begin sum = 1; cout = 0; end
    2'b10: begin sum = 1; cout = 0; end
    2'b11: begin sum = 0; cout = 1; end
    endcase
end

endmodule

