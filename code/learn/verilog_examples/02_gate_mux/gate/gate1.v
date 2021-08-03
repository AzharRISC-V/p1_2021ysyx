// 基本门电路的几种描述方法

// (1) 门级结构描述
module gate1(F,A,B,C,D);
input A,B,C,D;
output F;

nand (F1,A,B);
and (F2,B,C,D);
or (F,F1,F2);

endmodule

// (2) 数据流描述
module gate2(F,A,B,C,D);
input A,B,C,D;
output F;

assign F = (A & B) | (B & C & D);

endmodule

// (3) 行为描述
module gate3(F,A,B,C,D);
input A,B,C,D;
output F;
reg F;

always @(A or B or C or D) begin
    F = (A & B) | (B & C & D);
end

endmodule

