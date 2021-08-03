// 一些零散的电路

// 两个加法器和一个选择器
// sel=1, sum = a + b
// sel=0, sum = c + d
// 两个加法电路，一个选择器电路。
module resource1(sum,a,b,c,d,sel);
parameter size = 4;
output [size:0] sum;
input sel;
input [size-1:0] a,b,c,d;
reg [size:0] sum;
always @(a or b or c or d or sel) begin
    if (sel) sum = a + b;
    else sum = c + d;
end
endmodule

// 两个选择器和一个加法器
// sel=1, sum = a + b
// sel=0, sum = c + d
// 两个选择器电路，一个加法电路。
module resource2(sum,a,b,c,d,sel);
parameter size = 4;
output [size:0] sum;
input sel;
input [size-1:0] a,b,c,d;
reg [size-1:0] atemp,btemp;
reg [size:0] sum;
always @(a or b or c or d or sel) begin
    if (sel) begin
        atemp = a;
        btemp = b;
    end
    else begin
        atemp = c;
        btemp = d;
    end
    sum = atemp + btemp;
end
endmodule







