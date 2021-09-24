
`include "defines.v"

module ysyx_210544_S011HD1P_X32Y2D128_BW(
    Q, CLK, CEN, WEN, BWEN, A, D
);
parameter Bits = 128;
parameter Word_Depth = 64;
parameter Add_Width = 6;
parameter Wen_Width = 128;

output reg [Bits-1:0] Q;
input                 CLK;
input                 CEN;        // 低电平有效
input                 WEN;        // 低电平有效
input [Wen_Width-1:0] BWEN;       // 低电平有效
input [Add_Width-1:0] A;
input [Bits-1:0]      D;

wire cen  = ~CEN;
wire wen  = ~WEN;
wire [Wen_Width-1:0] bwen = ~BWEN;

reg [Bits-1:0] ram [0:Word_Depth-1];
always @(posedge CLK) begin
    if(cen && wen) begin
        ram[A] <= (D & bwen) | (ram[A] & ~bwen);
    end
    Q <= cen && !wen ? ram[A] : 0;//{4{$random}};
end

endmodule
