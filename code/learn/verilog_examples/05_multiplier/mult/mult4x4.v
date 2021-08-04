// 4x4查找表乘法器

// 查找表方式实现2x2乘法
module lookup(out,a,b,clk);
    output [3:0] out;
    input [1:0] a,b;
    input clk;
    reg [3:0] out;
    reg [3:0] address;
    always @(posedge clk) begin
        address = {a,b};
        case (address)
            4'b00_00: out = 4'd0;
            4'b00_01: out = 4'd0;
            4'b00_10: out = 4'd0;
            4'b00_11: out = 4'd0;
            4'b01_00: out = 4'd0;
            4'b01_01: out = 4'd1;
            4'b01_10: out = 4'd2;
            4'b01_11: out = 4'd3;
            4'b10_00: out = 4'd0;
            4'b10_01: out = 4'd2;
            4'b10_10: out = 4'd4;
            4'b10_11: out = 4'd6;
            4'b11_00: out = 4'd0;
            4'b11_01: out = 4'd3;
            4'b11_10: out = 4'd6;
            4'b11_11: out = 4'd9;
        endcase
    end
endmodule


module mult4x4(out,a,b,clk);
    output [7:0] out;
    input [3:0] a,b;
    input clk;
    reg [7:0] out;
    reg [1:0] firsta,firstb,seconda,secondb;
    wire [3:0] outa,outb,outc,outd;

    // 原理类似于：25 * 34 = (2*3*100 + 2*4*10 + 5*3*10 + 5*4)
    always @(posedge clk) begin
        firsta = a[3:2]; seconda = a[1:0];
        firstb = b[3:2]; secondb = b[1:0];
    end

    lookup  m1(outa,firsta,firstb,clk),
            m2(outb,firsta,secondb,clk),
            m3(outc,seconda,firstb,clk),
            m4(outd,seconda,secondb,clk);
    
    always @(posedge clk) begin
        out = (outa << 4) + (outb << 2) + (outc << 2) + outd;
    end
    
endmodule
