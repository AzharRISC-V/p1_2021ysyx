// 三态门（three-state gate, tri-state gate, TSL)

// 用 bufif1 关键字描述
module tri_1(in,en,out);
input in,en;
output out;
tri out;

bufif1 b1(out,in,en);   // output, input, enable

endmodule

// 用 assign 语句描述
module tri_2(in,en,out);
input in,en;
output out;

assign out = en ? in : 'bz;

endmodule

// 行为描述
module tri_3(in,en,out);
input in,en;
output out;
reg out;
always @(en,in)
    if (en) out <= in;
    else out <= 'bz;
endmodule

// 8位的三态门
module tri_buffer(dout,din,en);
input [7:0] din;
input en;
output [7:0] dout;
reg [7:0] dout;
always @(en,din)
    if (en) dout <= din;
    else dout <= 8'bz;
endmodule

// 带方向控制的8位三态门
module tri_bibuffer(en,dir,da,db);
inout [7:0] da,db;      // 两个双向数据端口
input en,dir;           // 使能端，数据方向控制端。1 : a -> b, 0 : b -> a
reg [7:0] da,db;
always @(*) begin
    if (dir) begin
        if (en) db = da;
        else db = 'bz;
    end
    else begin
        if (en) da = db;
        else da = 'bz;
    end
end
endmodule

// 三态双向驱动器 (tri-state bidirectional driver)

// (1)
module bidir(tri_inout,out,in,en,b);
inout tri_inout;
output out;
input in,en,b;

assign tri_inout = en ? in : 'bz;   // 使能时，接收输入
assign out = tri_inout ^ b;

endmodule

// (2)
module bidir2(bidir,en,clk);
inout [7:0] bidir;
input en,clk;
reg [7:0] temp;

assign bidir = en ? temp : 8'bz;
always @(posedge clk) begin
    if (en) temp = bidir;
    else temp = temp + 1;
end

endmodule



