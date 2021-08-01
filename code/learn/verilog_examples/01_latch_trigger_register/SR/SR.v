// SR 锁存器

// 方式1
module SR(q,qn,s,r);
input s,r;
output q,qn;
reg q,qn;
reg q1,qn1;

always @(*) begin
    q1 = ~(s & qn1);
    qn1 = ~(r & q1);
    q = q1;
    qn = qn1;

end

endmodule

// 方式2
module d(q,qn,d,clk,s,r);
input s,r,d,clk;
output q,qn;
reg q,qn;

always @(posedge clk) begin
    if ({r,s} == 2'b01) begin
        q = 0; qn = 'b1;
    end
    else if ({r,s} == 2'b10) begin
        q = 'b1; qn = 0;
    end
    else if ({r,s} == 2'b11) begin
        q = d; qn = ~d;
    end
end

endmodule

