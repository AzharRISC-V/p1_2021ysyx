// 减法器 - 不带借位

// 描述1
module half_sub1(dout,cout,a,b);
    output dout,cout;       // 差位，是否借位
    input a,b;              // 被减数，减数
    reg dout,cout;

    /*  a   b   dout    cout 
        0   0   0       0
        0   1   1       1
        1   0   1       0
        1   1   0       0
    */
    always @(*) begin
        dout = a ^ b;
        cout = (~a) & b;
    end
endmodule

// 描述2
module half_sub2(dout,cout,a,b);
    output dout,cout;       // 差位，是否借位
    input a,b;              // 被减数，减数
    reg dout,cout;
    always @(*) begin
        {cout,dout} = a - b;
    end
endmodule

// 减法器 - 带借位
module sub(dout,cout,a,b,ci);
    output dout,cout;       // 差位，是否借位
    input a,b,ci;           // 被减数，减数，低位借位
    reg dout,cout;
    always @(*) begin
        {cout,dout} = a - b - ci;
    end
endmodule

