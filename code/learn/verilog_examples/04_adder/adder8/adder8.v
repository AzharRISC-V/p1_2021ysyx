// 8 位全加器 - 非流水线方式
module adder8(cout,sum,ina,inb,cin,clk);
    output [7:0] sum;
    output cout;
    input [7:0] ina,inb;
    input cin,clk;
    reg [7:0] tempa,tempb,sum;
    reg cout;
    reg tempc;

    // 输入数据缓存
    always @(posedge clk) begin
        tempa = ina; tempb = inb; tempc = cin;
    end

    always @(posedge clk) begin
        {cout,sum} = tempa + tempb + tempc;
    end

endmodule
