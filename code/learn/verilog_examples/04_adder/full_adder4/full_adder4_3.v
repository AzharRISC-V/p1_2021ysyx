// 4 位全加器 - 通过 task 和并联四个一位全加器模块实现
module full_adder4_3(sum,cout,a,b,cin);
output [3:0] sum;
output cout;
input [3:0] a,b;
input cin;
reg [3:0] sum;
reg cout;
reg [1:0] s0,s1,s2,s3;

task ADD;
    input a,b,cin;
    output [1:0] c;
    reg [1:0] c;
    reg s,cout;

    begin
        s = a ^ b ^ cin;
        cout = (a & b) | (a & cin) | (b & cin);
        c = {cout, s};
    end
endtask

always @(a or b or cin) begin
    ADD (a[0],b[0],cin,     s0);
    ADD (a[1],b[1],s0[1],   s1);
    ADD (a[2],b[2],s1[1],   s2);
    ADD (a[3],b[3],s2[1],   s3);
    sum = {s3[0],s2[0],s1[0],s0[0]};
    cout = s3[1];
end

endmodule

