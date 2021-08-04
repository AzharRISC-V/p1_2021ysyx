`include "../full_adder/full_adder1.v"

// 8 位全加器 - 级连
module add8_cascade(sum,cout,a,b,cin);
    output [7:0] sum;
    output cout;
    input [7:0] a,b;
    input cin;
    
    // 级连描述
    full_adder1 f0(a[0],b[0],cin,   sum[0],cin1);
    full_adder1 f0(a[1],b[1],cin1,  sum[1],cin2);
    full_adder1 f0(a[2],b[2],cin2,  sum[2],cin3);
    full_adder1 f0(a[3],b[3],cin3,  sum[3],cin4);
    full_adder1 f0(a[4],b[4],cin4,  sum[4],cin5);
    full_adder1 f0(a[5],b[5],cin5,  sum[5],cin6);
    full_adder1 f0(a[6],b[6],cin6,  sum[6],cin7);
    full_adder1 f0(a[7],b[7],cin7,  sum[7],cout);

endmodule
