// 二选一数据选择器
// sel = 0 时，out = a
// sel = 1 时，out = b
module mut2 (out,
            a,
            b,
            sel);
    input a,b,sel;
    output out;
    wire selnot,a1,b1;

    not U1(selnot,sel);     // selnot = !sel
    and U2(a1,a,selnot);    // a1 = a && selnot
    and U3(b1, b, sel);     // b1 = b && sel
    or  U4(out, a1, b1);    // out = a1 || b1

endmodule //mut2