// 1 位全加器进位输出 UDP 元件
primitive carry_udp(cout,cin,a,b);
input cin,a,b;
output cout;
    table
        // cin  a   b   :   cout // 真值表
            0   0   0   :   0;
            0   0   1   :   0;
            0   1   0   :   0;
            0   1   1   :   1;
            1   0   0   :   0;
            1   0   1   :   1;
            1   1   0   :   1;
            1   1   1   :   1;
    endtable
endprimitive