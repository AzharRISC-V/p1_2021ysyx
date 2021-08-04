// 1 位全加器进位输出 UDP 元件 - 包含 x 态输入的
primitive carry_udp(cout,cin,a,b);
input cin,a,b;
output cout;
    table
        // cin  a   b   :   cout // 真值表
            // 已知情形
            0   0   0   :   0;
            0   0   1   :   0;
            0   1   0   :   0;
            0   1   1   :   1;
            1   0   0   :   0;
            1   0   1   :   1;
            1   1   0   :   1;
            1   1   1   :   1;
            // 剩余情形
            0   0   x   :   0;  // 只有有两个输入为0，则进位为0
            0   x   0   :   0;
            x   0   0   :   0;
            1   1   x   :   1;  // 只要有一个输入为1，则进位为1
            1   x   1   :   1;
            x   1   1   :   1;
    endtable
endprimitive