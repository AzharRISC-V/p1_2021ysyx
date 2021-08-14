; 程序描述：
; D = 3, 然后增加至 5，然后减小至 0，然后增加至 5，然后减小至 0，反复。。。

    MOV D, 3;

increase:
    INC D;
    CMP D, 5;
    JO increase     ; D < 5 时继续增加

decrease:
    DEC D;
    CMP D, 0;
    JZ increase     ; D = 0 时跳转到 increase
    JMP decrease    ; 否则，继续减

    HLT     ; 期望 D = 6
