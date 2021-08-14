    MOV D, 1;

increase:
    ADD D, 50;
    JMP increase

    HLT     ; 期望 D = 6
