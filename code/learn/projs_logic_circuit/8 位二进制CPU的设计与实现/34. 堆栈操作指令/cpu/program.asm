    
    MOV SS, 1
    MOV SP, 0x10    ; [0, 0x9] 栈空间
    MOV D, 10
    
    PUSH D
    PUSH 1

    POP C       ; 不能直接 POP A，因为 A 会被内部用来运算 SP，后期可以改善这部分设计。
    MOV A, C    ; A = 1
    POP B       ; B = 10。  注意，凡是 POP 操作，都会更改 A 的值。因此还需要搬运一次。
    MOV A, C    ; A = 1
    
    ADD A, B    ; A = 11
    MOV D, A    ; D = 11

    HLT
