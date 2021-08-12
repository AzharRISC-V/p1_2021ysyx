; 程序现象：
; 显示 0， 显示 255，
; 显示 1， 显示 255，
; 显示 2， 显示 255，
; 依次类推


    MOV SS, 1
    MOV SP, 0x20    ; [0, 0x1F] 栈空间
    JMP start

; 显示 255
show:
    MOV D, 255;
    RET

; C = 0
start:
    MOV C, 0

; C 递增，送显示，中间函数调用，继续递增。。
increase:
    INC C;
    MOV D, C;
    CALL show
    JMP increase
    
    HLT
