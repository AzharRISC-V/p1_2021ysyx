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
    IRET

; C = 0
start:
    MOV C, 0

; C 递增，送显示，中间函数调用，继续递增。。
increase:
    INC C;
    MOV D, C;
    JP disable      ; 奇数，关中断，不显示；偶数，开中断，显示。

enable:
    STI
    JMP interrupt

disable:
    CLI         ; 关中断后，show程序不会调用

interrupt:
    INT show
    JMP increase
    
    HLT
