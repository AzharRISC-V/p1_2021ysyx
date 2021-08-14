; ADD立即数寻址
; MOV D, 1;
; ADD D, 5;

; ADD寄存器寻址

;（一般的）
; MOV D, 4
; MOV C, 7
; ADD D, C;

; PSW - 溢出
; MOV D, 250
; MOV C, 7
; ADD D, C;

; PSW - 零
; MOV D, 0
; MOV C, 0
; ADD D, C;

; SUB

; 立即数寻址
; MOV D, 5
; SUB D, 5

; 寄存器寻址
; MOV D, 5
; MOV C, 4
; SUB D, C

; INC & DEC
MOV D, 0
INC D
INC D
INC D
INC D
INC D
DEC D
DEC D
DEC D
DEC D
DEC D

HLT     ; 期望 D = 6
