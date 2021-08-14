; CMP
; MOV C, 5
; MOV D, 5
; CMP C, D

; AND
; MOV C, 5        ; 0101
; MOV D, 0xE      ; 1110
; AND D, C        ; 0100 = 4

; OR
; MOV C, 5        ; 0101
; MOV D, 0xE      ; 1110
; OR D, C         ; 1111 = 15

; XOR
; MOV C, 5        ; 0101
; MOV D, 0xE      ; 1110
; XOR D, C        ; 1011 = 11

; NOT
MOV D, 0x5A        ; 0101_1010
NOT D           ; 1010_0101 = A5

HLT     ; 期望 D = 6
