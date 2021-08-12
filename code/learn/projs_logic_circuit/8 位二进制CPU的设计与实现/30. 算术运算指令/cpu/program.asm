; MOV C, 5

; MOV D, C

; MOV D, [5]

; MOV A, 6;

; MOV D, [A];

; MOV [0x2F], 5

; MOV C, 0x18
; MOV [0x2F], C

; MOV [0x2E], 0x18
; MOV [0x2F], [0x2E]

; 8. 
; MOV [18], 0x19
; MOV C, 18
; MOV [0x2F], [C]

; 9.
; MOV A, 0x30
; MOV [A], 3

; 10.
; MOV A, 0x30
; MOV B, 0x31
; MOV [A], B

; 11.
; MOV [0x30], 0xF0
; MOV A,0x33
; MOV [A], [0x30]

; 12.
MOV [0x30], 0xF0
MOV D, 0x30
MOV C, 0x18
MOV [C], [D]        ; 结果是 [0x18] <-- 0xF0

hlt