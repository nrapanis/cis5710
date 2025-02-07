        .section .data
input_string:   .asciz "Hello world!"

        # tohost/fromhost are data locations used by Spike
        .align 8
tohost: .byte 0
        .align 8
fromhost: .byte 0

        
        .section .text
        .globl _start
_start:
        # Load the address of the input string into a0
        la a0, input_string

        ADDI t0, a0, 0  #Save input string address
        ADDI t2, x0, 97
        ADDI t3, x0, 122

        .START_LOOP:

        LB t1, 0(t0) #Load current letter

        BEQZ t1, end_program

        BLT t1, t2, .SKIPPER          # <97 or > 122
        BLT t3, t1, .SKIPPER
        
        ADDI t1, t1, -32

        SB t1, 0(t0)

        .SKIPPER:

        ADDI t0, t0, 1 # Increment counter

        j .START_LOOP
        
end_program:
        # jump here when you're done
        j end_program

