.text
.globl main
main:
    lui  t1, 0x10000      # start address
    li   t3, 4            # t3 controls how the store address changes
    li   t0, 1000000      # N
loop:
    sw   t0, 0(t1)
    add  t1, t1, t3       # t3 = 4, the address advances by 4 each iteration, writing N = 1,000,000 distinct words (about 4 MB total)
    addi t0, t0, -1
    bne  t0, x0, loop
    li   a7, 10
    ecall