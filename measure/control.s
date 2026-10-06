.text
.globl main
main:
    lui  t1, 0x10000      # start address
    li   t3, 0            # t3 controls how the store address changes
    li   t0, 1000000      # N
loop:
    sw   t0, 0(t1)
    add  t1, t1, t3       # t3 = 0, means t1 never changes, so all N = 1,000,000 stores go to the same address (0x10000000)
    addi t0, t0, -1
    bne  t0, x0, loop
    li   a7, 10
    ecall