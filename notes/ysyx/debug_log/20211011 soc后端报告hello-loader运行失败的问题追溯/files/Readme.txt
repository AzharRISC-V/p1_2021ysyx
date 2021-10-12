1. disassemble elf to txt
riscv64-linux-gnu-objdump -D hello-riscv64-mycpu.elf > hello-riscv64-mycpu.txt

2. elf to bin
riscv64-linux-gnu-objcopy -O binary hello-riscv64-mycpu.elf hello-riscv64-mycpu.bin

