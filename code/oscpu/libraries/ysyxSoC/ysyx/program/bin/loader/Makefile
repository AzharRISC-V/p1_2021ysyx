all:
	riscv64-linux-gnu-objdump -D -b binary -m riscv:rv64 hello-loader.bin > hello-loader.txt
	riscv64-linux-gnu-objdump -D -b binary -m riscv:rv64 memtest-loader.bin > memtest-loader.txt
	riscv64-linux-gnu-objdump -D -b binary -m riscv:rv64 rtthread-loader.bin > rtthread-loader.txt

