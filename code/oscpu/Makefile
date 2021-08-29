
ALL ?= inst_diff

ifeq ($(ALL), inst_diff)
	ALLBIN := $(ALL)
else
	ALLBIN := $(ALL)-riscv64-mycpu
endif

# build and run
app:
	./build.sh -e cpu_diff -d -b -m "EMU_TRACE=1" -s -a "-i $(ALLBIN).bin --dump-wave -b 0"

# only run
run:
	./build.sh -e cpu_diff -d -s -a "-i $(ALLBIN).bin --dump-wave -b 0"

# run all
run-all:
	@./build.sh -e cpu_diff -r

# Clean nemu/build
clean:
	@./build.sh -e cpu_diff -c
