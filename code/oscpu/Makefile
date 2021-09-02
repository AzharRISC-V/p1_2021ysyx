
ALL ?= inst_diff

START ?= 1
END ?= -1

ifeq ($(ALL), inst_diff)
	ALLBIN := $(ALL)
else
	ALLBIN := $(ALL)-riscv64-mycpu
endif

# build and run
app:
	./build.sh -e cpu_diff -d -b -m "EMU_TRACE=1" -s -a "-i $(ALLBIN).bin --dump-wave -b $(START) -e $(END)"

# run without dump
run:
	./build.sh -e cpu_diff -d -s -a "-i $(ALLBIN).bin"

# run with dump
dump:
	./build.sh -e cpu_diff -d -s -a "-i $(ALLBIN).bin --dump-wave -b $(START) -e $(END)"

# run all
run-all:
	@./build.sh -e cpu_diff -b -r

# Clean nemu/build
clean:
	@./build.sh -e cpu_diff -c
