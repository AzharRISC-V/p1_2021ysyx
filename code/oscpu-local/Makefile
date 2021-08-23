
ALL ?= inst_diff

ifeq ($(ALL), inst_diff)
	ALLBIN := $(ALL)
else
	ALLBIN := $(ALL)-riscv64-mycpu
endif

app:
	./build.sh -e cpu_diff -d -b -m "EMU_TRACE=1"
run:
	$(info $(ALL))
	$(info $(ALLBIN))
	./build.sh -e cpu_diff -d -s -a "-i $(ALLBIN).bin --dump-wave -b 0"