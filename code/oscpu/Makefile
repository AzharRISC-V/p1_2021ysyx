
BIN ?= inst_diff

START ?= 1
END ?= -1


PROJECT = cpu_axi_diff
PROJECT_AXI_FLAGS = WITH_DRAMSIM3=1

# build and run
app:
	./build.sh -e $(PROJECT) -d -b -s -a "-i $(BIN).bin --dump-wave -b $(START) -e $(END)" -m "EMU_TRACE=1 $(PROJECT_AXI_FLAGS)"

# run without dump
run:
	./build.sh -e $(PROJECT) -d -s -a "-i $(BIN).bin" -m "EMU_TRACE=1 $(PROJECT_AXI_FLAGS)"

# run with dump
dump:
	./build.sh -e $(PROJECT) -d -s -a "-i $(BIN).bin --dump-wave -b $(START) -e $(END)" -m "EMU_TRACE=1 $(PROJECT_AXI_FLAGS)"

# run all
run-all-1:
	./build.sh -e $(PROJECT) -b -r "non-output/cpu-tests" -m "EMU_TRACE=1 $(PROJECT_AXI_FLAGS)"
run-all-2:
	./build.sh -e $(PROJECT) -b -r "non-output/riscv-tests" -m "EMU_TRACE=1 $(PROJECT_AXI_FLAGS)"
run-all-3:
	./build.sh -e $(PROJECT) -b -r "my/cpu-tests" -m "EMU_TRACE=1 $(PROJECT_AXI_FLAGS)"


# Clean nemu/build
clean:
	@./build.sh -e $(PROJECT) -c
