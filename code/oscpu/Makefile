
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
	./build.sh -e $(PROJECT) -d -s -a "-i $(BIN).bin"

# run with dump
dump:
	./build.sh -e $(PROJECT) -d -s -a "-i $(BIN).bin --dump-wave -b $(START) -e $(END)" -m "EMU_TRACE=1 $(PROJECT_AXI_FLAGS)"

# run all
run-all:
	@./build.sh -e $(PROJECT) -b -r

# Clean nemu/build
clean:
	@./build.sh -e $(PROJECT) -c
