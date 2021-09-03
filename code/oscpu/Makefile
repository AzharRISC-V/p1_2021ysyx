
BIN ?= inst_diff

START ?= 1
END ?= -1

PROJECT = cpu_axi_diff


# build and run
app:
	./build.sh -e $(PROJECT) -d -b -s -a "-i $(BIN).bin --dump-wave -b $(START) -e $(END)" -m "EMU_TRACE=1"

# run without dump
run:
	./build.sh -e $(PROJECT) -d -s -a "-i $(BIN).bin"

# run with dump
dump:
	./build.sh -e $(PROJECT) -d -s -a "-i $(BIN).bin --dump-wave -b $(START) -e $(END)" -m "EMU_TRACE=1"

# run all
run-all:
	@./build.sh -e $(PROJECT) -b -r

# Clean nemu/build
clean:
	@./build.sh -e $(PROJECT) -c
