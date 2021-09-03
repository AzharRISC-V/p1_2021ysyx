
BIN ?= inst_diff

START ?= 1
END ?= -1


# build and run
app:
	./build.sh -e cpu_diff -d -b -s -a "-i $(BIN).bin --dump-wave -b $(START) -e $(END)" -m "EMU_TRACE=1"

# run without dump
run:
	./build.sh -e cpu_diff -d -s -a "-i $(BIN).bin"

# run with dump
dump:
	./build.sh -e cpu_diff -d -s -a "-i $(BIN).bin --dump-wave -b $(START) -e $(END)" -m "EMU_TRACE=1"

# run all
run-all:
	@./build.sh -e cpu_diff -b -r

# Clean nemu/build
clean:
	@./build.sh -e cpu_diff -c
