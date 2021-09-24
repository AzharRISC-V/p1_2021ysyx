
BIN ?= inst_diff

START ?= 1
END ?= -1


PROJECT = cpu_axi_diff
PROJECT_AXI_FLAGS = WITH_DRAMSIM3=1

# build and run
app:
	rm projects/cpu_axi_diff/build/emu-compile -rf
	./build.sh -e $(PROJECT) -d -b -s -v ' -Wall ' -a "-i $(BIN).bin --dump-wave -b $(START) -e $(END)" -m "EMU_TRACE=1 $(PROJECT_AXI_FLAGS)"

# run without dump
run:
	./build.sh -e $(PROJECT) -d -s -a "-i $(BIN).bin" -m "$(PROJECT_AXI_FLAGS)"

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


# ysyx soc
soc:
	@cd projects/cpu_axi_diff/vsrc/;\
	cat defines.v ysyx_210544_axi_rw.v ysyx_210544_S011HD1P_X32Y2D128_BW.v ysyx_210544_cache_axi.v \
	ysyx_210544_cache_basic.v ysyx_210544_cache_core.v ysyx_210544_cache.v ysyx_210544_putch.v ysyx_210544_rtc.v \
	ysyx_210544_clint.v ysyx_210544_regfile.v ysyx_210544_csrfile.v ysyx_210544_if_stage.v ysyx_210544_ifU.v \
	ysyx_210544_id_stage.v ysyx_210544_idU.v ysyx_210544_exe_stage.v ysyx_210544_exeU.v ysyx_210544_exceptionU.v \
	ysyx_210544_mem_stage.v ysyx_210544_memU.v ysyx_210544_mem_mmio.v ysyx_210544_mem_nothing.v ysyx_210544_wb_stage.v \
	ysyx_210544_wbU.v ysyx_210544_cmt_stage.v ysyx_210544_cmtU.v ysyx_210544_cpu.v SimTop4Soc.v > ysyx_210544.v; \
	mv ysyx_210544.v ../../soc/vsrc/; \
	cd ../../soc/vsrc/; \
	sed '/`include/d' ysyx_210544.v -i; \
	sed '/`timescale/d' ysyx_210544.v -i; \
	sed 's/module SimTop4Soc/module ysyx_210544/g' ysyx_210544.v -i; \
	sed '/`define SUPPORT_DIFFTEST/d' ysyx_210544.v -i;\
	sed -i "1i/* verilator lint_off DECLFILENAME */" ysyx_210544.v
	./build.sh -e soc -b -s -y -v '--timescale "1ns/1ns" -Wall --trace' -a "-i ysyxSoc/flash/hello-flash.bin --dump-wave"
soc-run:
	./build.sh -e soc -b -s -y -v '--timescale "1ns/1ns" -Wall --trace' -a "-i ysyxSoc/flash/hello-flash.bin"

# Clean nemu/build
clean:
	@./build.sh -e $(PROJECT) -c
