all:
	@-mkdir ./build
	iverilog -o ./build/tb_mut2 ./src/tb_mut2.v ./src/mut2.v

run:
	vvp -n ./build/tb_mut2
	gtkwave ./build/wave.vcd

.PHONY: clean

clean:
	rm -r ./build
