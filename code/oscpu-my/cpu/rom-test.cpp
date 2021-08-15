
#include <verilated.h>
#include <verilated_vcd_c.h>
#include <iostream>
#include <fstream>
#include "Vram.h"

using namespace std;

static Vram *top;
static VerilatedVcdC *tfp;
static vluint64_t main_time = 0;
static const vluint64_t sim_time = 1000;

// inst.bin
// inst 0: 1 + zero = reg1 1+0=1
// inst 1: 2 + zero = reg1 2+0=2
// inst 2: 1 + reg1 = reg1 1+2=3
int inst_rom[65536];

/*
	read all instructions from given file,
	and store to global variable : inst_rom
*/
void read_inst(char *filename)
{
	FILE *fp = fopen(filename, "rb");
	if (fp == NULL)
	{
		printf("Can not open instruction file: %s!\n", filename);
		exit(1);
	}

	fseek(fp, 0, SEEK_END);
	size_t size = ftell(fp);
	fseek(fp, 0, SEEK_SET);
	size = fread(inst_rom, size, 1, fp);
	fclose(fp);
}

int main(int argc, char **argv)
{
	char filename[100] = "../inst.bin";
	//printf("Please enter your filename~\n");
	//cin >> filename;
	read_inst(filename);

	// initialization
	Verilated::commandArgs(argc, argv);
	Verilated::traceEverOn(true);

	top = new Vram;
	tfp = new VerilatedVcdC;

	top->trace(tfp, 99);	// 99 hierarchy at most
	tfp->open("ram-test.vcd");

	vluint32_t write_addr = 0;
	vluint32_t write_data = 0x10;
	vluint32_t read_addr = 0;

	while (!Verilated::gotFinish() && main_time < sim_time)
	{
		// 时钟周期10，每5电平翻转
		if (main_time % 10 == 0)
			top->clk = 0;
		if (main_time % 10 == 5)
			top->clk = 1;

		// 10内保持复位信号
		if (main_time < 10)
		{
			top->rst = 1;
		}
		else
		{
			top->rst = 0;

			// 测试写入
			if (main_time < 100)
			{
				if (main_time % 10 == 1)
				{
					top->waddr_i = write_addr;
					top->wdata_i = write_data;
					write_addr += 1;
					write_data += 1;
				}
				if (main_time % 10 == 2)
					top->we_i = 1;
				if (main_time % 10 == 8)
					top->we_i = 0;
			}
			// 测试读取
			else if (main_time < 300)
			{
				if (main_time % 10 == 1)
				{
					top->raddr_i = read_addr;
					read_addr += 1;
				}
			}
			// 重新装填变量
			else if (main_time == 300) {
				write_addr = 100;
				read_addr = 100;
				write_data = 0x55667700;
			}
			// 边写边读
			else
			{
				if (main_time % 10 == 1)
				{
					top->raddr_i = read_addr;
					top->waddr_i = write_addr;
					top->wdata_i = write_data;
					write_addr += 1;
					write_data += 2;
					read_addr += 1;
				}
				if (main_time % 10 == 2) {
					top->we_i = 1;
					top->we_i = 1;
				}
			}
		}
		top->eval();
		tfp->dump(main_time);
		main_time++;
	}

	// clean
	tfp->close();
	delete top;
	delete tfp;
	exit(0);
	return 0;
}