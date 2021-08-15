
#include <verilated.h>
#include <verilated_vcd_c.h>
#include <iostream>
#include <fstream>
#include "Vram.h"

using namespace std;

static Vtop *top;
static VerilatedVcdC *tfp;
static vluint64_t main_time = 0;
static vluint64_t sim_time = 1000;

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
	//read_inst(filename);

	// initialization
	Verilated::commandArgs(argc, argv);
	Verilated::traceEverOn(true);

	top = new Vram;
	tfp = new VerilatedVcdC;

	top->trace(tfp, 99); //trace 99 levels of hierarchy
	tfp->open("ram.vcd");

	vluint32_t write_addr = 1;
	vluint32_t write_data = 0x10;
	vluint32_t read_addr = 1;

	while (!Verilated::gotFinish() && main_time < sim_time)
	{
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
				/*
				 	以5为周期
					1: 给出地址
					2: wr_en = 1
					3: wr_en = 0
				*/
				if (main_time % 5 == 1)
				{
					top->addr = write_addr;
					top->data = write_data;
					write_addr += 1;
					write_data + 2;
				}
				if (main_time % 5 == 2)
					top->wr_en = 1;
				if (main_time % 5 == 3)
					top->wr_en = 0;
			}
			// 测试读取
			else
			{
				/*
				 	以5为周期
					1: 给出地址
					2: wr_en = 1
					3: wr_en = 0
				*/
				if (main_time % 5 == 1)
				{
					top->addr = read_addr;
					read_addr += 1;
				}
				if (main_time % 5 == 2)
					top->rd_en = 1;
				if (main_time % 5 == 3)
					top->rd_en = 0;
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
