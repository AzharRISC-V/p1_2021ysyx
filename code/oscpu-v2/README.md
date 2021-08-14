# oscpu-framework

这是一个基于`verilator`的`RISC-V`CPU开发仿真框架。  

开发前请在`myinfo.txt`文件中填写报名`一生一芯`时的学号和自己的姓名。例如：

```
ID=202100001
Name=张三
```

# 开发环境

操作系统：[Linux Ubuntu v20.04](https://ubuntu.com/download/desktop)  

开发软件：[verilator](https://verilator.org/guide/latest/)、[gtkwave](http://gtkwave.sourceforge.net/)

verilator要求统一使用`v4.204`版本，可以从[这里](https://oscpu.github.io/ysyx/events/2021-07-09_Verilator/verilator_installer.tar.gz)下载安装包。使用下面的命令安装`verilator`和`gtkwave`。

```
# 安装verilator，需要先下载verilator的安装包
tar vxf verilator_installer.tar.gz
./install_verilator.sh
# 安装gtkwave
sudo apt-get install gtkwave
```

关于开发环境的详细安装流程，可参考[讲座-Verilator介绍](https://oscpu.github.io/ysyx/events/events.html?EID=2021-07-09_Verilator)。

# 获取代码

```
git clone --recursive -b 2021 https://github.com/OSCPU/oscpu-framework.git oscpu
```

如果子仓库克隆失败，可在`oscpu`目录下使用下面的命令重新克隆子仓库。

```
git submodule update --init --recursive
```

参与`一生一芯`还需要设置git信息。

```
# 使用你的编号和姓名拼音代替双引号中内容
git config --global user.name "2021000001-Zhang San"
# 使用你的邮箱代替双引号中内容
git config --global user.email "zhangsan@foo.com"
```

# 编译NEMU

`香山difftest框架`依赖`NEMU`的支持，本项目已经集成`NEMU`和`香山difftest框架`，编译`香山difftest框架`之前，需要安装编译`NEMU`所需的软件包。

```
sudo apt-get install libreadline-dev libsdl2-dev bison
```

如果内存小于8G，编译该工程之前，需要修改`NEMU`和`香山difftest框架`的ram大小。

修改`NEMU`的ram大小：

```
cd libraries/NEMU
export NEMU_HOME=`pwd`
make defconfig riscv64-xs-ref_defconfig
make menuconfig
#进入Memory Configuration菜单，将Memory size的值修改为0x10000000，回车，保存，退出
make
```

修改`香山difftest框架`的ram大小，文件：`libraries/difftest/src/test/csrc/common/ram.h`。

```
#define EMU_RAM_SIZE (256 * 1024 * 1024UL)
//#define EMU_RAM_SIZE (8 * 1024 * 1024 * 1024UL)
```

对于`NEMU`更新后导致的`香山difftest框架`编译或运行报错，可以在清除`NEMU`编译的文件后运行build.sh来重新编译`NEMU`。

```
cd libraries/NEMU
export NEMU_HOME=`pwd`
make clean
```

对于`香山difftest框架`更新导致的编译或运行报错，也可通过`build.sh`中的`-c`选项删除`build`目录后重新编译工程。

# 例程

我们提供了脚本`build.sh`用于自动化编译、仿真和查看波形。下面是`build.sh`的参数说明，也可在oscpu目录下使用`./build.sh -h`命令查看帮助。

```
-e 指定一个例程作为工程目录，如果不指定，将使用"cpu"目录作为工程目录
-b 编译工程，编译后会在工程目录下生成"build"(difftest)或"build_test"子目录，里面存放编译后生成的文件
-t 指定verilog顶层文件名，如果不指定，将使用"top.v" 或"SimTop.v"(difftest)作为顶层文件名，该参数在接入difftest时无效
-s 运行仿真程序，即"build/emu"程序，运行时工作目录为"build"(difftest)或"build_test"子目录
-a 传入仿真程序的参数，比如：-a "1 2 3 ......"，多个参数需要使用双引号
-f 传入c++编译器的参数，比如：-f "-DGLOBAL_DEFINE=1 -ggdb3"，多个参数需要使用双引号，该参数在接入difftest时无效
-l 传入c++链接器的参数，比如：-l "-ldl -lm"，多个参数需要使用双引号，该参数在接入difftest时无效
-g 使用gdb调试仿真程序
-w 使用gtkwave打开工作目录下修改时间最新的.vcd波形文件
-c 删除工程目录下编译生成的"build"文件夹
-d 接入香山difftest框架
-m 传入difftest框架makefile的参数，比如：-m "EMU_TRACE=1 EMU_THREADS=4"，多个参数需要使用双引号
```

## 编译和仿真

`projects`目录下几个例程可用于了解如何基于`Verilator`和`香山difftest框架`来开发仿真CPU。 

### counter

`examples/counter`目录下存放了4位计数器的例程源码。可以使用下面的命令编译和仿真。

```
./build.sh -e counter -b -s
```

如果`Verilator `安装正确，你会看到下面的输出

```
Simulating...
Enabling waves ...
Enter the test cycle:
```

输入测试周期数后仿真程序退出，并在`projects/counter/build_test/`路径下生成`.vcd`波形文件。

### cpu

`projects/cpu`目录下存放了单周期`RISC-V`CPU例程源码，源码实现了`RV64I`指令`addi`。可以使用下面的命令编译和仿真。

```
./build.sh -b -t rvcpu.v -s
```

输入`inst.bin`和回车后程序结束运行，并在`projects/cpu/build_test/`路径下生成`.vcd`波形文件。其中`inst.bin`为`bin`目录下的一个`RISC-V`测试程序，里面存放了3条`addi`指令。

### cpu_diff

`projects/cpu_diff`目录下存放了接入`香山difftest框架`的单周期`RISC-V` CPU例程源码，源码实现了`RV64I`指令`addi`。关于`香山difftest框架`的详细介绍，可参考[讲座-Difftest 处理器验证方法介绍](https://oscpu.github.io/ysyx/events/events.html?EID=2021-07-17_Difftest)。可以使用下面的命令编译和仿真。

```
# 编译仿真
./build.sh -e cpu_diff -d -b -s -a "-i inst_diff.bin"
# 编译仿真，并从CPU上报至difftest的时钟周期0开始输出波形
./build.sh -e cpu_diff -d -b -s -a "-i inst_diff.bin --dump-wave -b 0" -m "EMU_TRACE=1" 
```

仿真程序运行后，终端将打印绿色的提示内容`HIT GOOD TRAP at pc = 0x8000000c`。说明程序运行到自定义的`0x6b`指令，并且此时存放错误码的`a0`寄存器的值为0，即程序按照预期结果成功退出。关于`0x6b`自定义指令作用，可参考[讲座-AM运行环境介绍](https://oscpu.github.io/ysyx/events/events.html?EID=2021-07-13_AM_Difftest)。如果指定输出波形，将在`projects/cpu_diff/build/`路径下生成`.vcd`波形文件。

### cpu_axi_diff

`projects/cpu_diff`目录下存放了通过`AXI总线`接入`香山difftest框架`的单周期`RISC-V`CPU例程源码，源码实现了`RV64I`指令`addi`和`AXI总线`读逻辑。可以使用下面的命令编译和仿真。

```
./build.sh -e cpu_axi_diff -d -s -a "-i inst_diff.bin --dump-wave -b 0" -m "EMU_TRACE=1 WITH_DRAMSIM3=1" -b
```

## 查看波形

在`oscpu`目录下使用命令可以通过`gtkwave`查看输出的波形，其中`xxx`表示例程名。

```
# 未接入difftest
./build.sh -e xxx -w
# 接入difftest
./build.sh -e xxx -d -w
```

# 回归测试

在实现了能够运行所有`cpu-tests`和`riscv-tests`测试用例的指令后，可以通过以下命令对CPU进行一键回归测试。该命令会将`bin`目录下的所有`.bin`文件作为参数来调用接入了`香山difftest框架`的仿真程序，其中`xxx`表示例程名。

```
./build.sh -e xxx -b -r
```

通过测试的用例，将打印`PASS`。测试失败的用例，打印`FAIL`并生成对应的log文件，可以查看log文件来调试，也可以另外开启波形输出来调试。

# 扩展

[一生一芯官网](https://oscpu.github.io/ysyx/)

[会议汇总](https://oscpu.github.io/ysyx/events/)

[讲座回放](https://www.bilibili.com/video/BV1PU4y1V7X3)

[RISC-V Unprivileged Spec](https://github.com/riscv/riscv-isa-manual/releases/download/Ratified-IMAFDQC/riscv-spec-20191213.pdf)

[RISC-V Privileged Spec](https://github.com/riscv/riscv-isa-manual/releases/download/Ratified-IMFDQC-and-Priv-v1.11/riscv-privileged-20190608.pdf)

[cpu-tests](https://github.com/NJU-ProjectN/am-kernels)

[riscv-tests](https://github.com/NJU-ProjectN/riscv-tests)

[香山difftest框架](https://github.com/OpenXiangShan/difftest)

[NEMU](https://github.com/OpenXiangShan/NEMU)

[DRAMsim3](https://github.com/OpenXiangShan/DRAMsim3)

[AXI4 specification](http://www.gstitt.ece.ufl.edu/courses/fall15/eel4720_5721/labs/refs/AXI4_specification.pdf)

