## 一生一芯的子项目

* RISCV64

  ```
  RV64指令集
  寄存器宽度是64bit
  指令宽度总是32bit
  ```
  
  
  
* 项目列表

  ```
  verilator					开源的SystemVerilog仿真器和lint系统，将verilog转换为C程序快速仿真
  	SystemVerilog	基于IEEE1364-2001 Verilog，并进行了扩展，扩充了包括C语言数据类型、结构、压缩和非压缩数组、接口、断言等，使得它在一个更高的抽象层次上提高了设计建模的能力。见：https://www.cnblogs.com/qiyuexin/p/6379887.html
  waveform					开源的波形查看器
  abstract-machine			对上层应用程序封装了ISA差异的中间件
  am-kernels					采用am接口的一组应用
  	test/cpu-tests			第一阶段的CPU指令测试
  oscpu-framework				一生一芯cpu项目的代码框架，包含了verilator,difftest等技术
  nemu						一个支持多ISA的模拟器
  difftest					一种测试技术，利用nemu与verilator产生的真机运行结果进行比对
  	这个库用于学习原理，原本用于NutShell到。而一生一芯是定制过的版本。
  qemu						difftest当初开发nemu库时使用的REF模拟机
  OpenXiangShan/difftest		独立的difftest框架，依赖特定版本的NEMU（模拟器）
  OpenXiangShan/xs-env		对应版本的其他项目
  	NutShell		果壳，接入了difftest框架
  	NEMU			配套的模拟器
  SDL							跨平台的多媒体库，用于VGA设备模拟
  QEMU						著名的开源模拟器，用于同NEMU的REF
  riscv-tests					第二阶段的cpu测试
  ```
  
  
  
* 2021ysyx （我个人的仓库）

  ```
  自己的一个仓库
  ```
  
* verilator项目

  ```
  use special version
  install gtkwave
  ```
  
  
  
* abstract-machine, am-kernels 项目

  ```
  作用：
  将ISA与应用分离的一个中间件am，以及在此中间件am之上的应用层am-kernels。
  利用这些库来检查自己CPU实现的正确性。
  方法：将生成的bin文件作为oscpu-framework中的inst.bin，利用verilator来检查当执行到0x6b指令时寄存器a0的值是否为0。但是后面引入DiffTest是更好的方法。
  
  1. 交叉编译环境
  sudo apt-get install g++-riscv64-linux-gnu binutils-riscv64-linux-gnu
  2. 获取源代码
  git clone https://github.com/NJU-ProjectN/am-kernels.git
  git clone -b ysyx2021 https://github.com/NJU-ProjectN/abstract-machine.git
  3. 设置环境变量
  echo export AM_HOME=$(pwd)/abstract-machine >> ~/.bashrc
  source ~/.bashrc
  4. am-kernels/tests/cpu-tests 对CPU指令实现的测试，riscv-tests是把rv64i的测试移植到了AM。
  程序难易排行：
      最简单的 dummy
      入门的 add
      需要string的 hello-str
      需要putch的 string
  执行编译
  	make ARCH=riscv64-mycpu ALL=add
  	作用：编译add.o, 以及am和klib目录，并打包为 am.a, klib.a，然后用ld链接生成elf，再用objcopy得到add程序的指令和数据，二进制保存在.bin文件，反汇编保存在.txt文件。
  	注意，mycpu平台仅仅是为了生成二进制文件，并不需要用nemu测试
  	make ARCH=risv64-nemu ALL=add
  	作用：使用NEMU模拟器，需要NEMU项目。$NEMU_HOME环境变量作为桥梁。
  	另外，mycpy和nemu中的一些地址设定也不同，注意区分。
  5. AM/mycpu提供了什么？
  a. 初始化函数
  在ld中使用 -e _start 指定了程序入口，该函数位于 start.S中，它设置指针，跳转至 _trm_init()。
  _trm_init执行 int ret = main(); halt(ret);
  b. 停机函数
  修改为
  void halt(int code) {
  	asm volatile("mv a0, %0; .word 0x0000006b" : : "r"(code));
  	while (1);
  }
  对应的汇编代码：
  00050513		mv a0, a0
  0000006b		0x6b
  c. 检查原理
  main()返回值保存在a0，halt使得cpu在读到0x6b指令时可根据a0来判断是否通过了add测试
  d. putch
  暂时没有介绍输入输出，所以cpu还没有输入输出功能，可参考halt实现添加自定义指令，在仿真中输出一个字符。
  比如verilog中$write()输出寄存器中存放的字符。
  void putch(char ch) {
  	asm volatile("mv a0, %0; .word ??" : : "r"(ch));
  }
  ```

  

* oscpu-framework 项目

  ```
  1. 主仓库
  git clone --recursive -b 2021 https://github.com/OSCPU/oscpu-framework.git oscpu
  
  2. 子仓库如果失败，还需重新克隆子仓库
  git submodule update --init --recursive
  
  3. 编译和仿真 counter
  $ ./build.sh -e counter -b -s
  
  3. cpu项目
  $ ./build.sh -b -t rvcpu -s
  $ inst.bin
  这里是三条addi指令和一条nemutrap自定义指令
  00100093	li ra,1			等价于 addi ra,zero,1
  00200093	li ra,2			等价于 addi ra,zero,2
  00108093	addi ra,ra,1
  0000006B	0x6b
  
  4. cpu_diff项目
  $ ./build.sh -e cpu_diff -d -b -a "-i inst_diff.bin --dump-wave -b 0" -m "EMU_TRACE=1"
  编译失败，虚拟机内存给8G解决。
  ------------------
  设置环境变量。使用 build.sh时可不设置，但emu直接运行时需要设置
  $ cd oscpu
  $ echo export NOOP_HOME=$(pwd) >> ~/.bashrc
  $ cd libraries/NEMU
  $ echo export NEMU_HOME=$(pwd) >> ~/.bashrc
  $ source ~/.bashrc
  ------------------
  使用 am-kernels 中的测试用例
  a. 编译cpu-tests所有项目
  $ cd ../am-kernels/tests/cpu-tests/
  $ make run
  b. 拷贝需要的bin文件
  $ cd build
  $ cp *.* ../../../../oscpu-local/bin/
  c. 测试
  $ make				# 使用默认的 inst_bin 编译
  $ make run			# 使用默认的 inst_bin 编译，并运行
  $ make ALL=add		# 使用自定义的bin编译
  $ make ALL=add run	# 使用自定义的bin编译，并运行
  
  5. 再次总结编译注意事项
  a. 设置 AM_HOME, NEMU_HOME, NOOP_HOME
  b. 清理 libraries/NEMU/build, libraries/DRAMsim3/build, projects/cpu_diff/build/
  c. 虚拟机内存至少7GB
  d. make or make run or make run ALL=add
  ```

* difftest项目

  ```
  1. 主仓库
  https://github.com/OpenXiangShan/difftest.git
  2. AXI总线，valid/ready握手机制
  https://blog.csdn.net/luxinwylive/article/details/99672825
  # AXI总线共有5个独立的通道，分别为写地址wa,写数据w,写回应r,读地址ra,读数据rd通道。它们有一些细小的差别，但共同使用一套握手机制：VALID/READY机制
  # ARM上写到：作为一种双向流控机制，VALID/READY机制可以使双方都有能力传输速率
  # 发送方置高VALID表示发送方已经将数据，地址或控制信息放到了写总线，并保持。
  # 接收方置高READY表示接收方已经做好接收的准备。
  # 协议规定：VALID信号一旦置高就不能拉低，直到此次传输传输完成。对于接收方，检测到VALID信号置起，如果系统在忙，完全可以让发送方等待，发送方在完成传输之前都不会置低VALID信号，不需要考虑发送方撤销传输的可能。
  # 协议还规定：发送方不能在置起VALID信号之前就光等待READY信号。换言之，发送方准备发送时，置起VALID信号是完全主动的过程。
  # READY信号很自由，可以等待VALID信号到来之后再做响应，也可以在VALID信号到来前就置高，表示接收端已经做好准备了。
  # READY信号与VALID信号不同，接收方可以置起READY之后发现：其实我好像还挺忙，然后拉低READY信号（前提是，只要此时VALID信号还没有置起）。
  # 当双方的信息同时为高，时钟上升沿到达后，一次数据传输完成，在1到n个时钟上升沿后，双方完成了要传输的信息后，两信号同时拉低。
  ----------------
  另一种解释：
  # 生产者准备好数据将标志位VALID置位，消费者准备好接收数据将标志位READY置位，在时钟沿同时出现VALID和READY置位，则完成数据传输。
  # 系统中所有信号在时钟信号的上升沿取样。valid信号在复位后置低，其他信号无要求。
  ```

  

* cpu-tests 项目

  ```
  这是第一阶段的CPU测试，位于 am-kernels/test/cpu-tests，现已通过。
  其中 hello-str, string 需要在 am/klib 中实现几个简易版本的库函数。
  ```

* riscv-tests

  ```
  这是第2阶段的cpu测试，
  现在发现有两个版本，估计核心的源码相同，只是脚本不同。
  1. https://github.com/riscv/riscv-tests					这是原版的
  2. https://github.com/NJU-ProjectN/riscv-tests    		这是定制过的
  注意submodule的更新，指令如下：
  git clone xx
  git submodule update --init --recursive
  ```

  * native运行

    ```
    编译指令
    $ cd am-kernels/tests/am-tests
    $ make ARCH=native run mainargs=xxx
    为运行不同子任务，设定mainargs参数
    	在native中，make的这种参数会被 am/arc/native/platform.c:init_platform中的 getenv()函数接收，不知道原理
    	在mycpu中，使用编译时刻给CFLAGS传递 -DMAINARGS=xx来实现，具体参考 riscv64-mycpu.mk中的 CFLAGS设定，以及 mycpu/trm.c中的 mainargs变量。
    	总之，native与mycpu都是在编译时在make中给定mainargs参数，已达到运行不同子任务的目的。
    ```

  * riscv64-mycpu运行

    ```
    编译
    $ cd am-kernels/tests/am-tests
    $ make ARCH=riscv64-mycpu mainargs=xxx
    安装，将 bin 拷贝至 oscpu/bin
    $ make install
    运行，在oscpu中当做普通的bin文件输入，用difftest比对即可。
    ```

  * 子程序 hello，很简单

  * 子程序 rtc_test，需要实现 timer, rtc

* 
