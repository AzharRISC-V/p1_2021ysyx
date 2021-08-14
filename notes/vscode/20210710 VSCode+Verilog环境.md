## VSCode使用

* 文本文件比较，左侧选择两个文件，右键进行比较

* 快捷键

  ```
  Ctrl + F	查找
  Ctrl + H	替换
  Ctrl + /	注释/取消注释
  Alt + Up/Down		移动选中内容
  扩展光标可以垂直操作，方便verilog中书写代码
  Ctrl + Alt + Up/Down		扩展光标
  Ctrl + Shift + Alt + Up/Down		可以垂直选择一个区域
  ```

* 使用不同编码打开文件

  在右下角UTF-8位置，点击，选择 使用编码重新打开

## 环境配置

补充：

FPGA超级入门教程：https://www.zhihu.com/column/c_1117750063287488512

* 安装 iverilog

  http://bleyer.org/icarus/

  选择 x64.exe

  记得将 iverilog.exe 和 gtkwave.exe 所在文件夹加入环境变量

  在命令行测试：

  ```
  > iverilog -help
  > gtkwave
  ```

  如果是ubuntu

  ```
  sudo apt install iverilog gtkwave
  ```

* 用 iverilog 完成一个hello world

  编辑

  ```
  module hello;
  	initial begin
  		$display("hello world");
  		$finish;
  	end
  endmodule
  ```

  编译

  ```
  > iverilog -o hello hello.v
  > vvp hello
  hello world
  .\hello.v:4: $finish called at 0 (1s)
  ```

  注意

  1. 生成的 hello 可以被vvp解释执行。
  2. 如果报错“没有指明顶层模块，可能是文件编码方式需要修改为UTF-8（不是UTF-8 with BOM)

* vscode的插件

  ```
  注意：
  Coq 和 Verilog 都使用 .v 为后缀。这两组有冲突。可以先禁用Coq的功能
  
  安装三个插件
  Verilog-HDL/SystemVerilog/Blue  提供Verilog源文件的语法高亮，自动补全，错误检查（linting）
  Verilog HDL   提供一个绿色按钮，可以一键编译执行一个verilog源文件（就是 iverilog ...; vvp )
  Verilog Snippet  一键补全固定语法格式的插件
  配置
  1. 打开设置，输入verilog
  2. 将 verilog 的 linter 改成 iverilog
  ```

* 多个verilog文件时，iverilog会报实例化错误，它现在还不智能，可用 -i 参数来抑制这种错误

  参看下一节来了解如何进行多文件编译

  ```
  VSCode Setting -> Verilog-Linting - Iverilog: Arguments
  > -i
  ```

* 更多插件

  * 让注释有突出颜色的标记，比如 标记todo

    Better Comments

  * 让括号拥有更清楚的颜色

    Rainbow Brackets
  
  * wavetrace

## iverilog的一些事项

* timescale的设置

  ```
  `timescale 10ns/10ns	// 时间单位10ns，时间精度1ns
  // 时间单位需要大于等于时间精度
  // 在 iverilog中，简化了，只能是 1, 10, 100。单位可以是 ps, ns, 等
  // 时间单位乘以数字值就是实际的延时时间。
  ```

* 多文件编译方法一

  ```
  // v1.v
  module v1;
  	initial $display("v1");
  endmodule
  
  // main.v
  `include "v1.v"
  module main;
  	v1 u_v1();
  endmodule
  
  // 编译
  $ iverilog -o main main.v v1.v
  $ vvp main
  ```

* 多文件编译方法二

  ```
  文件编写同上。
  使用 -c 参数，传入txt文本文件
  // commandfile.txt
  main.v
  v1.v
  
  // 编译
  $ iverilog -o main -c commandfile.txt
  $ vvp main
  ```

* 多文件编译方法三（暂时不可行）

  ```
  不需要使用 include 指令来包含。
  使用新的插件 FPGA Develop Support, 很强大
  1. 不使用 include 包含文件，自动分析出文件关系
  2. 配置，
    删除或禁用 Verilog-HDL/SystemVerilog/Bluespec SystemVerilog插件，因功能重复
    将 Verilog - Linting:Linter 配置为 none
    将 HDL - Linting - Linter 配置为 iverilog
    再设置 TOOL, Gtkwave, Install:Path
    	D:/DevTools/iverilog/gtkwave/bin/
    再设置 TOOL, IVerilog, Install:Path
    	D:/DevTools/iverilog/bin/
    (别忘记最后的斜杠)
  3. 补充说明
    该工具有创建 instance 的功能
  ```

### 另一种插件方案

* 插件

  ```
  先安装 iverilog 软件
  安装 Verilog HDL 插件
  安装自动例化插件 verilog-utils
  ```

* 编写 verilog 文件，不需要 include 

* 编译

  ```
  iverilog -o tb *.v
  vvp -n tb -lxt2
  gtkwave test_tb.lxt
  iverilog -tvhdl -o test.vhd test.v
  pause
  ```

* 额外功能：

  * 语法错误检查

    ```
    在要检查的文件中，使用命令面板 Ctrl + Shift + P
    选择 Verilog: Run Verilog HDL Code 即可
    【其实，该功能太繁琐了，只要使用 原来安装的 Verilog HDL 插件，并配置 Linting 为 iverilog 即可。带有例化时，需要使用 -i 参数 】
    ```

    

  * 例化

    ```
    复制需要例化的模块（module头部内容）
    粘贴到需要使用的位置（保持选中状态）
    右键选择命令面板（或输入 Ctrl + Shift + P)调用命令面板
    选择 Verilog Utils - Instation 即可
    ```

    

  

