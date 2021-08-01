## VSCode + Modelsim环境

* VSCode配置

  * 安装 Verilog-HDL/SystemVerilog/Bluespec SystemVerilog插件
  * 该插件需要以下之一软件的支持
    * Icarus Verilog - iverilog
    * Vivado Logical Simulation - xvlog
    * Modelsim - modelsim
    * Verilator - verilator

* Modelsim配置

  * 安装Modelsim
  * 将 vlog.exe 所在的win64目录加入系统变量
  * 任意新建项目，并新增与“default library name"同名的文件夹，里面会有一个_info文件
  * 将该目录路径复制到vscode 的 verilog > Lingting > Modelsim: Work 设置中
  * 将 Linter 改为 modelsim
  * 之后就可以用 vlog 命令进行编译。若无语法错误，基本都可以通过编译。
    * vlog test.v
    * 编译通过只是基本的语法检测。有些错误vlog检测不出来

* 最简单的方法

  * 在modelsim中管理项目
  * 在vscode中编辑文件

  