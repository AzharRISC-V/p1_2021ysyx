# oscpu-framework
A Verilator-based framework.

Please fill your information in myinfo.txt.

For example:  
ID=202100001  
Name=张三  

Use "./build.sh -h" command under Ubunutu terminal to get the build instructions.

# Some notes for development
* Extensions for VSCode
  - Better Comments
  - Rainbow Brackets
  - WaveTrace
  - Verilog-HDL/SystemVerilog/Blue..
    + Setting, verilog linter : verilator
  - Hex Editor
  - C/C++

* VSCode skill
  - format code: Ctrl + Shift + I
  - close preview window right hand: 
    - “关闭预览功能方法:点击—文件----首选项----设置-----用户设置-----文本编辑器----小地图----取消对勾。”
  - 无法输入中文
    - 因为 snap 方式安装的版本被精简了。首先卸载snap版本： sudo snap remove code，然后从 code.visualstudio.com 中下载 deb 文件，然后安装: sudo dpkg -i xx.deb
  - verilog formatter
    - Verilog Format 插件
      * 该插件还需要一些配置，还需要安装 Java 环境，按照说明配置即可。
        具体的，从 $ git clone https://github.com/ericsonj/verilog-format.git 下载后得到 verilog-format 可执行程序。
      * 在 vscode 中，设置 verilog-format path即可
  - 设置换行
    - 一个个文件的修改，打开文件在右下角单击 LF / CRLF 等字样，保存即可
    - 设置默认值，> settings > files.eol，设置为固定值

* 异常情况
  - build.sh 报错 %Warning-EOFNEWLINE: regfile.v:1:3: Missing newline at end of file (POSIX 3.206).
    - 查了半天，可能是 CRLF 换成 LF，还可能是 /* xxx */ 开头的中文注释需要先禁止掉
## RISC-V 指令分析
  - 指令类型分析
    - R-type, x[rd] = f(x[rs1], x[rs2])
    - I-type, x[rd] = f(x[rs1], sext(imm))
    - 
