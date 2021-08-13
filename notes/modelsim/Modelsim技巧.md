## Modelsim技巧

* ModelSim软件配置

  * tab配置为4

  * 字体配置

  * 更改为默认编辑器

    * 从preference中查找editor即可
    * 需要在windows中更改为modelsim.exe打开.v文件
    * 可能还要删除 \HKEY_CURRENT_USER\SOFTWARE\Model Technology Incorporated\ModelSim ，还原到默认值

  * 更改为vscode

    ```
    在Transcript中输入
    proc external_editor {filename linenumber} { exec "D:\\DevTools\\Microsoft VS Code\\Code.exe" $filename }
    再输入
    set PrefSource(altEditor) external_editor
    ```

    

* 仿真和调试的对应关系

  | 并行语言 | 顺序语言 |
  | -------- | -------- |
  | 仿真     | 调试     |
  | 功能仿真 | 下线调试 |
  | 行为仿真 | 上线调试 |

  补充解释：

  * 调试只会输出步骤的结果却无视指令的内容，它也无视时钟的消耗数。
  * 所谓的并行语言犹如VHDL或Verilog HDL等各种描述语言，描述语言不像顺序语言有步骤支持整体的顺序结构，结果描述语言的结构自由，甚至称为没有结构的地步。顺序语言每一个关键字都在暗示处理器的处理行为，然后描述语言每一个关键字只是描述手段，我们用它在白纸上绘出我们想要的“形状”。
  * 顺序语言每个时钟只能执行一个步骤（若这个步骤能在一个时钟内完成的话）。而并行语言可在一个时钟内执行千千万万个步骤，上限没有尽头。顺序语言不关心时钟，因为时钟不仅隐藏而且无法控制，反之并行语言的时钟不仅开放也能控制。
  * 调试是追求单向结果，调试用来断定某个信号在某个时钟的某个结果。仿真时追求多向过程，即N个信号在所有个时钟发生的结果。

* 