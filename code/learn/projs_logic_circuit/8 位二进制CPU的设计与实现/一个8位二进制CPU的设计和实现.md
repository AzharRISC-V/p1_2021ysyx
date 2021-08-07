## Logical Circuit 软件

* 软件官网及介绍

  https://logiccircuit.org

  Version 2.21.01.10 released.
  14 January 2021

* 软件使用

  * 快捷键
    * 模拟开始：Ctrl + W
  * 技巧
    * 新增电路，修改电路Name,Notation
    * Select Free Wires 选择没有连接的线。
    * 与门、非门等的封装（非常简单）
    * 连线时有折线，需要点击量词鼠标。
    * 连线交叉位置，先选中一条线，然后按住Alt，点击焦点即可增加节点。

## 一个8位二进制CPU的设计和实现

* B站视频地址

  https://space.bilibili.com/491131440/channel/detail?cid=163546

  https://www.bilibili.com/video/BV1W5411p7Ax/?spm_id_from=autoNext

* 半加器

  * 真值表

  | A    | B    | S    | C    |
  | ---- | ---- | ---- | ---- |
  | 0    | 0    | 0    | 0    |
  | 0    | 1    | 1    | 0    |
  | 1    | 0    | 1    | 0    |
  | 1    | 1    | 0    | 1    |
  * 逻辑公式

  $$
  \begin{aligned}
  S =& \overline{A} B + A \overline{B} \\
  C =& AB
  \end{aligned}
  $$

* 全加器

  * 多种实现方法
  * 利用查找表的方式
    * ROM (3地址，2数据)

* 取反器

  * 1位取反器

    * EN控制是否取反，I是输入，O是输出

    * 真值表

      | EN   | I    | O    |
      | ---- | ---- | ---- |
      | 0    | 0    | 0    |
      | 0    | 1    | 1    |
      | 1    | 0    | 1    |
      | 1    | 1    | 0    |

    * 其实就是异或门

  * 8位取反器

  * 减法进位真值表

    | CI(进位输入 & 是否减法标志) | CO(进位输出) | O（实际输出） |
    | --------------------------- | ------------ | ------------- |
    | 0                           | 0            | 0             |
    | 0                           | 1            | 1             |
    | 1                           | 0            | 0             |
    | 1                           | 1            | 0             |

    含义：CI = 0，加法电路，此时，CO有效。CI=1，减法电路，此时，CO无效。

    公式：
    $$
    \begin{aligned}
    O = \overline{CI} ~ CO
    \end{aligned}
    $$

  * 

  * 七段十进制数码管
  * 