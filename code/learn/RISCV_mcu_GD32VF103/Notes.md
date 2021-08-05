## 两个开发环境

### 1. VSCode + PlatformIO

【西部数据】RISC-V汇编语言教程
https://www.bilibili.com/video/BV1eJ411t7JS/?spm_id_from=333.788.recommend_more_video.1

* 参考资料
  * RISC-V-Reader-Chinese-v2p1
* 硬件
  * 开发板：HiFive1 Rev B https://www.crowdsupply.com/sifive/hifive1-rev-b
* 软件
  * 开发环境：vscode
    * vscode的几个插件
      * C/C++
      * Markdown All in One
      * vscode-icons
      * vscode-pdf
    * PlatformIO IDE插件
* superBlink点灯项目
  * platformIO在创建C项目，准备几个空的函数
    * setupGPIO, setLED, delay 等
  * 汇编代码
    * gpio.inc
    * memory_map.inc
    * setupGPIO.S

### 2. SEGGER Embedded Studio

* 感觉这个环境更加简单，好用。

