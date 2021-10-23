#include <amtest.h>

void show_cpu_copyright_info() {
  uint64_t addr = 0x02008000;
  bool bQuit = false;
  while (!bQuit) {
    // 取出8个字符
    uint64_t ch8 = *((volatile uint64_t *)addr);
    addr += 1;

    // 从低字节开始显示，碰到0停下来
    for (int i = 0; i < 8; i++) {
      uint8_t ch = ch8 & 0xFF;
      ch8 = ch8 >> 8;
      if (ch) {
        putch(ch);
      } else {
        bQuit = true;
        break;
      }
    }
  }

  putstr("\n\n");
}

void hello() {
  for (int i = 0; i < 10; i ++) {
    putstr("Hello, AM World @ " __ISA__ "\n");
  }
  show_cpu_copyright_info();
}
