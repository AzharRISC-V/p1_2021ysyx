#include <amtest.h>

#define CLINT_START 0x02000000
#define CLINT_MTIMECMP (CLINT_START + 0x4000)

Context *simple_trap(Event ev, Context *ctx) {
  switch(ev.event) {
    case EVENT_IRQ_TIMER:
      // 由于 mtime 一直在增加，这里到达中断时间后，将mtimecmp也增加，
      // 则产生了固定时间间隔产生中断的效果。
      //*((uint64_t *)CLINT_MTIMECMP) += 7000000;
      printf("t"); break;
    case EVENT_IRQ_IODEV:
      printf("d"); break;
    case EVENT_YIELD:
      printf("y"); break;
    default:
      printf("N");
      break;
  }
  return ctx;
}

void hello_intr() {
  printf("Hello, AM World @ " __ISA__ "\n");
  printf("  t = timer, d = device, y = yield\n");
  io_read(AM_INPUT_CONFIG);

  // 开中断。
  // 如果是 yield 实验，也就是环境调用异常 ecall，不需要中断即可产生（可认为是内中断）
  // 如果是 计时器中断 实验，则需要考虑它
  iset(1);;
  //for (volatile int i = 0; i < 1000; i++) ;
  //halt(0);
  while (1) {
    // for (volatile int i = 0; i < 10000000; i++) ;
    for (volatile int i = 0; i < 100; i++) ;
    //yield();
  }
}
