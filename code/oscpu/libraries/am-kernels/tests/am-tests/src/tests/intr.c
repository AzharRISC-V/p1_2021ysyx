#include <amtest.h>

Context *simple_trap(Event ev, Context *ctx) {
  switch(ev.event) {
    case EVENT_IRQ_TIMER:
      printf("==AA\n");
      putch('t'); break;
    case EVENT_IRQ_IODEV:
      printf("==BB\n");
      putch('d'); break;
    case EVENT_YIELD:
      printf("==CC\n");
      putch('y'); break;
    default:
      printf("==DD\n");
      break;
  }
  return ctx;
}

void hello_intr() {
  printf("Hello, AM World @ " __ISA__ "\n");
  printf("  t = timer, d = device, y = yield\n");
  io_read(AM_INPUT_CONFIG);
  iset(1);
  while (1) {
    // for (volatile int i = 0; i < 10000000; i++) ;
    for (volatile int i = 0; i < 100; i++) ;
    yield();
  }
}
