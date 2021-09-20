#include <am.h>
#include <klib.h>

static Context* (*user_handler)(Event, Context*) = NULL;

Context* __am_irq_handle(Context *c) {
  if (user_handler) {
    Event ev = {0};
    switch (c->cause) {
      case 0x800000000007: //!
        ev.event = EVENT_IRQ_TIMER;
        break;
      case 11:
        if (c->GPR1 == -1) {
          ev.event = EVENT_YIELD;   // 环境调用异常
          c->epc += 4;    // mepc要比保存之前的加4，因为保存时为ecall所在的pc，需要返回到下一条指令
          // 为何不在一开始不赋值为 +4 的位置？因为riscv有规定出现异常时mepc为当前的（出现异常时的）pc
          // 所以只能在软件上处理
        }
        else {
          ev.event = EVENT_SYSCALL;
        }
        break;

      default: 
        ev.event = EVENT_ERROR; 
        break;
    }

    c = user_handler(ev, c);
    assert(c != NULL);
  }

  return c;
}

extern void __am_asm_trap(void);

bool cte_init(Context*(*handler)(Event, Context*)) {
  // initialize exception entry
  asm volatile("csrw mtvec, %0" : : "r"(__am_asm_trap));

  // register event handler
  user_handler = handler;

  return true;
}

Context *kcontext(Area kstack, void (*entry)(void *), void *arg) {
  return NULL;
}

void yield() {
  // ecall指令，通过引发环境调用异常来请求执行环境
  asm volatile("li a7, -1; ecall");
}

bool ienabled() {
  return false;
}

void iset(bool enable) {
}
