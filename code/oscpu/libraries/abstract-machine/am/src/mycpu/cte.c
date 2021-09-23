#include <am.h>
#include <klib.h>

static Context* (*user_handler)(Event, Context*) = NULL;

Context* __am_irq_handle(Context *c) {
  if (user_handler) {
    Event ev = {0};
    // printf("cause[0]:%x, cause[1]:%x, status:%x, epc:%x\n", c->cause, c->cause >> 32, c->status, c->epc);
    switch (c->cause) {
      case 0x8000000000000007: //!
        ev.event = EVENT_IRQ_TIMER;
        // 中断时，保存的pc就是当前这条正在执行（但尚未执行完）的指令
        // 中断返回时，不需要加4。
        // 加4时 ecall 特有的。
        break;
      case 11:
        if (c->gpr[17] == -1) {
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

  // 计时器中断：硬件自动置位 mip寄存器的 mtip 位，进入中断模式
}

bool ienabled() {
  return false;
}

#define MIE_MTIE  0x80

void iset(bool enable) {
  if (enable) {
    asm volatile("csrsi mstatus, 8");   // mstatus_MIE
    set_csr(mie, MIE_MTIE);
  } else {
    asm volatile("csrci mstatus, 8");
    clear_csr(mie, MIE_MTIE);
  }
}
