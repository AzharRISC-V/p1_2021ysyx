#include <am.h>

void __am_timer_init() {
}

void __am_timer_uptime(AM_TIMER_UPTIME_T *uptime) {
  uint64_t cycle = 0;
  asm volatile("csrr %0, mcycle" : "=r"(cycle) : );
  /*
      8000248c:	b00027f3          	csrr	a5,mcycle
    80002490:	00f53023          	sd	a5,0(a0)
    80002494:	00008067          	ret
    */
  // asm volatile("addi sp,sp,-8");
  // asm volatile("")
  // ; li s11,0");
  // asm volatile("csrr s11, mcycle");// : "=r"(mcycle_val));
  // asm volatile("sd s11,0(a0)");

  // 注意:
  // 1. 这里的换算系数需要同 verilog_code/devices/rtc.v 中的设计一致，因为硬件时钟周期并不是外界的时间。
  // 2. 目前是 1秒240万个周期，要换算成 1秒100万个周期（也就是us），所以 cycle需要除以2.4
  // 3. 但是直接使用 cycle / 2.4 则生成 fcvt.d.lu 汇编指令，而现在的处理器还不支持乘除，以及浮点，换个写法
  //    cycle * 10 / 24，这样的指令是可以的，内部会用整数指令来模拟乘除。
  uptime->us = cycle * 10 / 24;
}

void __am_timer_rtc(AM_TIMER_RTC_T *rtc) {

  uint64_t rtc_val = *((uint64_t *)0x20000100);

  rtc->second = (rtc_val >> 0) & 0x3F;
  rtc->minute = (rtc_val >> 6) & 0x3F;
  rtc->hour   = (rtc_val >> 12) & 0x3F;
  rtc->day    = (rtc_val >> 18) & 0x1F;
  rtc->month  = (rtc_val >> 23) & 0xF;
  rtc->year   = (rtc_val >> 27) & 0xFFFF;
}
