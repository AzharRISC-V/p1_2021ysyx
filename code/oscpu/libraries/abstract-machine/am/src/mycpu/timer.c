#include <am.h>

void __am_timer_init() {
}

void __am_timer_uptime(AM_TIMER_UPTIME_T *uptime) {
  // 访存，可以内存映射到设备
  // uint64_t ticks = *(volatile uint64_t *)RTC_ADDR;
  // uptime->us = ticks / TICKS_PER_US;

  // csr指令
  uintptr_t mcycle;
  asm volatile("csrr %0, mcycle" : "=r"(mcycle));

  uptime->us = mcycle;
}

void __am_timer_rtc(AM_TIMER_RTC_T *rtc) {
  rtc->second = 0;
  rtc->minute = 0;
  rtc->hour   = 0;
  rtc->day    = 0;
  rtc->month  = 0;
  rtc->year   = 1900;
}
