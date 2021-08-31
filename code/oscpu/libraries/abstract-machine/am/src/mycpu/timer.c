#include <am.h>

void __am_timer_init() {
}

void __am_timer_uptime(AM_TIMER_UPTIME_T *uptime) {
  uintptr_t mcycle_val = 0;
  asm volatile("csrr %0, mcycle" : "=r"(mcycle_val));

  uptime->us = mcycle_val;
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
