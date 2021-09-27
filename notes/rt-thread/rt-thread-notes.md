## RT-Thread的启动流程分析

### 正常流程

* entry() 在 components.c，系统入口
  * rtthread_startup() 在 components.c，启动系统
    * rt_hw_interrupt_disable，禁中断
    * rt_hw_board_init，板级初始化
    * rt_show_version，显示logo
    * rt_system_timer_init，定时器初始化
    * rt_system_scheduler_init
    * rt_system_signal_init
    * rt_application_init
      * rt_thread_create("main") 或 rt_thread_init("main")
      * rt_thread_startup()
    * rt_system_timer_thread_init，定时器线程
      * rt_thread_init，创建静态线程
      * rt_thread_startup，启动该线程
    * rt_thread_idle_init，空闲线程
      * rt_thread_init，创建静态线程
      * rt_thread_startup，启动该线程
    * rt_system_scheduler_start 在 components.c
      * rt_schedule_remove_thread
      * rt_hw_context_switch_to 在 libcpu/risc-v/virt64/context_gcc.S
        * load sp, (a0)
        * csrw mstatus, a0
        * rt_hw_context_switch_exit 在 context_gcc.S
          * mret，会跳转到相应的线程
  * rt_thread_startup(xxx) 在 thread.c ，启动一个线程
    * rt_thread_resume，将本线程暂停
    * if (rt_thread_self() != RT_NULL)  {  rt_schedule(); } 不为空时，进行调度
  * rt_thread_init，线程初始化，一个壳
    * rt_object_init，初始化一个thread对象，按数据结构创建了一些数据。
    * _rt_thread_init，线程初始化的主要工作
  * rt_thread_timer_entry，定时器线程入口
  
* 中断机制

  * trap_entry，在 libcpu/risc-v/virt64/interrupt_gcc.S

    * 部分代码

      ```
          /* handle interrupt */
          call  rt_interrupt_enter
          csrr  a0, SRC_XCAUSE
          csrr  a1, SRC_XEPC
          mv    a2, s0
          call  handle_trap
          call  rt_interrupt_leave
      
          /* switch to from_thread stack */
          move  sp, s0
      
          /* need to switch new thread */
          la    s0, rt_thread_switch_interrupt_flag
          lw    s2, 0(s0)
          beqz  s2, spurious_interrupt
          sw    zero, 0(s0)
      
          la    s0, rt_interrupt_from_thread
          LOAD  s1, 0(s0)
          STORE sp, 0(s1)
      
          la    s0, rt_interrupt_to_thread
          LOAD  s1, 0(s0)
          LOAD  sp, 0(s1)
      spurious_interrupt:
          tail rt_hw_context_switch_exit
      ```

  * handle_trap，在  libcpu/risc-v/virt64/interrupt.c

    * 主要是中断，异常会打印信息。中断只考虑 IRQ_M_TIMER ，调用 tick_isr()

  * tick_isr，在 libcpu/risc-v/virt64/interrupt.c

    * 处理时钟中断

    * 部分代码

      ```
       int tick_cycles = VIRT_CLINT_TIMEBASE_FREQ / RT_TICK_PER_SECOND;
       rt_tick_increase();
       *(uint64_t*)CLINT_MTIMECMP(r_mhartid()) = *(uint64_t*)CLINT_MTIME + tick_cycles;
      ```

    * 代码解读

      * \#define VIRT_CLINT_TIMEBASE_FREQ (10000000)，基准频率100万。

      * \#define RT_TICK_PER_SECOND 100，每秒100个tick

      * 所以，tick_cycles = 10000，每个tick时钟周期增加1万。

      * CLINT_MTIME是CPU内部在变化的，

      * CLINT_MTIMECMP，基本上是由OS来维护。经测试，目前的设计，每两次读取的数据如下

        ```
        MTIMECMP    diff_between_last
        177185400	566600
        177752000	756200
        178508200	566600
        179074800	566800
        179641600	566600
        180208200	566800
        180775000	566600
        181341600	566800
        181908400	566600
        182475000	566800
        183041800	566600
        183608400	756200
        184364600	566600
        184931200	566800
        ```

        可认为，在两次中断之间，CPU的MTIME变化值是60万左右，而OS每次增加的是1万。说明中断需要更频繁的被触发。

      * rt_tick_increase，通知该线程有一个tick到达了，当tick数递减到0时，会触发线程调度。

        该函数还额外的实现了软件定时器功能的支持，这里暂不使用。

      * 总之，现在是肉眼可见的500ms左右触发一次中断，需要更快的到达。问题在哪里？

      * 现状

        ```
        截止 2021.09.27 20:17 ，github提交的这个版本，
        每条指令约20个clock，所以这里的1M为基准，100 ticks/s, 相当于 10000个clock后发生一次中断，大约相当于500条指令。
        可以将时钟基准设置为2M，让每个时钟中断之间执行1000条指令。
        ```

        

### 09.27 启动异常分析

* entry()
  * rtthread_startup()
    * rt_hw_interrupt_disable
    * rt_hw_board_init
    * rt_show_version
    * rt_system_timer_init
    * rt_system_scheduler_init
    * rt_system_signal_init
    * rt_application_init
    * rt_system_timer_thread_init
      * rt_thread_init
      * rt_thread_startup
    * rt_thread_idle_init
      * rt_thread_init
      * rt_thread_startup
    * rt_system_scheduler_start 在 components.c
      * rt_schedule_remove_thread
      
      * rt_hw_context_switch_to (这一步会出错)
      
        已找到问题并解决，是cpu中的0x81xx_xxxx的地址未处理，设计问题。
  
* 
  * 

  