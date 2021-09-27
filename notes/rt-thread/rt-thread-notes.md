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
    * 
    * 

  