## Makefile skills

几个优秀的案例

```
参考：
am-kernels/tests/cpu-tests/Makefile
```



1. 基本模板

   ```
   # 这里是注释
   WORK_DIR 	= $(shell pwd)					# 获得当前路径
   DST_DIR		= $(WORK_DIR)/build/$(ARCH)		# 构造另一个路径
   $(shell mkdir -p $(DST_DIR))				# 创建目录
   
   hello: hello.c
   	gcc -o $@ $<		# $@是目标，$<是第一个依赖，等价于 gcc hello.c -o hello
   
   .PHONY: clean
   
   clean:
   	rm hello
   ```

2. makefile多目标和多规则

   * makefile多目标

   ```
   特点：一个规则中有多个目标，规则所定义的命令对所有目标都有效。
   例如：
   kdb.o cmd.o files.o : common.h
   这三个目标都依赖于同一个头文件
   ```

   * makefile多规则

   ```
   特点：一个名称作为多个规则的目标
   1. 当给出多个规则时，将合并这些规则。 
   2. 对于一个对规则的目标，重建此目标的命令只能出现在一个规则中。
   3. 如果多个规则同时给出重建此目标的命令，make使用最后一个规则中所定义的命令，同时给出错误信息。
   ```

   

3. 条件语句的三个关键字

   ```
   1. ifeq 判断相等
   ifeq (a, b)
   	xxx
   else
   	xxx
   endif
   2. ifneq，与ifeq相反
   3. ifdef 判断一个变量是否已经定义
   格式与 ifeq 类似，条件部分是 (a)，而不是(a,b)两部分。
   补充说明：指示测试一个变量是否有值，不会进行替换展开来判断变量的值是否为空
   比如：
   bar =
   foo = $(bar)
   ifdef foo 的结果是真。
   4. ifndef，与ifdef相反。
   ```

   

4. 不回显当前命令

   ```
   @rm 1.txt
   作用：原本会打印"rm 1.txt"命令，现在不显示了。
   ```

5. 忽略当前命令执行失败，允许继续执行

   ```
   echo "1"
   -rm 1.txt
   echo "2"
   作用：如果1.txt不存在，则 rm 1.txt 会导致不输出2，但 -rm 1.txt 会忽略这个错误
   如果再配合 -@rm -rf 1.txt，则不会输出任何失败信息
   ```

6. make时静默执行，不输出执行结果

   ```
   make -s -f Makefile.add
   ```

7. 定义变量

   ```
   1. ?=，默认值
   	ISA ?= riscv64		# 如果不存在，则赋值，否则使用传入的值
   2. :=，直接赋值
   	ISA := riscv64		# 直接赋值，在当前位置就是它
   3. =，间接赋值
       A	= a
       ISA = $(A)			# 结果是 b，并不是 a
       A	= b
       间接赋值是先扫描一遍Makefile，然后得到一个最终的结果。
   4. +=，增量赋值
   	A += a
   	A += b				# 结果是 A = a b，会自动添加空格
   ```

8. 包含文件

   ```
   -include $(AM_HOME)
   ```

9. 执行shell命令

   ```
   $(shell cmd args)
   ```

   * 获得当前路径

     ```
     WORK_DIR	= $(shell pwd)
     ```

   * 创建目录

     ```
     $(shell mkdir -p $(DST_DIR))
     ```

   * 将命令输出写入文件，可以是空文件

     ```
     参考：am-kernels/tests/cpu-tests/Makefile
     RESULT = .result
     $(shell > $(RESULT))			# 在当前目录生成一个 .result 的空文件
     原理：执行shell命令，命令是空的，>是输出重定向，把空字符串写入文件。
     $(shell echo "123" > 1.txt)		# 将"123"写入1.txt
     ```

   * 连续命令之间的管道操作

     ```
     $ echo "abc" | cat		# 输出 abc
     说明： | 是管道操作，将第一个命令的输出作为第二个命令的输入
     $ echo "abc" | vim _	# 送入 vim 编辑器
     ```

   * 字符转换，比如大小写，下划线等

     ```
     echo riscv-nemu | tr a-z A-Z | tr - _
     输出： RISCV_NEMU
     原理：| 是管道连接操作，tr 是字符替换，没有深究。
     ```

10. 执行內建的函数

   * 字符替换、获取第几个单词（以空格分隔）

     ```
     ARCH := riscv64-nemu
     ARCH_SPLIT	= $(subst -, ,$(ARCH))		# riscv64 nemu
     ISA			= $(word 1,$(ARCH_SPLIT))	# riscv64
     PLATFORM	= $(word 2,$(ARCH_SPLIT))	# nemu
     ```

   * 直接输出信息

     ```
     makefile中除了变量定义、规则，还可以直接写一些调试信息
     $(info "abc")
     这条语句不是一个规则，当makefile展开到这里时，直接打印该信息。
     ```

   * 出错并终止编译

     ```
     $(error ErrorMsg)		# 给出错误信息，并终止编译
     ```

   * 获得相对路径

     ```
     $(abspath $(IMAGE_REL))
     ```

   * 排序多个字符串

     ```
     $(sort c b a)		# a b c
     ```

   * addprefix

   * join

11. 嵌套执行make

    ```
    $(LIBS) : %:
    	$(MAKE) -s -C $(AM_HOME)/$* archive
    解释：
    $(MAKE) 表示开始一个新的make
    -s		静默执行
    -C 		改变工作目录
    %:
    $*
    ```

12. GCC编译选项

    ```
    常用写法：
    	CC = 
    	CFLAGS += xxx xxx
    	$(DST_DIR)/%.o : %.c
    		$(CC) $(CFLAGS) -c -o $@ $(realpath $<)
    CFLAGS的常用写法
        -Wall			最高警告等级
        -Werror			警告转变为错误
    	-D__ISA__=\"$(ISA)\"		增加宏定义__ISA__=riscv64，假定$(ISA)是riscv64
    	-D__ISA_$(shell echo $(ISA) | tr a-z A-Z)__		增加宏定义 __ISA_RISCV64__
    	-DISA_H=\"$(ISA).h\"		增加宏定义ISA_H=riscv64.h
    	-fno-asynchronous-unwind-tables		?
    	-fno-builtin				?
    	-fno-stack-protector		?
    	-Wno-main					?
    	-MMD						?
    ```

13. ar打包目标文件为库

    ```
    ar rcs mylib.a a.o b.o c.o
    ```

14. ld选项

    ```
    ld -melf64lriscv -T nemu.ld \
    	--defsym=_perm_start=0x80000000 \
    	--defsym=_entry_offset=0x0 \
    	-e _start -o my.elf	
    ```

15. 反汇编 objdump

    * 将elf文件反汇编，自动识别格式

      ```
      objdump -d my.elf > my.txt
      -d	反汇编exeecutable sections
      -D	反汇编all sections
      ```

    * 将bin文件反汇编，手动指定格式

      ```
      objdump -D add-riscv64-mycpu.bin -b binary -m riscv:rv64
      ```

16. 目标文件拷贝 objcopy

    ```
    objcopy -S --set-section-flags .bss=alloc,contents -O binary my.elf my.bin
    ```

17. 