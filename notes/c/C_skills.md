## C语言知识点补充

1. void * 的补充

   ```
   在 am-kernels/tests/cpu-tests/tests/load-store.c: line35 看到
   ((unsigned *)(void *)mem + 1))[1]
   解释：
   1. void * 是无类型指针，可以指向任意类型的数据，可用任意类型的指针对void指针赋值。
   若将void * p赋值给其他类型的指针，需要强制类型转换，如 a = (int *)p。
   2. 在ANSI C标准中，不允许对void指针进行算数运算，如 p++, p+=1等。因为void无类型，运算是不知道操作数是几个字节。
   3. 在GNU C中则允许，因为默认的，GNU认为void *和char *一样。此时 sizeof(*p)==sizeof(char)
   
   ```

   

2. 