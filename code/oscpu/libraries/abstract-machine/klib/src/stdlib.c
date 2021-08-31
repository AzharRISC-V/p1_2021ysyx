#include <am.h>
#include <klib.h>
#include <klib-macros.h>

#if !defined(__ISA_NATIVE__) || defined(__NATIVE_USE_KLIB__)
static unsigned long int next = 1;

int rand(void) {
  // RAND_MAX assumed to be 32767
  next = next * 1103515245 + 12345;
  return (unsigned int)(next/65536) % 32768;
}

void srand(unsigned int seed) {
  next = seed;
}

int abs(int x) {
  return (x < 0 ? -x : x);
}

// 太简单了
// 输入 "3 4 5"，得到 345，这个合理吗？
int atoi(const char* nptr) {
  int x = 0;
  while (*nptr == ' ') { nptr ++; }
  while (*nptr >= '0' && *nptr <= '9') {
    x = x * 10 + *nptr - '0';
    nptr ++;
  }
  return x;
}

/*
  功能：  int转换为零结尾的字符串
  参数：
    int     value   要转换的32位整数
    char *  str     要写入的字符串缓冲区
  返回值：
    无
  备注：  至多需要12个字节来产生32位整数的字符串形式
*/
void itoa(int value, char * str) {
  // 32位整数，最大值是 2147483647，共10位，再加一个负号，一个零结束标志
  char buf[12];
  int n = 0;    // buf的写入位置
  int n1 = 0;   // str的写入位置
  bool neg = (value < 0); // 是否为负数
  
  // 负数处理
  if (neg) {
    value = -value;
  }
  
  // 倒序存入
  while (true) {
    buf[n++] = (value % 10) + '0';
    value = value / 10;
    if (!value) {
      break;
    }
  }
  if (neg) {
    buf[n++] = '-';
  }
  // 正序输出
  for (; n > 0; n--) {
    str[n1++] = buf[n - 1];
  }
  str[n1] = 0;
}


/*
  功能：  int转换为零结尾的无符号的Hex字符串
  参数：
    int     value   要转换的32位整数
    char *  str     要写入的字符串缓冲区
  返回值：
    无
  备注：  至多需要9个字节来产生32位整数的字符串形式
*/
void itox(int value, char * str) {
  // 32位整数，最大值是 FFFFFFFF，共8位，再加一个零结束标志
  char buf[9];
  int n = 0;    // buf的写入位置
  int n1 = 0;   // str的写入位置
  uint32_t uval = (uint32_t)value;
  
  // 倒序存入
  int rem = 0;
  char c = 0;
  while (true) {
    rem = uval % 16;
    if (rem > 9) c = (rem - 10) + 'A';
    else c = rem + '0';
    buf[n++] = c;
    uval = uval / 16;
    if (!uval) {
      break;
    }
  }
  // 正序输出
  for (; n > 0; n--) {
    str[n1++] = buf[n - 1];
  }
  str[n1] = 0;
}

// 一个内存块
typedef struct {
  char *  pstart;
  size_t  size;
} memBlk;

// static char * s_pfree = 0;    // 指向空闲区域

void *malloc(size_t size) {
  size = (size + 0xf) & ~0xf;   // aligned to 16 Byte
  if (heap.end - heap.start >= size) {
    //printf("malloc %x bytes at %x\n", size, heap.start);

    char * pstart = heap.start;
    heap.start += size;
    return pstart;
  } else {
    panic_on(0, "Run out of memory!");
    return NULL;
  }

  //panic("Not implemented");
}

void free(void *ptr) {

}

#endif
