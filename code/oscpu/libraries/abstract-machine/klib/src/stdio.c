#include <am.h>
#include <klib.h>
#include <klib-macros.h>
#include <stdarg.h>

#if !defined(__ISA_NATIVE__) || defined(__NATIVE_USE_KLIB__)

int printf(const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);

  char buf[200];
  int cnt = vsnprintf(buf, sizeof(buf), fmt, ap);

  putstr(buf);

  return cnt;
}

int sprintf(char *out, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int cnt = vsprintf(out, fmt, ap);
  va_end(ap);

  return cnt;
}

int vsprintf(char *out, const char *fmt, va_list ap) {
  return vsnprintf(out, 0xFFFF, fmt, ap);
}


int snprintf(char *out, size_t n, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int cnt = vsnprintf(out, n, fmt, ap);
  va_end(ap);

  return cnt;
}

/*
  支持的格式:
  %s %d
  返回值：返回产生的字符数量，并且out是以C风格的字符串（以0结尾）
*/
int vsnprintf(char *out, size_t n, const char *fmt, va_list ap) {
  char c, c1;     // 格式符中的当前字符，下一个字符
  char *p = out;  // 跟踪位置
  int cnt = 0;      // 统计写入的字节数
  int n_freebytes;    // 空闲字节数，保留1字节的结束符0
  int copy_len = 0;   // 临时计算拷贝长度
  char buf4val[12];   // 保存一个整数的临时变量

  // 若只有1个字节的存储空间，则及早退出
  if (n == 1) {
    out[0] = 0;
    return 0;
  }

  // 初始的空闲字节数
  n_freebytes = n - cnt - 1;

  // 解析格式字符串
  c = *fmt;
  c1 = *(fmt+1);
  while (c) {
    // 如果是控制符
    if (c == '%') {
      // 字符串
      if (c1 == 's') {
        char *s = va_arg(ap, char *);
        copy_len = strlen(s);
        copy_len = copy_len < n_freebytes ? copy_len : n_freebytes;
        strncpy(p, s, copy_len);
        p += (copy_len);
        cnt += copy_len;
        n_freebytes -= copy_len;
      }
      // 十进制整数（支持负数）
      else if (c1 == 'd') {
        int value = va_arg(ap, int);
        itoa(value, buf4val);
        copy_len = strlen(buf4val);
        copy_len = copy_len < n_freebytes ? copy_len : n_freebytes;
        strncpy(p, buf4val, copy_len);
        cnt += strlen(p);
        p += strlen(p);
        n_freebytes -= copy_len;
      }
      // 十六进制整数
      else if (c1 == 'x') {
        int value = va_arg(ap, int);
        itox(value, buf4val);
        copy_len = strlen(buf4val);
        copy_len = copy_len < n_freebytes ? copy_len : n_freebytes;
        strncpy(p, buf4val, copy_len);
        cnt += strlen(p);
        p += strlen(p);
        n_freebytes -= copy_len;
      }
      // 字符
      else if (c1 == 'c') {
        copy_len = 1;
        *p = (char)(va_arg(ap, int));
        cnt += copy_len;
        p += copy_len;
        n_freebytes -= copy_len;
      }
      // not support
      else {
        break;
      }
      fmt += 2;
    } 
    // 非控制符
    else {
      if (n_freebytes > 0) {
        *p = c;
        p++;
        cnt++;
        fmt++;
        n_freebytes--;
      } else {
        break;
      }
    }
    c = *fmt;
    c1 = *(fmt+1);

    // 判断是否还有空间
    if (n_freebytes == 0) {
      break;
    }
  }

  out[cnt] = 0; // 以0结尾

  return cnt;
}

#endif
