#include <klib.h>
#include <klib-macros.h>
#include <stdint.h>

#if !defined(__ISA_NATIVE__) || defined(__NATIVE_USE_KLIB__)

size_t strlen(const char *s) {
  size_t n = 0;
  while (*(s++)) {
    n++;
  }
  return n;
}

char *strcpy(char* dst,const char* src) {
  size_t n = strlen(src);
  memcpy(dst, src, n + 1);  // +1 is \0
  return dst;
}

char* strncpy(char* dst, const char* src, size_t n) {
  memcpy(dst, src, n + 1);  // +1 is \0
  return dst;
}

char* strcat(char* dst, const char* src) {
  size_t n = strlen(dst);
  strcpy(&dst[n], src);
  return dst;
}

int strcmp(const char* s1, const char* s2) {
  size_t n1 = strlen(s1);
  size_t n2 = strlen(s2);
  size_t n = n1 > n2 ? n1 : n2;
  return memcmp(s1, s2, n);
}

int strncmp (const char *s1, const char *s2, size_t n) {
  return memcmp(s1, s2, n);
}

void* memset(void* v,int c,size_t n) {
  char * p = (char *)v;
  for (size_t i = 0; i < n; i++) {
    *p = c;
    p++;
  }
  return v;
}

void* memmove(void* dst,const void* src,size_t n) {
  memcpy(dst, src, n);
  return dst;
}

void* memcpy(void* out, const void* in, size_t n) {
  char * pin = (char *)in;
  char * pout = (char *)out;
  
  if (n == 0) {
    return pout;
  }

  if (pout > pin) {
    pout = pout + (n - 1);
    pin = pin + (n - 1);
    for (size_t i = 0; i < n; i++) {
      *pout = *pin;
      pin--;
      pout--;
    }
  } else {
    for (size_t i = 0; i < n; i++) {
      *pout = *pin;
      pin++;
      pout++;
    }
  }
  return out;
}

int memcmp(const void* s1, const void* s2, size_t n) {
  char * p1 = (char *)s1;
  char * p2 = (char *)s2;

  for (size_t i = 0; i < n; i++) {
    if (*p1 < *p2)
      return -1;
    else if (*p1 > *p2)
      return 1;
    
    p1++;
    p2++;
  }
  return 0;
}

#endif
