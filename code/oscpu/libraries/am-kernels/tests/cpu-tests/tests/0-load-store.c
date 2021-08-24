/*
	这是用于早期 load/store 指令的调试

*/

#include "trap.h"

unsigned mem[] = { 
	0x01234567, 0x89ABCDEF, 
	0x00112233, 0x44556677, 
	0x8899AABB, 0xCCDDEEFF
};

int main() {
  unsigned long long *  pu64;
  unsigned long long    u64;

  // unsigned long *       pu32;
  // unsigned long         u32;
  
  // unsigned short        u16;
  // unsigned short *      pu16;
  
  // unsigned char         u8;
  // unsigned char *       pu8;

  // 对齐访问
  pu64 = (unsigned long long *)mem;
  u64 = *pu64;
  u64 = *(pu64 + 1);
  u64 = *(pu64 + 2);
  u64 = u64 + 1;
  (void)u64;

  // pu32 = (unsigned long *)mem;
  // u32 = *pu32;
  // u32 = *(pu32 + 1);
  // u32 = *(pu32 + 2);
  // u32 = *(pu32 + 3);
  // u32 = *(pu32 + 4);
  // u32 = u32 + 1;
  // (void)u32;


  // 非对齐访问

	return 0;
}
