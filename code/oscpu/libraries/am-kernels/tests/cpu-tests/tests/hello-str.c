#include "trap.h"

char buf[128];

//不设置noinline属性的话，会被gcc内联到每个调用语句处的，空间换时间的优化
void mydl(uint64_t tm) __attribute__ ((noinline));    
void mydl(uint64_t tm) {
  for(uint64_t i = tm; i != 0;) {
    asm volatile("");    //这句是根据avrgcc改的
    i--;
  }
}

int main() {

  printf("===TEST Started!\n");

	sprintf(buf, "%s", "Hello world!\n");
	check(strcmp(buf, "Hello world!\n") == 0);

	sprintf(buf, "%d + %d = %d\n", 1, 1, 2);
	check(strcmp(buf, "1 + 1 = 2\n") == 0);

	sprintf(buf, "%d + %d = %d\n", 2, 10, 12);
	check(strcmp(buf, "2 + 10 = 12\n") == 0);


  for (int i = 0; i < 100; i++) {
    //printf("%d\n", i);
    putch('a' + (i%10));
    mydl(1000);
    if ((i + 1) % 10 == 0) {
      putch('\n');
    }
  }
  putch('\n');
  putch('b');
  putch('c');

  printf("===TEST Finished!\n");

	return 0;
}
