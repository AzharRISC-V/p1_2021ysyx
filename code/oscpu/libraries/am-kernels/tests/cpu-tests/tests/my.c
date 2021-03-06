/*
  利用 asm 内联汇编编写一些简单的汇编指令，手动从bin中提取

*/

int main() {

  // asm volatile("j 0");  // 原地跳转，但编译器不支持
  // asm volatile(".word 0x0000006f"); // 原地跳转

  asm volatile("addi a0,zero,1");   // "li a0,1"
  asm volatile("addi a0,zero,2");
  asm volatile("addi a0,zero,3");
  asm volatile("addi a0,zero,4");
  asm volatile("addi a0,zero,5");
  asm volatile("addi a0,zero,6");
  asm volatile("addi a0,zero,7");
  asm volatile("addi zero,zero,0");   // "li a0,0"

  return 0;
}
