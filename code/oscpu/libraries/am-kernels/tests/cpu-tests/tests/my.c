/*
  利用 asm 内联汇编编写一些简单的汇编指令，手动从bin中提取

*/

int main() {

  asm volatile("addi a0,zero,1");   // "li a0,1"
  asm volatile("addi a0,zero,2");
  asm volatile("addi a0,zero,3");
  asm volatile("addi a0,zero,4");
  asm volatile("addi a0,zero,5");
  asm volatile("addi a0,zero,6");
  asm volatile("addi a0,zero,7");

  return 0;
}
