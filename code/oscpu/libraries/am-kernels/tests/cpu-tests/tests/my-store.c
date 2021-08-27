// 准备手写一些汇编指令，测试特定的CPU指令，但是还不能这样做，因为基础指令还未完成。

int main() {
  asm volatile("auipc   addi s1, 0x12345678; sd s1, 0(s2);");

  //asm volatile("mv a0, %0; .word 0x0000006b" : : "r"(code));
  return 0;
}