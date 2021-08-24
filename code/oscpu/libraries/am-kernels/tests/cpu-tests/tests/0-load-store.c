/*
	这是用于早期 load/store 指令的调试

*/

#include "trap.h"

// unsigned short mem[] = {
// 	0x0, 0x0258, 0x4abc, 0x7fff, 0x8000, 0x8100, 0xabcd, 0xffff
// };

// unsigned lh_ans[] = {
// 	0x00000000, 0x00000258, 0x00004abc, 0x00007fff, 0xffff8000, 0xffff8100, 0xffffabcd, 0xffffffff
// };

// unsigned lhu_ans[] = {
// 	0x00000000, 0x00000258, 0x00004abc, 0x00007fff, 0x00008000, 0x00008100, 0x0000abcd, 0x0000ffff
// };

// unsigned  sh_ans[] = {
// 	0x0000fffd, 0x0000fff7, 0x0000ffdf, 0x0000ff7f, 0x0000fdff, 0x0000f7ff, 0x0000dfff, 0x00007fff
// };

// unsigned  lwlr_ans[] = {
// 	0xbc025800, 0x7fff4a, 0xcd810080, 0xffffab
// };

unsigned mem[] = { 
	0x01234567, 0x89ABCDEF, 
	0x00112233, 0x44556677, 
	0x8899AABB, 0xCCDDEEFF
};

int main() {

	check(mem[0] == 0x01234567);
	check(mem[1] == 0x89ABCDEF);

	return 0;
}
