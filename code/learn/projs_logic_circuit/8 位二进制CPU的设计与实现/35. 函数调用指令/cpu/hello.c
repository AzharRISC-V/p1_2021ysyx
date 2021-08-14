
/* C语言的调用方式：
C语言规定：由调用方维护堆栈。
调用：
 PUSH PC
 PUSH number1
 PUSH number2
 PUSH return
返回：
 POP ..
*/
int add(int number1, int number2)
{
    return number1 + number2;
}

