## Logic Circuit 程序改进

1. 选择焊接点时，点的范围太小，很难选中，要么就是拖动图形。应该让Point的矩形更大一些。

   ```
   在 EditorDiagram.cs 的 ClickArea 函数中，以及 DiagramMouseDown() 函数中。
   一个常量 ：EditorDiagram.ClickProximity. 是 Symbol.PinRadius 的两倍。这两个值控制了矩形判断条件。
   
结论：失败，显示和操作逻辑捆绑在一起，需要区分选择wire、instance等，需要更智能和更复杂的逻辑来控制，不能直接修改参数来达到直接选中jam（焊接点）的目的。
   ```

2. 模拟运行时，最高频率限制为50，想要使频率更高

   ```
   这部分逻辑与Windows的定时精度有关，程序中使用 System.Timer.Interval 参数，该参数最小精度是 1 ms。但由于进程调度时间不固定，实际上做不到 1ms 调度一次。
   目标是修改为 200hz，能否5ms运行一次。
   相关代码：Runner/CircuitRunner.RunCircuit(),PreciseTimer
   实际调试时发现，实际频率最高也就是 30多 （Debug）
   （Release模式）也是如此。应该不是性能问题，而是程序设置，或者是Windows精度问题，继续检查。
   阻塞机制：CircuitRunner.RunCircuit() 中 line218, this.evaluationGate.WaitOne();
   而 evaluationGate 是 AutoResetEvent 类的实例，是一种线程同步器，简称同步信号，
   具有 wait(), set() 等方法。
   其 set() 是在 OnFunctionUpdated() 函数中触发的
   该函数是 this.CircuitState.FunctionUpdated 事件的响应函数。
   
   最终确定，控制模拟周期的时间间隔，是在 PreciseTimer.TimerElapsed()函数中， this.timer.Interval 中设定。当最小值是 1 时，Windows下的响应频率仍然是 30hz 左右。
   一个想法：这里的控制流程太繁琐，首先是 System.Timer的周期性响应，处理函数中会触发 this.Action，该 Action相当于一个匿名函数（或回调函数），该Action指向 this.TimerTick()【在 CircuitRunner类中】，此时会将 this.evaluationGate.Set() 信号释放。
   
   结论：失败，做不到高速模拟。
   
   网上提到的C#高精度定时，一般是开一个线程，然后用while循环，调用Windows API：
   QueryPerformanceCounter()，精度可以达到 1us。
   但是，其控制比较复杂了。也有性能平衡问题。
   ```

   

3. 