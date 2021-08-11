## Logic Circuit 程序改进

1. 选择焊接点时，点的范围太小，很难选中，要么就是拖动图形。应该让Point的矩形更大一些。

   ```
   在 EditorDiagram.cs 的 ClickArea 函数中，以及 DiagramMouseDown() 函数中。
   一个常量 ：EditorDiagram.ClickProximity. 是 Symbol.PinRadius 的两倍。这两个值控制了矩形判断条件。
   ```

   

2. 