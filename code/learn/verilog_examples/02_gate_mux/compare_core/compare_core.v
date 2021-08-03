// 比较器模块
// 相等输出1，否则输出0
module compare_core (result,a,b);
input [7:0] a,b;
output result;

assign result = (a == b) ? 1 : 0;

endmodule

// 数据比较器
// a > b, (y1,y2,y3) = (1,0,0)
// a = b, (y1,y2,y3) = (0,1,0)
// a < b, (y1,y2,y3) = (0,0,1)
module comparator_4 (y1,y2,y3,a,b);
input [3:0] a,b;
output y1,y2,y3;
reg y1,y2,y3;

always @(a,b) begin
    if (a > b) begin
        y1 = 1; y2 = 0; y3 = 0;
    end
    else if (a == b) begin
        y1 = 0; y2 = 1; y3 = 0;
    end
    else begin
        y1 = 0; y2 = 0; y3 = 1;
    end
end

endmodule

// 任务实现比较器
// x > y, tmp = x
// x <=y, tmp = y
// 选出 x 和 y 中较大的，存入 tmp
task task_demo;
    input [7:0] x,y;
    output [7:0] tmp;

    if (x > y)
        tmp = x;
    else
        tmp = y;
endtask

