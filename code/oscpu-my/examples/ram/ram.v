/*
 https://blog.csdn.net/Stynis/article/details/80555825
 使用双向口的话需要利用三态门进行输入输出的控制。使用条件操作符实现三态门的构造。
 在时钟上升沿，
 若只有写信号有效，则将当前地址线对应存储器的空间存入当前data上的数据；
 若只有读信号有效，则将地址线对应存储器空间的数据输出至data，
 读写均无效、读写均有效时为高阻态。
 */

`include "defines.v"


//ram.v
module ram(clk,
           rst,
           addr,
           wr_en,
           rd_en,
           data);
    input                   clk;
    input                   rst;
    input                   wr_en;
    input                   rd_en;
    input [`RAM_ADDR_BUS]   addr;
    inout [`RAM_DATA_BUS]   data;
    
    reg [`RAM_DATA_BUS] mem[`RAM_SIZE_BUS];
    reg [`RAM_DATA_BUS] data0;  // 由于三态门，不能直接输出至data，使用data0实现缓存
    //integer          i;
    
    // 读信号有效时送出数据，否则高阻（相当于这里不处理，不影响输入的信号）
    assign data = rd_en? data0 : `RAM_DATA_HZ;
    
    always @(posedge clk or posedge rst)
    begin
        // if (rst)
        // begin
        //     // 内存清零
        //     for(i = 0;i<= `RAM_SIZE;i = i+1)
        //         mem[i] = `RAM_DATA_ZERO;
        // end
        // else 
        if (wr_en) begin
            mem[addr] <= data;
        end
        else if (rd_en) begin
            data0 = mem[addr];
        end
        else begin
            data0 = `RAM_DATA_HZ;      // 其余情况，为高阻态。
        end
    end
    
endmodule
    
