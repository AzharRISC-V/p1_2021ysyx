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
           r_addr,
           r_en,
           r_data,
           w_addr,
           w_en,
           w_data);
    input clk,rst,w_en,r_en;
    input [`RAM_ADDR_BUS]   w_addr, r_addr;
    input [`RAM_DATA_BUS]   w_data;
    output [`RAM_DATA_BUS]  r_data;
    
    reg [`RAM_DATA_BUS] mem[`RAM_SIZE_BUS];
    //integer          i;
    
    // 写入
    always @(posedge clk or posedge rst)
    begin
        if (!rst && w_en) begin
            mem[w_addr] <= w_data;
        end
    end
    
    // 读取
    assign r_data = (!rst && r_en) ? mem[r_addr] : `RAM_DATA_HZ;
    
    // always @(posedge clk or posedge rst)
    // begin
    //     if (rst)
    //     begin
    //         // 内存清零
    //         for(i = 0;i< = `RAM_SIZE;i = i+1)
    //             mem[i] = `RAM_DATA_ZERO;
    //     end
    //     else
    // end
    
endmodule
    
