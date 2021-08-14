/*
    https://blog.csdn.net/Stynis/article/details/80555825
    使用双向口的话需要利用三态门进行输入输出的控制。使用条件操作符实现三态门的构造。
    在时钟上升沿，
        若写信号有效，则将当前地址线对应存储器的空间存入当前data_io上的数据；
        若读信号有效，则将地址线对应存储器空间的数据输出至data_io，
        读写无效时为高阻态。
*/

//ram.v
module ram(
    input                   clk_i,
    input                   rst_i,
    input                   wr_en_i,
    input                   rd_en_i,
    input [7:0]             addr_i,
    inout [31:0]            data_io
);

    reg [31:0]       bram[255:0];    
    integer          i;   
    reg [31:0]       data;  // 临时寄存器

    always @(posedge clk_i or posedge rst_i)
    begin
       if (rst_i)   
         begin
           for(i=0;i<=255;i=i+1) //reset, 按字操作
           bram[i] <= 32'b0;
         end
       else if (wr_en_i) begin
            bram[addr_i] <= data_io;
       end
       else if (rd_en_i) begin
            data <= bram[addr_i];
       end
       else begin
            data <= 32'bz;      //读写均无效时，为高阻态。若不加此句，时序会出现问题
       end
    end

    // 读信号有效时送出数据，否则高阻（相当于这里不处理，不影响输入的信号）
    assign data_io = rd_en_i? data : 32'bz; //三态门实现
endmodule
