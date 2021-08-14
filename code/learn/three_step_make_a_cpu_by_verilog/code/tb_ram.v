/*
    https://blog.csdn.net/Stynis/article/details/80555825
    根据设计的ram，需要激励大致要遵循以下几个原则：
    （1）高电平复位清空数据
    （2）先给地址和数据，再给读写信号
    （3）同样采用三态门结构对应与ram相连的inout线（inout端口不能单独存在）
    （4）采用task简化激励组合
*/
`timescale 1ns/1ns

`include "ram.v"

module tb_ram (
    output reg          clk_o,
    output reg          rst_o,
    output reg          wr_en_o,
    output reg          rd_en_o,
    output reg [7:0]    addr_o,
    inout      [31:0]   data_io
  );
    reg[31:0] WriteRAM;  // 由于三态门，不能直接输出至data_io，使用WriteRAM实现缓存

    always begin
      #5 clk_o = ~clk_o;    //提供100MHz时钟
    end
    
    // 0 < addr <255, 0 < WriteRAM <2^32 - 1
    task write(
        input[7:0]       x_i,
        input[31:0]      y_i
        );
    begin
        #100;                  //拉开每次读写之间的间隔，简化initial内容
        @(posedge clk_o);      //时钟控制
        addr_o = x_i;
        WriteRAM = y_i;
        #1                    //先给出地址和数据，再使能
        wr_en_o = 1'b1;
        @(posedge clk_o);
        #50                   //拉长有效时间便于波形显示
        wr_en_o = 1'b0;
    end
    endtask

    task read(             //读操作只需给出地址参数
        input[7:0]       x_i
        );
    begin
        #100;
        @(posedge clk_o);
        addr_o = x_i;
        #1
        rd_en_o = 1'b1;
        @(posedge clk_o);
        #50
        rd_en_o =  1'b0;
    end
    endtask 

    initial begin
        $monitor($time,,, "Data = %d", data_io);  //监视data_io数据线
        WriteRAM= 0;
        clk_o   = 0;
        wr_en_o = 0;
        rd_en_o = 0;
        addr_o  = 0;
        rst_o   = 1;

        #20 rst_o = 0;      // 复位完成

        //为方便查看，使写入的数据为地址的5倍
        write(50,250);
        write(100,500);  //地址100，写入500,下同
        write(200,1000); 
        write (250,1250);
        
        //读取数据
        read(50);
        read(100);
        read(200);
        read(250);

        $finish;
    end

    assign data_io = wr_en_o ? WriteRAM : 32'bz;


endmodule
