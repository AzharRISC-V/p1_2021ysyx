/*
    内存模块

    功能：
    1. 支持读、写
*/

`include "defines.v"

module ram(
    input   wire                        clk,
    input   wire                        rst,

    input   wire    [`RAM_ADDR_BUS]     raddr_i,        // 要读取的地址
    output  reg     [`RAM_DATA_BUS]     rdata_o,        // 读取到的数据

    input   wire    [`RAM_ADDR_BUS]     waddr_i,        // 要写入的地址
    input   wire    [`RAM_DATA_BUS]     wdata_i,        // 要写入的数据
    input   wire                        we_i            // 写入请求
);
    
    reg [`RAM_DATA_BUS] mem [`RAM_SIZE_BUS];
    
    // 写入
    always @(posedge clk or posedge rst)
    begin
        if (!rst && we_i) begin
            mem[waddr_i] <= wdata_i;
        end
    end
    
    // 读取
    assign rdata_o = (!rst) ? mem[raddr_i] : `RAM_DATA_ZERO;
    
endmodule
    
