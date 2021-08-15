/*
    ROM模块

    功能：
    1. 支持读
    2. 支持调试模式，允许对ROM进行初始化，设置初始化完成标志
*/

`include "defines.v"

module rom(
    input   wire                        clk,
    input   wire                        rst,

    input   wire    [`ROM_ADDR_BUS]     raddr_i,        // 要读取的地址
    output  reg     [`ROM_DATA_BUS]     rdata_o,        // 读取到的数据

    // (调试用，开机先写入ROM，并设置初始化完毕标志)
    input   wire    [`ROM_ADDR_BUS]     waddr_i,        // 要写入的地址
    input   reg     [`ROM_DATA_BUS]     wdata_i         // 读写入的数据
    input   wire                        inited_i,       // ROM是否已初始化完毕（外部设置）
    output  wire                        inited_o,       // ROM是否已初始化完毕（内部反馈）
);
    
    reg [`ROM_DATA_BUS] mem [`ROM_SIZE_BUS];
    
    // 读取
    assign rdata_o = (!rst) ? mem[raddr_i] : `ROM_DATA_ZERO;

    // 写入
    always @(posedge clk or posedge rst)
    begin
        if (!rst && we_i) begin
            mem[waddr_i] <= wdata_i;
        end
    end

    // 初始化完毕
    initial begin
        inited_o <= 0;
    end
    always @(posedge clk or posedge rst)
    begin
        if (rst) begin
            inited_o <= 0;
        end
        else begin
            inited_o <= inited_i;
        end
    end
    
endmodule
    
