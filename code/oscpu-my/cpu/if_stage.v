/*
    IF: Instruction Fetch
    取值阶段
    
    功能：
    1. 从ROM中获取当前PC对应的指令
*/
`include "defines.v"

module if_stage(
    input   wire                        rst,
    input   wire                        clk,

    input   wire    [`REG_BUS]          pc_i,               // PC

    output  wire    [`INST_BUS]         inst_o,             // 取出的指令
);

    
    reg     [`ROM_ADDR_BUS]     rom_raddr_i,        // 要读取的地址
    reg     [`ROM_DATA_BUS]     rom_rdata_o,        // 读取到的数据
    wire    [`ROM_ADDR_BUS]     waddr_i,            // 要写入的地址
    reg     [`ROM_DATA_BUS]     wdata_i             // 读写入的数据
    wire                        inited_i,           // ROM是否已初始化完毕（外部设置）
    wire                        inited_o,           // ROM是否已初始化完毕（内部反馈）

    rom inst_rom(
        .clk(clk),
        .rst(rst),
        .raddr_i

    input   wire                        clk,
    input   wire                        rst,
    input   wire    [`ROM_ADDR_BUS]     raddr_i,        // 要读取的地址
    output  reg     [`ROM_DATA_BUS]     rdata_o,        // 读取到的数据
    input   wire    [`ROM_ADDR_BUS]     waddr_i,        // 要写入的地址
    input   reg     [`ROM_DATA_BUS]     wdata_i         // 读写入的数据
    input   wire                        inited_i,       // ROM是否已初始化完毕（外部设置）
    output  wire                        inited_o,       // ROM是否已初始化完毕（内部反馈）
    );

    always @(posedge clk) begin
        if (rst) begin
            inst_o <= `DWORD_ZERO;
        end
        else begin
            pc <= pc + 1;
        end
    end
    
    assign inst_addr = pc;
    assign inst_ena  = (rst == 1'b1) ? 0 : 1;
    
endmodule
