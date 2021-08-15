/*
	寄存器组

	逻辑比较简单：
	1. 有两个读取通道（一般常用来表示：源操作数1，源操作数2），一个写入通道（用来处理目的操作数）
	2. 读取是组合逻辑，只要使能便有数据
	3. 写入是时序逻辑，在时钟上升沿根据写入使能信号写入数据
*/

`include "defines.v"

module regs(
    input   wire                        rst,
    input   wire                        clk,

    // 写入
    input   wire    [`REG_ADDR_BUS]     widx_i,         // 写寄存器索引
    input   wire    [`REG_BUS]          wdata_i,        // 写寄存器数据
    input   wire 		                we_i,           // 写寄存器标志
    // 读取1
    input   wire    [`REG_ADDR_BUS]     ridx1_i,        // 读寄存器1索引
    output  reg     [`REG_BUS]          rdata1_o,       // 读寄存器2数据
    // 读取2
    input   wire    [`REG_ADDR_BUS]     ridx2_i,        // 读寄存器2索引
    output  reg     [`REG_BUS]          rdata2_o,       // 读寄存器2数据
);
    
    reg     [`REG_BUS]  regs    [`REG_NUM - 1 : 0];
    
	// 写寄存器
    always @(posedge clk) begin
        if (rst == 1'b1) begin
            regs[0]  <= `REG_ZERO;
            regs[1]  <= `REG_ZERO;
            regs[2]  <= `REG_ZERO;
            regs[3]  <= `REG_ZERO;
            regs[4]  <= `REG_ZERO;
            regs[5]  <= `REG_ZERO;
            regs[6]  <= `REG_ZERO;
            regs[7]  <= `REG_ZERO;
            regs[8]  <= `REG_ZERO;
            regs[9]  <= `REG_ZERO;
            regs[10] <= `REG_ZERO;
            regs[11] <= `REG_ZERO;
            regs[12] <= `REG_ZERO;
            regs[13] <= `REG_ZERO;
            regs[14] <= `REG_ZERO;
            regs[15] <= `REG_ZERO;
            regs[16] <= `REG_ZERO;
            regs[17] <= `REG_ZERO;
            regs[18] <= `REG_ZERO;
            regs[19] <= `REG_ZERO;
            regs[20] <= `REG_ZERO;
            regs[21] <= `REG_ZERO;
            regs[22] <= `REG_ZERO;
            regs[23] <= `REG_ZERO;
            regs[24] <= `REG_ZERO;
            regs[25] <= `REG_ZERO;
            regs[26] <= `REG_ZERO;
            regs[27] <= `REG_ZERO;
            regs[28] <= `REG_ZERO;
            regs[29] <= `REG_ZERO;
            regs[30] <= `REG_ZERO;
            regs[31] <= `REG_ZERO;
        end
        else begin
			if ((we_i == 1'b1) && (waddr_i != 5'h0)) begin
                regs[waddr_i] <= wdata_i;
            end
        end
    end
    
	// 读寄存器1
    always @(*) begin
        rdata1_o = regs[ridx1_i];
    end
    
	// 读寄存器2
    always @(*) begin
        rdata2_o = regs[ridx2_i];
    end
    
endmodule
