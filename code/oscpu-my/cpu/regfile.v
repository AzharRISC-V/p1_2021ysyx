/*
	寄存器组

	逻辑比较简单：
	1. 有两个读取通道（一般常用来表示：源操作数1，源操作数2），一个写入通道（用来处理目的操作数）
	2. 读取是组合逻辑，只要使能便有数据
	3. 写入是时序逻辑，在时钟上升沿根据写入使能信号写入数据
*/

`include "defines.v"

module regfile(clk,
               rst,
               w_addr,
               w_data,
               w_ena,
               r_addr1,
               r_data1,
               r_ena1,
               r_addr2,
               r_data2,
               r_ena2);
    input wire clk;
    input wire rst;
	// 寄存器写入通道
    input wire [4 : 0] w_addr;
    input wire [`REG_BUS] w_data;
    input wire 		 w_ena;
	// 寄存器读取通道1
    input wire [4 : 0] r_addr1;
    output reg [`REG_BUS] r_data1;
    input wire 		 r_ena1;
	// 寄存器读取通道2
    input wire [4 : 0] r_addr2;
    output reg [`REG_BUS] r_data2;
    input wire 		 r_ena2;
    
    // 32 registers
    reg [`REG_BUS] 	regs[0 : 31];
    
	// 时钟上升沿：复位，写入寄存器
    always @(posedge clk)
    begin
        if (rst == 1'b1)
        begin
            regs[0]  <= `ZERO_WORD;
            regs[1]  <= `ZERO_WORD;
            regs[2]  <= `ZERO_WORD;
            regs[3]  <= `ZERO_WORD;
            regs[4]  <= `ZERO_WORD;
            regs[5]  <= `ZERO_WORD;
            regs[6]  <= `ZERO_WORD;
            regs[7]  <= `ZERO_WORD;
            regs[8]  <= `ZERO_WORD;
            regs[9]  <= `ZERO_WORD;
            regs[10] <= `ZERO_WORD;
            regs[11] <= `ZERO_WORD;
            regs[12] <= `ZERO_WORD;
            regs[13] <= `ZERO_WORD;
            regs[14] <= `ZERO_WORD;
            regs[15] <= `ZERO_WORD;
            regs[16] <= `ZERO_WORD;
            regs[17] <= `ZERO_WORD;
            regs[18] <= `ZERO_WORD;
            regs[19] <= `ZERO_WORD;
            regs[20] <= `ZERO_WORD;
            regs[21] <= `ZERO_WORD;
            regs[22] <= `ZERO_WORD;
            regs[23] <= `ZERO_WORD;
            regs[24] <= `ZERO_WORD;
            regs[25] <= `ZERO_WORD;
            regs[26] <= `ZERO_WORD;
            regs[27] <= `ZERO_WORD;
            regs[28] <= `ZERO_WORD;
            regs[29] <= `ZERO_WORD;
            regs[30] <= `ZERO_WORD;
            regs[31] <= `ZERO_WORD;
        end
        else
        begin
			// 防止写入 r0
            if ((w_ena == 1'b1) && (w_addr != 5'h00)) begin
                regs[w_addr] <= w_data;
            end
        end
    end
    
	// 寄存器读取通道1
    always @(*) begin
        if (rst == 1'b1)
            r_data1 = `ZERO_WORD;
        else if (r_ena1 == 1'b1)
            r_data1 = regs[r_addr1];
        else
            r_data1 = `ZERO_WORD;
    end
    
	// 寄存器读取通道2
    always @(*) begin
        if (rst == 1'b1)
            r_data2 = `ZERO_WORD;
        else if (r_ena2 == 1'b1)
            r_data2 = regs[r_addr2];
        else
            r_data2 = `ZERO_WORD;
    end
    
endmodule
