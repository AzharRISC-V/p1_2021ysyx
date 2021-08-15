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
            regs[0]  <= `DWORD_ZERO;
            regs[1]  <= `DWORD_ZERO;
            regs[2]  <= `DWORD_ZERO;
            regs[3]  <= `DWORD_ZERO;
            regs[4]  <= `DWORD_ZERO;
            regs[5]  <= `DWORD_ZERO;
            regs[6]  <= `DWORD_ZERO;
            regs[7]  <= `DWORD_ZERO;
            regs[8]  <= `DWORD_ZERO;
            regs[9]  <= `DWORD_ZERO;
            regs[10] <= `DWORD_ZERO;
            regs[11] <= `DWORD_ZERO;
            regs[12] <= `DWORD_ZERO;
            regs[13] <= `DWORD_ZERO;
            regs[14] <= `DWORD_ZERO;
            regs[15] <= `DWORD_ZERO;
            regs[16] <= `DWORD_ZERO;
            regs[17] <= `DWORD_ZERO;
            regs[18] <= `DWORD_ZERO;
            regs[19] <= `DWORD_ZERO;
            regs[20] <= `DWORD_ZERO;
            regs[21] <= `DWORD_ZERO;
            regs[22] <= `DWORD_ZERO;
            regs[23] <= `DWORD_ZERO;
            regs[24] <= `DWORD_ZERO;
            regs[25] <= `DWORD_ZERO;
            regs[26] <= `DWORD_ZERO;
            regs[27] <= `DWORD_ZERO;
            regs[28] <= `DWORD_ZERO;
            regs[29] <= `DWORD_ZERO;
            regs[30] <= `DWORD_ZERO;
            regs[31] <= `DWORD_ZERO;
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
            r_data1 = `DWORD_ZERO;
        else if (r_ena1 == 1'b1)
            r_data1 = regs[r_addr1];
        else
            r_data1 = `DWORD_ZERO;
    end
    
	// 寄存器读取通道2
    always @(*) begin
        if (rst == 1'b1)
            r_data2 = `DWORD_ZERO;
        else if (r_ena2 == 1'b1)
            r_data2 = regs[r_addr2];
        else
            r_data2 = `DWORD_ZERO;
    end
    
endmodule
