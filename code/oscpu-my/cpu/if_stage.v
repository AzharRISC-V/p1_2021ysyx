
/* verilator lint_off UNUSED */
//--xuezhen--

`include "defines.v"

module if_stage(clk,
                rst,
                inst_addr,
                inst_ena);
    input wire clk;
    input wire rst;
    // 输出的取值地址、使能信号
    output wire [63 : 0]inst_addr;
    output wire inst_ena;
    
    // 程序计数器
    reg [`REG_BUS]pc;
    
    // fetch an instruction
    always@(posedge clk)
    begin
        if (rst == 1'b1)
        begin
            pc <= `ZERO_DWORD ;
        end
        else
        begin
            pc <= pc + 4;
        end
    end
    
    assign inst_addr = pc;
    assign inst_ena  = (rst == 1'b1) ? 0 : 1;
    
    
endmodule
