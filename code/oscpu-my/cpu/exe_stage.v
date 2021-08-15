
//--xuezhen--

`include "defines.v"

module exe_stage(rst,
                 inst_type_i,
                 inst_opcode,
                 op1,
                 op2,
                 inst_type_o,
                 rd_data);
    input wire rst;
    input wire [4 : 0]inst_type_i;
    input wire [7 : 0]inst_opcode;
    input wire [`REG_BUS ]op1;
    input wire [`REG_BUS ]op2;
    output wire [4 : 0]inst_type_o;
    output reg [`REG_BUS ]rd_data;
    
    
    regfile Regfile(
    .clk        (clk),
    .rst        (rst),
    .w_addr     (rd_w_addr0),
    .w_data     (rd_data0),
    .w_ena      (rd_w_ena0),
    .r_addr1    (rs1_r_addr),
    .r_data1    (r_data1),
    .r_ena1     (rs1_r_ena),
    .r_addr2    (rs2_r_addr),
    .r_data2    (r_data2),
    .r_ena2     (rs2_r_ena)
    );

    assign inst_type_o = inst_type_i;
    
    always@(*)
    begin
        if (rst == 1'b1)
        begin
            rd_data = `DWORD_ZERO;
        end
        else
        begin
            case(inst_opcode)
            `INST_ADDI: begin rd_data = op1 + op2;  end
            default:    begin rd_data = `DWORD_ZERO; end
            endcase
        end
    end
    
endmodule
