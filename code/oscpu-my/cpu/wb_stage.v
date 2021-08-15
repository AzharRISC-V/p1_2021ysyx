// Zhengpu Shi

`include "defines.v"

module wb_stage(clk,
                rst,
                rd_w_ena_i,
                rd_w_addr_i,
                rd_data_i,
                rd_w_ena_o,
                rd_w_addr_o,
                rd_data_o);
    input wire clk;
    input wire rst;

    input wire rd_w_ena_i;
    input wire [4 : 0]rd_w_addr_i;
    input reg [`REG_BUS ]rd_data_i;

    output reg rd_w_ena_o;
    output reg [4 : 0]rd_w_addr_o;
    output reg [`REG_BUS ]rd_data_o;

    always@(posedge clk)
    begin
        if (rst == 1'b1)
        begin
            rd_w_ena_o <= 0;
            rd_w_addr_o <= 0;
            rd_data_o <= 0;
        end
        else
        begin
            rd_w_ena_o <= rd_w_ena_i;
            rd_w_addr_o <= rd_w_addr_i;
            rd_data_o <= rd_data_i;
        end
    end
    
endmodule
