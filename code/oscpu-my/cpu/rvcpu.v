
/* verilator lint_off UNUSED */
//--xuezhen--

`timescale 1ns / 1ps

`include "defines.v"


module rvcpu(clk,
             rst,
             inst,
             inst_addr,
             inst_ena);
    
    input wire clk;
    input wire rst;
    /* ----- 模拟ROM ----- */
    // 输入的指令
    input wire [31 : 0] inst;
    
    /* ----- 调试? ----- */
    // 输出指令地址
    output wire [63 : 0] inst_addr;
    // 输出指令有效
    output wire inst_ena;
    
    /* ----- 内部信号 ----- */
    // 源操作数1
    wire rs1_r_ena;
    wire [4 : 0]rs1_r_addr;
    wire [`REG_BUS] r_data1;
    
    // 源操作数2
    wire rs2_r_ena;
    wire [4 : 0]rs2_r_addr;
    wire [`REG_BUS] r_data2;
    
    // 目的操作数
    wire rd_w_ena;
    wire [4 : 0]rd_w_addr;
    wire [`REG_BUS]rd_data;
    
    // 目的操作数（wb_stage）
    wire rd_w_ena0;
    wire [4 : 0]rd_w_addr0;
    wire [`REG_BUS]rd_data0;
    
    // 指令类型（自定义）（用于CU）
    wire [4 : 0]inst_type;
    // 指令操作（自定义）（用于ALU）
    wire [7 : 0]inst_opcode;
    
    // 操作数1，操作数2
    wire [`REG_BUS]op1;
    wire [`REG_BUS]op2;
    
    // exe_stage -> other stage
    wire [4 : 0]inst_type_o;
    // exe_stage -> regfile
    
    /* ----- 业务逻辑 ----- */
    
    if_stage If_stage(
    .clk(clk),
    .rst(rst),
    
    .inst_addr(inst_addr),
    .inst_ena(inst_ena)
    );
    
    id_stage Id_stage(
    .rst(rst),
    .inst(inst),
    .rs1_data(r_data1),
    .rs2_data(r_data2),
    
    .rs1_r_ena(rs1_r_ena),
    .rs1_r_addr(rs1_r_addr),
    .rs2_r_ena(rs2_r_ena),
    .rs2_r_addr(rs2_r_addr),
    .rd_w_ena(rd_w_ena),
    .rd_w_addr(rd_w_addr),
    .inst_type(inst_type),
    .inst_opcode(inst_opcode),
    .op1(op1),
    .op2(op2)
    );
    
    exe_stage Exe_stage(
    .rst(rst),
    .inst_type_i(inst_type),
    .inst_opcode(inst_opcode),
    .op1(op1),
    .op2(op2),
    
    .inst_type_o(inst_type_o),
    .rd_data(rd_data)
    );
    
    wb_stage Wb_stage(
    .clk(clk),
    .rst(rst),
    .rd_w_ena_i(rd_w_ena),
    .rd_w_addr_i(rd_w_addr),
    .rd_data_i(rd_data),
    .rd_w_ena_o(rd_w_ena0),
    .rd_w_addr_o(rd_w_addr0),
    .rd_data_o(rd_data0)
    );
    
    regfile Regfile(
    .clk(clk),
    .rst(rst),
    .w_addr(rd_w_addr0),
    .w_data(rd_data0),
    .w_ena(rd_w_ena0),
    
    .r_addr1(rs1_r_addr),
    .r_data1(r_data1),
    .r_ena1(rs1_r_ena),
    .r_addr2(rs2_r_addr),
    .r_data2(r_data2),
    .r_ena2(rs2_r_ena)
    );
    
endmodule
    
    
