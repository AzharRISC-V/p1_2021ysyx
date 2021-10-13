
`timescale 1ns / 1ps

`define ZERO_WORD           64'h00000000_00000000
`define REG_BUS             63 :0
`define DOUBLE_REG_BUS      127:0

// `define PC_START            64'h00000000_80000000 
`define PC_START            32'h3000_0000

// `define RAM_ADDR_WIDTH      64
`define RAM_ADDR_WIDTH      32
`define RAM_DATA_WIDTH      64

`define INST_WIDTH          32
`define DATA_WIDTH          64

// `define AXI_ADDR_WIDTH      64
`define AXI_ADDR_WIDTH      32
`define AXI_DATA_WIDTH      64
`define AXI_ID_WIDTH        4
`define AXI_USER_WIDTH      1

`define SIZE_B              2'b00
`define SIZE_H              2'b01
`define SIZE_W              2'b10
`define SIZE_D              2'b11

`define REQ_READ            1'b0
`define REQ_WRITE           1'b1

`define RISCV_PRIV_MODE_U   0
`define RISCV_PRIV_MODE_S   1
`define RISCV_PRIV_MODE_M   3

`define ALU_SEL_BUS         3:0
`define ALU_SEL_WIDTH       4

`define ALU_SEL_OR          4'b0001
`define ALU_SEL_AND         4'b0010
`define ALU_SEL_XOR         4'b0011
`define ALU_SEL_SLL         4'b0100
`define ALU_SEL_SRL         4'b0101
`define ALU_SEL_SRA         4'b0110
`define ALU_SEL_SLT         4'b0111
`define ALU_SEL_ADD         4'b1000
`define ALU_SEL_SUB         4'b1001

`define TRANSFER_SEL_BUS    2:0
`define TRANSFER_SEL_WIDTH  3

`define TRANSFER_JAL        3'b000
`define TRANSFER_JALR       3'b001
`define TRANSFER_BEQ        3'b010
`define TRANSFER_BNE        3'b011
`define TRANSFER_BLT        3'b100
`define TRANSFER_BGE        3'b101
`define TRANSFER_BLTU       3'b110
`define TRANSFER_BGEU       3'b111

`define MEM_SEL_BUS         3:0
`define MEM_SEL_WIDTH       4

`define MEM_LB              4'b0000
`define MEM_LH              4'b0001
`define MEM_LW              4'b0010
`define MEM_LD              4'b0011
`define MEM_LBU             4'b0100
`define MEM_LHU             4'b0101
`define MEM_LWU             4'b0110
`define MEM_SB              4'b1000
`define MEM_SH              4'b1001
`define MEM_SW              4'b1010
`define MEM_SD              4'b1011

`define CSR_SEL_BUS         1:0
`define CSR_SEL_WIDTH       2

`define CSR_CSRRW           2'b01
`define CSR_CSRRS           2'b10
`define CSR_CSRRC           2'b11

`define RD_SEL_BUS          1:0
`define RD_SEL_WIDTH        2

`define RD_SEL_ALU          2'b00
`define RD_SEL_LINK         2'b01
`define RD_SEL_CSR          2'b10
`define RD_SEL_LOAD         2'b11

`define CSR_MCYCLE          12'hb00
`define CSR_MSTATUS         12'h300
`define CSR_MTVEC           12'h305
`define CSR_MEPC            12'h341
`define CSR_MCAUSE          12'h342
`define CSR_MIE             12'h304
`define CSR_MIP             12'h344
`define CSR_MSCRATCH        12'h340



module ysyx_210413(
    input                               clock,
    input                               reset,

    input                               io_interrupt,

    input                               io_master_awready,
    output                              io_master_awvalid,
    output [31:0]                       io_master_awaddr,
    output [3:0]                        io_master_awid,
    output [7:0]                        io_master_awlen,
    output [2:0]                        io_master_awsize,
    output [1:0]                        io_master_awburst,
    
    input                               io_master_wready,
    output                              io_master_wvalid,
    output [63:0]                       io_master_wdata,
    output [7:0]                        io_master_wstrb,
    output                              io_master_wlast,
    
    output                              io_master_bready,
    input                               io_master_bvalid,
    input  [1:0]                        io_master_bresp,
    input  [3:0]                        io_master_bid,

    input                               io_master_arready,
    output                              io_master_arvalid,
    output [31:0]                       io_master_araddr,
    output [3:0]                        io_master_arid,
    output [7:0]                        io_master_arlen,
    output [2:0]                        io_master_arsize,
    output [1:0]                        io_master_arburst,
    
    output                              io_master_rready,
    input                               io_master_rvalid,
    input  [1:0]                        io_master_rresp,
    input  [63:0]                       io_master_rdata,
    input                               io_master_rlast,
    input  [3:0]                        io_master_rid,

    output                              io_slave_awready,
    input                               io_slave_awvalid,
    input  [31:0]                       io_slave_awaddr,
    input  [3:0]                        io_slave_awid,
    input  [7:0]                        io_slave_awlen,
    input  [2:0]                        io_slave_awsize,
    input  [1:0]                        io_slave_awburst,
    
    output                              io_slave_wready,
    input                               io_slave_wvalid,
    input  [63:0]                       io_slave_wdata,
    input  [7:0]                        io_slave_wstrb,
    input                               io_slave_wlast,
    
    input                               io_slave_bready,
    output                              io_slave_bvalid,
    output [1:0]                        io_slave_bresp,
    output [3:0]                        io_slave_bid,

    output                              io_slave_arready,
    input                               io_slave_arvalid,
    input  [31:0]                       io_slave_araddr,
    input  [3:0]                        io_slave_arid,
    input  [7:0]                        io_slave_arlen,
    input  [2:0]                        io_slave_arsize,
    input  [1:0]                        io_slave_arburst,
    
    input                               io_slave_rready,
    output                              io_slave_rvalid,
    output [1:0]                        io_slave_rresp,
    output [63:0]                       io_slave_rdata,
    output                              io_slave_rlast,
    output [3:0]                        io_slave_rid
);
    //Definition

    //cpu
    wire[`RAM_ADDR_WIDTH - 1:0]     iram_addr;
    wire[`RAM_DATA_WIDTH - 1:0]     iram_rdata;
    wire                            iram_valid;
    wire                            iram_ready;

    wire                            dram_wen;
    wire[`RAM_ADDR_WIDTH - 1:0]     dram_addr;
    wire[`RAM_DATA_WIDTH - 1:0]     dram_wdata;
    wire[`RAM_DATA_WIDTH / 8 - 1:0] dram_wmask;
    wire[`RAM_DATA_WIDTH - 1:0]     dram_rdata;
    wire[2:0]                       dram_rw_size;

    wire                            dram_valid;
    wire                            dram_ready;

    ysyx_210413_arbiter_to_axi arbiter_to_axi_sim(

        .clk                    (clock),
        .rst                    (reset),

        .iram_addr              (iram_addr),
        .iram_rdata             (iram_rdata),

        .iram_valid             (iram_valid),
        .iram_ready             (iram_ready),

        .dram_wen               (dram_wen),
        .dram_addr              (dram_addr),
        .dram_wdata             (dram_wdata),
        .dram_wmask             (dram_wmask),
        .dram_rdata             (dram_rdata),
        .dram_rw_size           (dram_rw_size),

        .dram_valid             (dram_valid),
        .dram_ready             (dram_ready),
    ////////////////////////////axi interface
    // aw
        .awid                   (io_master_awid),
        .awaddr                 (io_master_awaddr),
        .awlen                  (io_master_awlen),
        .awsize                 (io_master_awsize),
        .awburst                (io_master_awburst),
        .awvalid                (io_master_awvalid),
        .awready                (io_master_awready),
    // w
        .wdata                  (io_master_wdata),
        .wstrb                  (io_master_wstrb),
        .wlast                  (io_master_wlast),
        .wvalid                 (io_master_wvalid),
        .wready                 (io_master_wready),
    // b
        .bid                    (io_master_bid),
        .bresp                  (io_master_bresp),
        .bvalid                 (io_master_bvalid),
        .bready                 (io_master_bready),
    // ar
        .arid                   (io_master_arid),
        .araddr                 (io_master_araddr),
        .arlen                  (io_master_arlen),
        .arsize                 (io_master_arsize),
        .arburst                (io_master_arburst),
        .arvalid                (io_master_arvalid),
        .arready                (io_master_arready),
    // r
        .rid                    (io_master_rid),
        .rlast                  (io_master_rlast),
        .rdata                  (io_master_rdata),
        .rresp                  (io_master_rresp),
        .rvalid                 (io_master_rvalid),
        .rready                 (io_master_rready)
    );

    ysyx_210413_cpu cpu_sim(
        .clock(clock),
        .reset(reset),

        .iram_addr      (iram_addr),
        .iram_rdata     (iram_rdata),

        .iram_valid     (iram_valid),
        .iram_ready     (iram_ready),

        .dram_wen       (dram_wen),
        .dram_addr      (dram_addr),
        .dram_wdata     (dram_wdata),
        .dram_wmask     (dram_wmask),
        .dram_rdata     (dram_rdata),
        .dram_rw_size   (dram_rw_size),

        .dram_valid     (dram_valid),
        .dram_ready     (dram_ready)
    );
endmodule


module ysyx_210413_cpu(
    input                                   clock,
    input                                   reset,

    output wire[`RAM_ADDR_WIDTH - 1:0]      iram_addr,
    input  wire[`RAM_DATA_WIDTH - 1:0]      iram_rdata,

    output wire                             iram_valid,
    input  wire                             iram_ready,

    output wire                             dram_wen,
    output wire[`RAM_ADDR_WIDTH - 1:0]      dram_addr,
    output wire[`RAM_DATA_WIDTH - 1:0]      dram_wdata,
    output wire[`RAM_DATA_WIDTH / 8 - 1:0]  dram_wmask,
    input  wire[`RAM_DATA_WIDTH - 1:0]      dram_rdata,
    output wire[2:0]                        dram_rw_size,

    output wire                             dram_valid,
    input  wire                             dram_ready
);


    // Definition
    // ctrl
    wire[4:0]                           ctrl_stall_o;
    wire[3:0]                           ctrl_flush_o;
    // if stage
    wire [`RAM_ADDR_WIDTH - 1:0]        if_inst_addr_o;
    wire [`INST_WIDTH - 1: 0]           if_inst_o;
    wire                                stall_pc_flag_o;
    wire                                flush_if_id_flag_o;
    // id stage
    wire [`RAM_ADDR_WIDTH - 1:0]        id_inst_addr_i;
    wire [`INST_WIDTH - 1: 0]           id_inst_i;

    wire [`REG_BUS]                     id_csr_r_data_i;

    wire                                id_csr_r_ena_o;
    wire [11: 0]                        id_csr_r_addr_o;

    wire [`REG_BUS]                     id_rs1_r_data_i;
    wire [`REG_BUS]                     id_rs2_r_data_i;

    wire                                id_rs1_r_ena_o;
    wire [4 : 0]                        id_rs1_r_addr_o;
    wire                                id_rs2_r_ena_o;
    wire [4 : 0]                        id_rs2_r_addr_o;

    wire [`RAM_ADDR_WIDTH - 1:0]        id_inst_addr_o;
    wire [`INST_WIDTH - 1: 0]           id_inst_o;

    wire                                id_rd_w_ena_o;
    wire [4 : 0]                        id_rd_w_addr_o;

    wire                                id_csr_w_ena_o;
    wire [11: 0]                        id_csr_w_addr_o;

    wire [`REG_BUS]                     id_op1_o;
    wire [`REG_BUS]                     id_op2_o;
    wire [`REG_BUS]                     id_op3_o;

    wire[`ALU_SEL_BUS]                  id_alu_sel_o;
    wire                                id_alu_sub_flag_o;
    wire                                id_alu_word_flag_o;
    wire                                id_alu_symbol_flag_o;

    wire                                id_transfer_en_o;
    wire[`TRANSFER_SEL_BUS]             id_transfer_sel_o;

    wire                                id_mem_load_en_o;
    wire                                id_mem_store_en_o;
    wire[`MEM_SEL_BUS]                  id_mem_sel_o;

    // wire                                id_csr_en_o;
    wire[`CSR_SEL_BUS]                  id_csr_sel_o;

    wire[`RD_SEL_BUS]                   id_rd_sel_o;

    wire [`REG_BUS]                     id_exception_type_o;

    wire                                id_valid_o;
    wire                                id_stall_flag_o;
    //exe stage

    wire [`RAM_ADDR_WIDTH - 1:0]        exe_inst_addr_i;
    wire [`INST_WIDTH - 1: 0]           exe_inst_i;

    wire                                exe_csr_w_ena_i;
    wire [11: 0]                        exe_csr_w_addr_i;

    wire                                exe_rd_w_ena_i;
    wire [4 : 0]                        exe_rd_w_addr_i;

    wire [`REG_BUS]                     exe_op1_i;
    wire [`REG_BUS]                     exe_op2_i;
    wire [`REG_BUS]                     exe_op3_i;

    wire[`ALU_SEL_BUS]                  exe_alu_sel_i;
    wire                                exe_alu_sub_flag_i;
    wire                                exe_alu_word_flag_i;
    wire                                exe_alu_symbol_flag_i;

    wire                                exe_transfer_en_i;
    wire[`TRANSFER_SEL_BUS]             exe_transfer_sel_i;

    // wire                                exe_csr_en_i;
    wire[`CSR_SEL_BUS]                  exe_csr_sel_i;

    wire                                exe_mem_load_en_i;
    wire                                exe_mem_store_en_i;
    wire[`MEM_SEL_BUS]                  exe_mem_sel_i;

    wire[`RD_SEL_BUS]                   exe_rd_sel_i;

    wire [`REG_BUS]                     exe_exception_type_i;
    wire                                exe_valid_i;

    wire [`RAM_ADDR_WIDTH - 1:0]        exe_inst_addr_o;
    wire [`INST_WIDTH - 1: 0]           exe_inst_o;

    wire                                exe_csr_w_ena_o;
    wire [11: 0]                        exe_csr_w_addr_o;
    wire [`REG_BUS]                     exe_csr_w_data_o;

    wire                                exe_rd_w_ena_o;
    wire [4 : 0]                        exe_rd_w_addr_o;
    wire [`REG_BUS]                     exe_rd_w_data_o;

    wire [`RAM_ADDR_WIDTH - 1:0]        exe_mem_addr_o;
    wire [`RAM_DATA_WIDTH - 1:0]        exe_mem_w_data_o;

    wire                                exe_transfer_flag_o;
    wire [`RAM_ADDR_WIDTH - 1:0]        exe_transfer_addr_o;


    wire                                exe_mem_load_en_o;
    wire                                exe_mem_store_en_o;
    wire[`MEM_SEL_BUS]                  exe_mem_sel_o;

    wire [`REG_BUS]                     exe_exception_type_o;
    wire                                exe_valid_o;
    //mem stage
 
    wire [`RAM_ADDR_WIDTH - 1:0]        mem_inst_addr_i;
    wire [`INST_WIDTH - 1: 0]           mem_inst_i;

    wire                                mem_csr_w_ena_i;
    wire [11: 0]                        mem_csr_w_addr_i;
    wire [`REG_BUS]                     mem_csr_w_data_i;

    wire                                mem_rd_w_ena_i;
    wire [4 : 0]                        mem_rd_w_addr_i;
    wire [`REG_BUS]                     mem_rd_w_data_i;

    wire [`RAM_ADDR_WIDTH - 1:0]        mem_mem_addr_i;
    wire [`RAM_DATA_WIDTH - 1:0]        mem_mem_w_data_i;

    wire [`RAM_DATA_WIDTH - 1:0]        mem_mem_r_data_i;

    wire                                mem_mem_load_en_i;
    wire                                mem_mem_store_en_i;
    wire[`MEM_SEL_BUS]                  mem_mem_sel_i;

    wire [`REG_BUS]                     mem_exception_type_i;
    wire                                mem_valid_i;

    wire [`RAM_ADDR_WIDTH - 1:0]        mem_inst_addr_o;
    wire [`INST_WIDTH - 1: 0]           mem_inst_o;

    wire                                mem_csr_w_ena_o;
    wire [11: 0]                        mem_csr_w_addr_o;
    wire [`REG_BUS]                     mem_csr_w_data_o;

    wire                                mem_rd_w_ena_o;
    wire [ 4: 0]                        mem_rd_w_addr_o;
    wire [`REG_BUS]                     mem_rd_w_data_o;
    
    wire [`RAM_DATA_WIDTH / 8 - 1:0]    mem_dram_w_mask_o;
    wire [`RAM_DATA_WIDTH - 1:0]        mem_dram_w_data_o;
    wire                                mem_dram_w_en_o;
    wire [`RAM_ADDR_WIDTH - 1:0]        mem_dram_addr_o;
    wire [2:0]                          mem_dram_rw_size_o;

    wire                                mem_dram_valid;
    wire                                mem_dram_ready;

    wire                                mem_stall_3_2_1_flag_o;

    wire [`REG_BUS]                     mem_exception_type_o;
    wire                                mem_valid_o;
    wire                                mem_skip_o;
    //wb stage
    wire [`RAM_ADDR_WIDTH - 1:0]        wb_inst_addr_i;
    wire [`INST_WIDTH - 1: 0]           wb_inst_i;

    wire                                wb_csr_w_ena_i;
    wire [11: 0]                        wb_csr_w_addr_i;
    wire [`REG_BUS]                     wb_csr_w_data_i;

    wire                                wb_rd_w_ena_i;
    wire [4 : 0]                        wb_rd_w_addr_i;
    wire [`REG_BUS]                     wb_rd_w_data_i;

    wire [`REG_BUS]                     wb_exception_type_i;
    wire                                wb_valid_i;

    wire                                wb_skip_i;

    wire [`RAM_ADDR_WIDTH - 1:0]        wb_inst_addr_o;
    wire [`INST_WIDTH - 1: 0]           wb_inst_o;

    wire                                wb_csr_w_ena_o;
    wire [11: 0]                        wb_csr_w_addr_o;
    wire [`REG_BUS]                     wb_csr_w_data_o;

    wire                                wb_rd_w_ena_o;
    wire [4 : 0]                        wb_rd_w_addr_o;
    wire [`REG_BUS]                     wb_rd_w_data_o;

    wire [`REG_BUS]                     wb_exception_type_o;
    wire                                wb_valid_o;

    wire                                wb_skip_o;
    //csr
    wire                                csr_transfer_flag_o;
    wire [`RAM_ADDR_WIDTH - 1:0]        csr_transfer_addr_o;

    wire                                csr_timer_interrupt_flag_o;

    //clint
    wire                                clint_timer_interrupt_o;

/////////////////////////////////////////////////////////////////////////////////////////////////////
    //ctrl
    ysyx_210413_ctrl Ctrl(

        .stall_pc_flag_i        (stall_pc_flag_o),

        .flush_if_id_flag_i     (flush_if_id_flag_o),

        .stall_flag_from_id_i   (id_stall_flag_o),

        .flush_flag_from_exe_i  (exe_transfer_flag_o),

        .stall_3_2_1_flag_i     (mem_stall_3_2_1_flag_o),

        .csr_transfer_flag_i    (csr_transfer_flag_o),

        .stall_o                (ctrl_stall_o),
        .flush_o                (ctrl_flush_o)
    );
    //if_stage

    ysyx_210413_if_stage If_stage(
        .clk                    (clock),
        .rst                    (reset),

        .stall_i                (ctrl_stall_o[4]),

        .transfer_flag_i        (exe_transfer_flag_o),
        .transfer_addr_i        (exe_transfer_addr_o),

        .exception_flag_i       (csr_transfer_flag_o),
        .exception_addr_i       (csr_transfer_addr_o),

        .iram_addr              (iram_addr),
        .iram_rdata             (iram_rdata),
        .iram_valid             (iram_valid),
        .iram_ready             (iram_ready),

        .stall_pc_flag_o        (stall_pc_flag_o),

        .flush_if_id_flag_o     (flush_if_id_flag_o),

        .inst_addr              (if_inst_addr_o),
        .inst                   (if_inst_o)
    );

    ysyx_210413_if_id If_id(
        .clk                    (clock),
        .rst                    (reset),

        .stall_i                (ctrl_stall_o[3]),
        .flush_i                (ctrl_flush_o[3]),

        .inst_addr_i            (if_inst_addr_o),
        .inst_i                 (if_inst_o),

        .inst_addr_o            (id_inst_addr_i),
        .inst_o                 (id_inst_i)
    );
    // id_stage
    ysyx_210413_id_stage Id_stage(
        .rst                    (reset),
        .timer_interrupt_flag_i (csr_timer_interrupt_flag_o),

        .inst_addr_i            (id_inst_addr_i),
        .inst_i                 (id_inst_i),
        
        .exe_csr_w_addr_i       (exe_csr_w_addr_o),
        .exe_csr_w_data_i       (exe_csr_w_data_o),
        .exe_csr_w_ena_i        (exe_csr_w_ena_o),

        .mem_csr_w_addr_i       (mem_csr_w_addr_o),
        .mem_csr_w_data_i       (mem_csr_w_data_o),
        .mem_csr_w_ena_i        (mem_csr_w_ena_o),

        .wb_csr_w_addr_i        (wb_csr_w_addr_o),
        .wb_csr_w_data_i        (wb_csr_w_data_o),
        .wb_csr_w_ena_i         (wb_csr_w_ena_o),

        .csr_r_data_i           (id_csr_r_data_i),
        .csr_r_ena_o            (id_csr_r_ena_o),
        .csr_r_addr_o           (id_csr_r_addr_o),

        .exe_mem_load_en_i      (exe_mem_load_en_o),

        .exe_rd_w_ena_i         (exe_rd_w_ena_o),
        .exe_rd_w_addr_i        (exe_rd_w_addr_o),
        .exe_rd_w_data_i        (exe_rd_w_data_o),

        .mem_rd_w_ena_i         (mem_rd_w_ena_o),
        .mem_rd_w_addr_i        (mem_rd_w_addr_o),
        .mem_rd_w_data_i        (mem_rd_w_data_o),

        .wb_rd_w_ena_i          (wb_rd_w_ena_o),
        .wb_rd_w_addr_i         (wb_rd_w_addr_o),
        .wb_rd_w_data_i         (wb_rd_w_data_o),

        .rs1_r_data_i           (id_rs1_r_data_i),
        .rs2_r_data_i           (id_rs2_r_data_i),

        .rs1_r_ena_o            (id_rs1_r_ena_o),
        .rs1_r_addr_o           (id_rs1_r_addr_o),
        .rs2_r_ena_o            (id_rs2_r_ena_o),
        .rs2_r_addr_o           (id_rs2_r_addr_o),

        .inst_addr_o            (id_inst_addr_o),
        .inst_o                 (id_inst_o),

        .csr_w_ena_o            (id_csr_w_ena_o),
        .csr_w_addr_o           (id_csr_w_addr_o),
        .rd_w_ena_o             (id_rd_w_ena_o),
        .rd_w_addr_o            (id_rd_w_addr_o),
        .op1_o                  (id_op1_o),
        .op2_o                  (id_op2_o),
        .op3_o                  (id_op3_o),

        .alu_sel_o              (id_alu_sel_o),
        .alu_sub_flag_o         (id_alu_sub_flag_o),
        .alu_word_flag_o        (id_alu_word_flag_o),
        .alu_symbol_flag_o      (id_alu_symbol_flag_o),

        .transfer_en_o          (id_transfer_en_o),
        .transfer_sel_o         (id_transfer_sel_o),

        .mem_load_en_o          (id_mem_load_en_o),
        .mem_store_en_o         (id_mem_store_en_o),
        .mem_sel_o              (id_mem_sel_o),

        // .csr_en_o               (id_csr_en_o),
        .csr_sel_o              (id_csr_sel_o),

        .rd_sel_o               (id_rd_sel_o),

        .exception_type_o       (id_exception_type_o),
        .valid_o                (id_valid_o),
        .stall_flag_o           (id_stall_flag_o)
    );
    ysyx_210413_id_exe Id_exe(
        .clk                    (clock),
        .rst                    (reset),

        .stall_i                (ctrl_stall_o[2]),
        .flush_i                (ctrl_flush_o[2]),

        .inst_addr_i            (id_inst_addr_o),
        .inst_i                 (id_inst_o),

        .csr_w_ena_i            (id_csr_w_ena_o),
        .csr_w_addr_i           (id_csr_w_addr_o),

        .rd_w_ena_i             (id_rd_w_ena_o),
        .rd_w_addr_i            (id_rd_w_addr_o),

        .op1_i                  (id_op1_o),
        .op2_i                  (id_op2_o),
        .op3_i                  (id_op3_o),

        .alu_sel_i              (id_alu_sel_o),
        .alu_sub_flag_i         (id_alu_sub_flag_o),
        .alu_word_flag_i        (id_alu_word_flag_o),
        .alu_symbol_flag_i      (id_alu_symbol_flag_o),

        .transfer_en_i          (id_transfer_en_o),
        .transfer_sel_i         (id_transfer_sel_o),

        // .csr_en_i               (id_csr_en_o),
        .csr_sel_i              (id_csr_sel_o),

        .mem_load_en_i          (id_mem_load_en_o),
        .mem_store_en_i         (id_mem_store_en_o),
        .mem_sel_i              (id_mem_sel_o),

        .rd_sel_i               (id_rd_sel_o),

        .exception_type_i       (id_exception_type_o),
        .valid_i                (id_valid_o),

        .inst_addr_o            (exe_inst_addr_i),
        .inst_o                 (exe_inst_i),

        .csr_w_ena_o            (exe_csr_w_ena_i),
        .csr_w_addr_o           (exe_csr_w_addr_i),

        .rd_w_ena_o             (exe_rd_w_ena_i),
        .rd_w_addr_o            (exe_rd_w_addr_i),

        .op1_o                  (exe_op1_i),
        .op2_o                  (exe_op2_i),
        .op3_o                  (exe_op3_i),

        .alu_sel_o              (exe_alu_sel_i),
        .alu_sub_flag_o         (exe_alu_sub_flag_i),
        .alu_word_flag_o        (exe_alu_word_flag_i),
        .alu_symbol_flag_o      (exe_alu_symbol_flag_i),

        .transfer_en_o          (exe_transfer_en_i),
        .transfer_sel_o         (exe_transfer_sel_i),

        // .csr_en_o               (exe_csr_en_i),
        .csr_sel_o              (exe_csr_sel_i),

        .mem_load_en_o          (exe_mem_load_en_i),
        .mem_store_en_o         (exe_mem_store_en_i),
        .mem_sel_o              (exe_mem_sel_i),

        .rd_sel_o               (exe_rd_sel_i),

        .exception_type_o       (exe_exception_type_i),
        .valid_o                (exe_valid_i)
    );
    // exe_stage
    
    ysyx_210413_exe_stage Exe_stage(
        .rst                    (reset),

        .inst_addr_i            (exe_inst_addr_i),
        .inst_i                 (exe_inst_i),

        .csr_w_ena_i            (exe_csr_w_ena_i),
        .csr_w_addr_i           (exe_csr_w_addr_i),

        .rd_w_ena_i             (exe_rd_w_ena_i),
        .rd_w_addr_i            (exe_rd_w_addr_i),

        .op1_i                  (exe_op1_i),
        .op2_i                  (exe_op2_i),
        .op3_i                  (exe_op3_i),

        .alu_sel_i              (exe_alu_sel_i),
        .alu_sub_flag_i         (exe_alu_sub_flag_i),
        .alu_word_flag_i        (exe_alu_word_flag_i),
        .alu_symbol_flag_i      (exe_alu_symbol_flag_i),

        .transfer_en_i          (exe_transfer_en_i),
        .transfer_sel_i         (exe_transfer_sel_i),

        // .csr_en_i               (exe_csr_en_i),
        .csr_sel_i              (exe_csr_sel_i),

        .mem_load_en_i          (exe_mem_load_en_i),
        .mem_store_en_i         (exe_mem_store_en_i),
        .mem_sel_i              (exe_mem_sel_i),

        .rd_sel_i               (exe_rd_sel_i),

        .exception_type_from_wb_i   (wb_exception_type_o),
        .exception_type_from_mem_i  (mem_exception_type_o),
        .exception_type_i       (exe_exception_type_i),
        .valid_i                (exe_valid_i),

        .inst_addr_o            (exe_inst_addr_o),
        .inst_o                 (exe_inst_o),

        .csr_w_ena_o            (exe_csr_w_ena_o),
        .csr_w_addr_o           (exe_csr_w_addr_o),
        .csr_w_data_o           (exe_csr_w_data_o),

        .rd_w_ena_o             (exe_rd_w_ena_o),
        .rd_w_addr_o            (exe_rd_w_addr_o),
        .rd_w_data_o            (exe_rd_w_data_o),

        .mem_addr_o             (exe_mem_addr_o),
        .mem_w_data_o           (exe_mem_w_data_o),

        .transfer_flag_o        (exe_transfer_flag_o),
        .transfer_addr_o        (exe_transfer_addr_o),
    
        .mem_load_en_o          (exe_mem_load_en_o),
        .mem_store_en_o         (exe_mem_store_en_o),
        .mem_sel_o              (exe_mem_sel_o),

        .exception_type_o       (exe_exception_type_o),
        .valid_o                (exe_valid_o)
    );
    // mem stage
    ysyx_210413_exe_mem Exe_mem(
        .clk                    (clock),
        .rst                    (reset),

        .stall_i                (ctrl_stall_o[1]),
        .flush_i                (ctrl_flush_o[1]),

        .inst_addr_i            (exe_inst_addr_o),
        .inst_i                 (exe_inst_o),

        .csr_w_ena_i            (exe_csr_w_ena_o),
        .csr_w_addr_i           (exe_csr_w_addr_o),
        .csr_w_data_i           (exe_csr_w_data_o),

        .rd_w_ena_i             (exe_rd_w_ena_o),
        .rd_w_addr_i            (exe_rd_w_addr_o),
        .rd_w_data_i            (exe_rd_w_data_o),

        .mem_addr_i             (exe_mem_addr_o),
        .mem_w_data_i           (exe_mem_w_data_o),

        .mem_load_en_i          (exe_mem_load_en_o),
        .mem_store_en_i         (exe_mem_store_en_o),
        .mem_sel_i              (exe_mem_sel_o),

        .exception_type_i       (exe_exception_type_o),
        .valid_i                (exe_valid_o),

        .inst_addr_o            (mem_inst_addr_i),
        .inst_o                 (mem_inst_i),

        .csr_w_ena_o            (mem_csr_w_ena_i),
        .csr_w_addr_o           (mem_csr_w_addr_i),
        .csr_w_data_o           (mem_csr_w_data_i),

        .rd_w_ena_o             (mem_rd_w_ena_i),
        .rd_w_addr_o            (mem_rd_w_addr_i),
        .rd_w_data_o            (mem_rd_w_data_i),

        .mem_addr_o             (mem_mem_addr_i),
        .mem_w_data_o           (mem_mem_w_data_i),

        .mem_load_en_o          (mem_mem_load_en_i),
        .mem_store_en_o         (mem_mem_store_en_i),
        .mem_sel_o              (mem_mem_sel_i),

        .exception_type_o       (mem_exception_type_i),
        .valid_o                (mem_valid_i)
    );

    ysyx_210413_mem_stage Mem_stage(
        .rst                    (reset),

        .inst_addr_i            (mem_inst_addr_i),
        .inst_i                 (mem_inst_i),

        .csr_w_ena_i            (mem_csr_w_ena_i),
        .csr_w_addr_i           (mem_csr_w_addr_i),
        .csr_w_data_i           (mem_csr_w_data_i),

        .rd_w_ena_i             (mem_rd_w_ena_i),
        .rd_w_addr_i            (mem_rd_w_addr_i),
        .rd_w_data_i            (mem_rd_w_data_i),

        .mem_addr_i             (mem_mem_addr_i),
        .mem_w_data_i           (mem_mem_w_data_i),

        .mem_r_data_i           (mem_mem_r_data_i),

        .mem_load_en_i          (mem_mem_load_en_i),
        .mem_store_en_i         (mem_mem_store_en_i),
        .mem_sel_i              (mem_mem_sel_i),

        .exception_type_from_wb_i(wb_exception_type_o),
        .exception_type_i       (mem_exception_type_i),
        .valid_i                (mem_valid_i),

        .inst_addr_o            (mem_inst_addr_o),
        .inst_o                 (mem_inst_o),

        .csr_w_ena_o            (mem_csr_w_ena_o),
        .csr_w_addr_o           (mem_csr_w_addr_o),
        .csr_w_data_o           (mem_csr_w_data_o),

        .rd_w_ena_o             (mem_rd_w_ena_o),
        .rd_w_addr_o            (mem_rd_w_addr_o),
        .rd_w_data_o            (mem_rd_w_data_o),
        
        .dram_w_mask_o          (mem_dram_w_mask_o),
        .dram_w_data_o          (mem_dram_w_data_o),
        .dram_w_en_o            (mem_dram_w_en_o),
        .dram_addr_o            (mem_dram_addr_o),
        .dram_rw_size_o         (mem_dram_rw_size_o),

        .dram_valid             (mem_dram_valid),
        .dram_ready             (mem_dram_ready),

        .stall_3_2_1_flag_o     (mem_stall_3_2_1_flag_o),

        .exception_type_o       (mem_exception_type_o),
        .valid_o                (mem_valid_o)
    );

    //wb stage
    ysyx_210413_mem_wb Mem_wb(
        .clk                    (clock),
        .rst                    (reset),

        .stall_i                (ctrl_stall_o[0]),
        .flush_i                (ctrl_flush_o[0]),

        .inst_addr_i            (mem_inst_addr_o),
        .inst_i                 (mem_inst_o),

        .csr_w_ena_i            (mem_csr_w_ena_o),
        .csr_w_addr_i           (mem_csr_w_addr_o),
        .csr_w_data_i           (mem_csr_w_data_o),

        .rd_w_ena_i             (mem_rd_w_ena_o),
        .rd_w_addr_i            (mem_rd_w_addr_o),
        .rd_w_data_i            (mem_rd_w_data_o),

        .exception_type_i       (mem_exception_type_o),
        .valid_i                (mem_valid_o),
        .skip_i                 (mem_skip_o),

        .inst_addr_o            (wb_inst_addr_i),
        .inst_o                 (wb_inst_i),

        .csr_w_ena_o            (wb_csr_w_ena_i),
        .csr_w_addr_o           (wb_csr_w_addr_i),
        .csr_w_data_o           (wb_csr_w_data_i),

        .rd_w_ena_o             (wb_rd_w_ena_i),
        .rd_w_addr_o            (wb_rd_w_addr_i),
        .rd_w_data_o            (wb_rd_w_data_i),

        .exception_type_o       (wb_exception_type_i),
        .valid_o                (wb_valid_i),
        .skip_o                 (wb_skip_i)
    );

    ysyx_210413_wb_stage Wb_stage(
        .rst                    (reset),

        .inst_addr_i            (wb_inst_addr_i),
        .inst_i                 (wb_inst_i),

        .csr_w_ena_i            (wb_csr_w_ena_i),
        .csr_w_addr_i           (wb_csr_w_addr_i),
        .csr_w_data_i           (wb_csr_w_data_i),

        .rd_w_ena_i             (wb_rd_w_ena_i),
        .rd_w_addr_i            (wb_rd_w_addr_i),
        .rd_w_data_i            (wb_rd_w_data_i),

        .exception_type_i       (wb_exception_type_i),
        .valid_i                (wb_valid_i),

        .skip_i                 (wb_skip_i),

        .inst_addr_o            (wb_inst_addr_o),
        .inst_o                 (wb_inst_o),

        .csr_w_ena_o            (wb_csr_w_ena_o),
        .csr_w_addr_o           (wb_csr_w_addr_o),
        .csr_w_data_o           (wb_csr_w_data_o),

        .rd_w_ena_o             (wb_rd_w_ena_o),
        .rd_w_addr_o            (wb_rd_w_addr_o),
        .rd_w_data_o            (wb_rd_w_data_o),

        .exception_type_o       (wb_exception_type_o),
        .valid_o                (wb_valid_o),

        .skip_o                 (wb_skip_o)
    );

    //regfile
    ysyx_210413_regfile Regfile(
        .clk                    (clock),
        .rst                    (reset),

        .r_addr1                (id_rs1_r_addr_o),
        .r_data1                (id_rs1_r_data_i),
        .r_ena1                 (id_rs1_r_ena_o),

        .r_addr2                (id_rs2_r_addr_o),
        .r_data2                (id_rs2_r_data_i),
        .r_ena2                 (id_rs2_r_ena_o),

        .w_ena                  (wb_rd_w_ena_o),
        .w_addr                 (wb_rd_w_addr_o),
        .w_data                 (wb_rd_w_data_o)
    );
    
    ysyx_210413_csr Csr(
        .clk                    (clock),
        .rst                    (reset),

        .timer_interrupt        (clint_timer_interrupt_o),

        .timer_interrupt_flag_o (csr_timer_interrupt_flag_o),
        
        .r_addr                 (id_csr_r_addr_o),
        .r_data                 (id_csr_r_data_i),
        .r_ena                  (id_csr_r_ena_o),

        .w_addr                 (wb_csr_w_addr_o),
        .w_data                 (wb_csr_w_data_o),
        .w_ena                  (wb_csr_w_ena_o),
        .exception_type         (wb_exception_type_i),
        .inst_addr              (wb_inst_addr_i),

        .transfer_flag          (csr_transfer_flag_o),
        .transfer_addr          (csr_transfer_addr_o)
    );
    wire [ 7: 0]                    mem_w_mask_o_real;
    wire [`RAM_DATA_WIDTH - 1: 0]   mem_w_data_o_real;
    wire                            mem_w_en_o_real;
    wire [`RAM_ADDR_WIDTH - 1: 0]   mem_addr_o_real;

    wire [`RAM_DATA_WIDTH - 1: 0]   clint_r_data;
    wire                            clint_valid;
    wire                            clint_ready;



    ysyx_210413_mem_filter mem_filter_sim(

        .dram_w_mask_i          (mem_dram_w_mask_o),
        .dram_w_data_i          (mem_dram_w_data_o),
        .dram_w_en_i            (mem_dram_w_en_o),
        .dram_r_data_o          (mem_mem_r_data_i),
        .dram_addr_i            (mem_dram_addr_o),
        .dram_valid_i           (mem_dram_valid),
        .dram_ready_o           (mem_dram_ready),

        .dram_w_mask_o          (mem_w_mask_o_real),
        .dram_w_data_o          (mem_w_data_o_real),
        .dram_w_en_o            (mem_w_en_o_real),
        .dram_addr_o            (mem_addr_o_real),

        .dram_r_data_i          (dram_rdata),
        .dram_valid_o           (dram_valid),
        .dram_ready_i           (dram_ready),

        .clint_r_data_i         (clint_r_data),
        .clint_valid_o          (clint_valid),
        .clint_ready_i          (clint_ready),

        .skip_o                 (mem_skip_o)
    );
    ysyx_210413_clint clint_sim(
        .clk                    (clock),
        .rst                    (reset),

        .clint_w_data_i         (mem_w_data_o_real),
        .clint_w_en_i           (mem_w_en_o_real),
        .clint_r_data_o         (clint_r_data),
        .clint_addr_i           (mem_addr_o_real),
        .clint_valid_i          (clint_valid),
        .clint_ready_o          (clint_ready),

        .timer_interrupt        (clint_timer_interrupt_o)
    );
    //////////////////////////////////////////////////////////////////////////////////////////////////

    assign dram_wen     = mem_w_en_o_real;
    assign dram_addr    = mem_addr_o_real;
    assign dram_wdata   = mem_w_data_o_real;
    assign dram_wmask   = mem_w_mask_o_real;
    assign dram_rw_size = mem_dram_rw_size_o;
endmodule


module ysyx_210413_arbiter_to_axi (
    input  wire                             clk,
    input  wire                             rst,

    input  wire[`RAM_ADDR_WIDTH - 1:0]      iram_addr,
    output wire[`RAM_DATA_WIDTH - 1:0]      iram_rdata,

    input  wire                             iram_valid,
    output wire                             iram_ready,

    input  wire                             dram_wen,
    input  wire[`RAM_ADDR_WIDTH - 1:0]      dram_addr,
    input  wire[`RAM_DATA_WIDTH - 1:0]      dram_wdata,
    input  wire[`RAM_DATA_WIDTH / 8 - 1:0]  dram_wmask,
    output wire[`RAM_DATA_WIDTH - 1:0]      dram_rdata,
    input  wire[2:0]                        dram_rw_size,

    input  wire                             dram_valid,
    output wire                             dram_ready,

    ////////////////////////////axi interface
    // aw
    output wire[`AXI_ID_WIDTH - 1:0]        awid,
    output wire[`AXI_ADDR_WIDTH - 1:0]      awaddr,
    output wire[7:0]                        awlen,
    output wire[2:0]                        awsize,
    output wire[1:0]                        awburst,
    output wire                             awvalid,
    input  wire                             awready,
    // w
    output wire[`AXI_DATA_WIDTH - 1:0]      wdata,
    output wire[`AXI_DATA_WIDTH / 8 - 1:0]  wstrb,
    output wire                             wlast,
    output wire                             wvalid,
    input  wire                             wready,
    // b
    input  wire[3:0]                        bid,
    input  wire[1:0]                        bresp,
    input  wire                             bvalid,
    output wire                             bready,
    // ar
    output wire[`AXI_ID_WIDTH - 1:0]        arid,
    output wire[`AXI_ADDR_WIDTH - 1:0]      araddr,
    output wire[7:0]                        arlen,
    output wire[2:0]                        arsize,
    output wire[1:0]                        arburst,
    output wire                             arvalid,
    input  wire                             arready,
    // r
    input  wire[`AXI_ID_WIDTH - 1:0]        rid,
    input  wire[`AXI_DATA_WIDTH - 1:0]      rdata,
    input  wire[1:0]                        rresp,
    input  wire                             rlast,
    input  wire                             rvalid,
    output wire                             rready
);
    reg             inst_buffer_flag;
    wire            inst_buffer_flag_value;
    reg [63: 0]     inst_buffer;
    wire[63: 0]     inst_buffer_value;

    // ar def
    wire inst_addr_ok;
    wire inst_addr_valid;

    reg  inst_load_state;
    wire inst_load_state_value;

    wire data_addr_ok;
    wire data_addr_valid;

    reg  data_load_state;
    wire data_load_state_value;

    // r def
    wire r_shake_ok;
    wire r_inst_ok;
    wire r_data_ok;

    // aw w b
    reg  data_store_state_1;
    reg  data_store_state_0;
    wire data_store_state_1_value;
    wire data_store_state_0_value;

    wire aw_data_store_valid;
    wire aw_data_store_ok;
    wire w_data_store_valid;
    wire w_data_store_ok;
    wire b_data_store_ready;
    wire b_data_store_ok;
    /**********************************************************************************************
    *   ar:
    ***********************************************************************************************/



    //当mem访存的时候，暂停取指
    // assign inst_addr_valid = inst_valid_i == 1'b1
    //                       &&(inst_load_state == 1'b0 || inst_load_state == 1'b1 && r_inst_ok == 1'b1)
    //                       && data_load_state_value == 1'b0
    //                       && data_store_state_0_value == 1'b0 && data_store_state_1_value == 1'b0 ? 1'b1 : 1'b0;
    assign inst_addr_valid = iram_valid == 1'b1
                          && inst_buffer_flag   == 1'b0
                          && inst_load_state    == 1'b0
                          && data_load_state    == 1'b0 && data_addr_valid     == 1'b0 
                          && data_store_state_0 == 1'b0 && aw_data_store_valid == 1'b0 
                          && data_store_state_1 == 1'b0 && w_data_store_valid  == 1'b0 ? 1'b1 : 1'b0;

    assign inst_addr_ok = inst_addr_valid == 1'b1 && arready == 1'b1 ? 1'b1 : 1'b0;

    assign inst_load_state_value = inst_load_state == 1'b0 && inst_addr_ok == 1'b1 ? 1'b1 :
                                   inst_load_state == 1'b1 &&    r_inst_ok == 1'b1 ? 1'b0 : inst_load_state;
    
    // assign data_addr_valid = dram_valid == 1'b1 && dram_wen == 1'b0 && data_load_state == 1'b0 ? 1'b1 : 1'b0;
    assign data_addr_valid = dram_valid == 1'b1 && dram_wen == 1'b0 && data_load_state == 1'b0 && inst_load_state == 1'b0 ? 1'b1 : 1'b0;

    assign data_addr_ok    = data_addr_valid == 1'b1 && arready == 1'b1                        ? 1'b1 : 1'b0;

    assign data_load_state_value = data_load_state == 1'b0 && data_addr_ok == 1'b1 ? 1'b1 :
                                   data_load_state == 1'b1 &&    r_data_ok == 1'b1 ? 1'b0 : data_load_state;
    /**********************************************************************************************
    *   r:
    ***********************************************************************************************/
    assign r_shake_ok = rready & rvalid & rlast & ~rresp[0] & ~rresp[1];
    assign r_inst_ok  = r_shake_ok == 1'b1 && rid == 4'h0 ? 1'b1 : 1'b0;
    assign r_data_ok  = r_shake_ok == 1'b1 && rid == 4'h1 ? 1'b1 : 1'b0;

    wire dram_ing;
    // assign dram_ing = data_load_state_value | data_store_state_0_value | data_store_state_1_value;
    assign dram_ing = dram_valid == 1'b1;

    assign inst_buffer_flag_value = inst_buffer_flag == 1'b0 && dram_ing == 1'b1 && r_inst_ok == 1'b1 ? 1'b1 :
                                    inst_buffer_flag == 1'b1 && dram_ing == 1'b0                      ? 1'b0 : inst_buffer_flag;

    assign inst_buffer_value = inst_buffer_flag == 1'b0 && dram_ing == 1'b1 && r_inst_ok == 1'b1 ? rdata : inst_buffer;
    
    /**********************************************************************************************
    *   aw:
    *   w:
    *   b:
    ***********************************************************************************************/

    // assign aw_data_store_valid      = dram_valid & dram_wen & ~data_store_state_1 ? 1'b1 : 1'b0;
    assign aw_data_store_valid      = dram_valid & dram_wen & ~data_store_state_1 & ~inst_load_state ? 1'b1 : 1'b0;
    assign aw_data_store_ok         = aw_data_store_valid & awready               ? 1'b1 : 1'b0;
    assign data_store_state_1_value = aw_data_store_ok == 1'b1 ? 1'b1 :
                                       b_data_store_ok == 1'b1 ? 1'b0 : data_store_state_1;

    // assign w_data_store_valid       = dram_valid & dram_wen & ~data_store_state_0 ? 1'b1 : 1'b0;
    assign w_data_store_valid       = dram_valid & dram_wen & ~data_store_state_0 & ~inst_load_state ? 1'b1 : 1'b0;
    assign w_data_store_ok          = w_data_store_valid & wready                 ? 1'b1 : 1'b0;
    assign data_store_state_0_value = w_data_store_ok == 1'b1 ? 1'b1 :
                                      b_data_store_ok == 1'b1 ? 1'b0 : data_store_state_0;

    assign b_data_store_ready       = data_store_state_1 & data_store_state_0 ? 1'b1 : 1'b0;
    // assign b_data_store_ok          = b_data_store_ready & bvalid             ? 1'b1 : 1'b0;
    assign b_data_store_ok          = b_data_store_ready && bvalid && bid == 4'b0001 && bresp == 2'b00 ? 1'b1 : 1'b0;

    always @(posedge clk) begin
        if (rst == 1'b1)
        begin
            inst_load_state     <= 0;
            data_load_state     <= 0;
            data_store_state_1  <= 0;
            data_store_state_0  <= 0;

            inst_buffer_flag    <= 0;
            inst_buffer         <= 0;
        end
        else
        begin
            inst_load_state     <= inst_load_state_value;
            data_load_state     <= data_load_state_value;
            data_store_state_1  <= data_store_state_1_value;
            data_store_state_0  <= data_store_state_0_value;

            inst_buffer_flag    <= inst_buffer_flag_value;
            inst_buffer         <= inst_buffer_value;
        end
    end 
    /**********************************************************************************************
    * cpu interface
    ***********************************************************************************************/
    //inst
    assign iram_rdata = inst_buffer_flag == 1'b0 ?       rdata[63:0] :
                        inst_buffer_flag == 1'b1 ? inst_buffer[63:0] : 0;

    assign iram_ready = ~inst_buffer_flag & ~dram_ing & r_inst_ok
                      |  inst_buffer_flag & ~dram_ing;

    //data
    assign dram_ready   = data_load_state    & r_data_ok
                        | data_store_state_0 & data_store_state_1 & bvalid;
    assign dram_rdata   = rdata;

    /**********************************************************************************************
    * axi interface
    ***********************************************************************************************/
    // ar
    assign arid     = data_addr_valid == 1'b1 ? 4'h1 : 4'h0;
    assign araddr   = data_addr_valid == 1'b1 ? {dram_addr[`RAM_ADDR_WIDTH - 1:0]} : {iram_addr[`RAM_ADDR_WIDTH - 1:0]};
    // assign araddr   = data_addr_valid == 1'b1 ? {dram_addr[`RAM_ADDR_WIDTH - 1:3], 3'h0} : {iram_addr[`RAM_ADDR_WIDTH - 1:3], 3'h0};
    assign arlen    = 8'b0;
    assign arsize   = inst_addr_valid ? 3'b010 : dram_rw_size;
    // assign arsize   = dram_rw_size;
    assign arburst  = 2'b01;
    assign arvalid  = inst_addr_valid | data_addr_valid ? 1'h1 : 1'h0;

    // r
    assign rready   = 1'h1;

    // aw
    assign awid     = 4'b0001;
    assign awaddr   = dram_addr;
    assign awlen    = 8'b0;
    //000 1Byte
    //001 2Byte
    //010 4Byte
    //011 8Byte
    assign awsize   = dram_rw_size;
    assign awburst  = 2'b01;
    assign awvalid  = aw_data_store_valid;

    // w
    assign wdata    = dram_wdata;
    assign wstrb    = dram_wmask;
    assign wlast    = 1'b1;
    assign wvalid   = w_data_store_valid;

    // b
    assign bready   = b_data_store_ready;
endmodule


module ysyx_210413_clint (//Core-Local Interruptor
    input  wire clk,
    input  wire rst,
    
    input  wire [`REG_BUS]               clint_w_data_i,
    input  wire                          clint_w_en_i,
    input  wire [`RAM_ADDR_WIDTH - 1: 0] clint_addr_i,
    input  wire                          clint_valid_i,
    output wire                          clint_ready_o,
    
    output reg [`REG_BUS]                clint_r_data_o,

    output wire                          timer_interrupt

    // output wire             mtip_clear
);
    // mtime >= mtimecmp时，产生计时器中断，mip的MTIP位置1；

    // Machine time register
    reg [`REG_BUS]      mtime;
    wire[`REG_BUS]      mtime_add;
    wire[`REG_BUS]      mtime_value;

    reg [2:0]           temp_counter;
    wire[2:0]           temp_counter_value;
    assign temp_counter_value = temp_counter + 1;
    // Machine time compare register
    reg [`REG_BUS]      mtimecmp;
    wire[`REG_BUS]      mtimecmp_value;

    // assign mtime_add = temp_counter_value == 0 ? mtime + 1 : mtime;
    assign mtime_add = mtime + 1;
    assign mtime_value    = (clint_valid_i == 1'b1) && (clint_w_en_i == 1'b1) && (clint_addr_i == `RAM_ADDR_WIDTH'h200bff8) ? clint_w_data_i : mtime_add;
    
    assign mtimecmp_value = (clint_valid_i == 1'b1) && (clint_w_en_i == 1'b1) && (clint_addr_i == `RAM_ADDR_WIDTH'h2004000) ? clint_w_data_i : mtimecmp;

    assign timer_interrupt= mtime >= mtimecmp ? 1'b1 : 1'b0;

    // assign mtip_clear     = (clint_valid_i == 1'b1) && (clint_w_en_i == 1'b1) && (clint_addr_i == 64'h2004000) ? 1'b1 : 1'b0;

    always @(posedge clk)begin
        if ( rst == 1'b1 ) begin
            mtime       <= `ZERO_WORD;
            mtimecmp    <= `ZERO_WORD;
            temp_counter<= 0;
        end
        else begin
            mtime       <= mtime_value;
            mtimecmp    <= mtimecmp_value;
            temp_counter<= temp_counter_value;
        end
    end

    always @(*) begin
        if (rst == 1'b1) begin
            clint_r_data_o = `ZERO_WORD;
        end else if (clint_valid_i == 1'b1 && clint_w_en_i == 1'b0) begin
            case (clint_addr_i)
                `RAM_ADDR_WIDTH'h200bff8: begin
                    clint_r_data_o = mtime;
                end 
                `RAM_ADDR_WIDTH'h2004000: begin
                    clint_r_data_o = mtimecmp;
                end
                default: begin
                    clint_r_data_o = `ZERO_WORD;
                end
            endcase
        end else begin
            clint_r_data_o = `ZERO_WORD; 
        end
    end

    assign clint_ready_o = clint_valid_i;
    // // 打印
    // always @(posedge clk) 
    // begin
    //         if((clint_valid_i == 1'b1) && (clint_w_en_i == 1'b1) && (clint_addr_i == 64'ha10003F8))
    //         begin
    //             $write("%c", clint_w_data_i[7:0]);
    //         end
    // end
endmodule


module ysyx_210413_regfile(
    input  wire clk,
    input  wire rst,
    
    input  wire  [4  : 0]   w_addr,
    input  wire  [`REG_BUS] w_data,
    input  wire             w_ena,
    
    input  wire  [4  : 0]   r_addr1,
    output reg   [`REG_BUS] r_data1,
    input  wire             r_ena1,
    
    input  wire  [4  : 0]   r_addr2,
    output reg   [`REG_BUS] r_data2,
    input  wire             r_ena2
);
    // 32 registers
    reg [`REG_BUS]     regs[0 : 31];

    always @(posedge clk) 
    begin
        if ( rst == 1'b1 ) begin
            regs[ 0] <= `ZERO_WORD;
            regs[ 1] <= `ZERO_WORD;
            regs[ 2] <= `ZERO_WORD;
            regs[ 3] <= `ZERO_WORD;
            regs[ 4] <= `ZERO_WORD;
            regs[ 5] <= `ZERO_WORD;
            regs[ 6] <= `ZERO_WORD;
            regs[ 7] <= `ZERO_WORD;
            regs[ 8] <= `ZERO_WORD;
            regs[ 9] <= `ZERO_WORD;
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
        else begin
            if ((w_ena == 1'b1) && (w_addr != 5'h00))    
                regs[w_addr] <= w_data;
        end
    end
    
    always @(*) begin
        if (rst == 1'b1)
            r_data1 = `ZERO_WORD;
        else if (r_ena1 == 1'b1)
            r_data1 = regs[r_addr1];
        else
            r_data1 = `ZERO_WORD;
    end
    
    always @(*) begin
        if (rst == 1'b1)
            r_data2 = `ZERO_WORD;
        else if (r_ena2 == 1'b1)
            r_data2 = regs[r_addr2];
        else
            r_data2 = `ZERO_WORD;
    end

endmodule


module ysyx_210413_csr (
    input  wire                             clk,
    input  wire                             rst,

    //interrupt 
    input  wire                             timer_interrupt,

    output wire                             timer_interrupt_flag_o,
    // from id
    input  wire[11: 0]                      r_addr,
    output reg [`REG_BUS]                   r_data,
    input  wire                             r_ena,
    // from wb
    input  wire[11: 0]                      w_addr,
    input  wire[`REG_BUS]                   w_data,
    input  wire                             w_ena,
    //from wb
    input  wire[`REG_BUS]                   exception_type,
    input  wire[`RAM_ADDR_WIDTH - 1 : 0]    inst_addr,
    //to ctrl&if
    output wire                             transfer_flag,
    output wire[`RAM_ADDR_WIDTH - 1 : 0]    transfer_addr
);

    // exception
    wire                exception_flag;
    wire                ret_flag;
    wire [`REG_BUS]     exception_code;

    reg [`REG_BUS]      mcycle;
    wire[`REG_BUS]      mcycle_add;
    wire[`REG_BUS]      mcycle_value;

    reg [`REG_BUS]      sstatus;
    wire[`REG_BUS]      sstatus_value;
    //[3]       :MIE
    //[7]       :MPIE
    //[12:11]   :MPP
    reg [`REG_BUS]      mstatus;
    wire[`REG_BUS]      mstatus_value;
    wire                mstatus_sd_value;
    //
    reg [`REG_BUS]      mtvec;
    wire[`REG_BUS]      mtvec_value;

    //
    reg [`REG_BUS]      mepc;
    wire[`REG_BUS]      mepc_value;

    //
    reg [`REG_BUS]      mcause;
    wire[`REG_BUS]      mcause_value;

    reg [`REG_BUS]      mip;
    wire                mip_mtip;
    wire[`REG_BUS]      mip_value;

    reg [`REG_BUS]      mie;
    wire[`REG_BUS]      mie_value;

    reg [`REG_BUS]      mscratch;
    wire[`REG_BUS]      mscratch_value;

    assign exception_code = (exception_type[39] == 1'b1) ? 64'h8000000000000007 :
                            (exception_type[ 5] == 1'b1) ? 64'hb                : `ZERO_WORD;    // ecall
    assign exception_flag = exception_code != 0 ? 1'b1 : 1'b0;
    assign ret_flag       = exception_type[32]  ? 1'b1 : 1'b0;

    assign transfer_flag = exception_flag | ret_flag;
    assign transfer_addr = exception_flag ? {mtvec[`RAM_ADDR_WIDTH - 1: 2], 2'h0} :
                           ret_flag       ? mepc[`RAM_ADDR_WIDTH - 1 : 0]         : 0;

    assign mcycle_add       = mcycle + 64'h1;
    assign mcycle_value     = (w_ena == 1'b1) && (w_addr == `CSR_MCYCLE)    ? w_data    : mcycle_add;

    assign mstatus_value    = exception_flag                                ? {mstatus_sd_value, mstatus[62:13], 2'b11, mstatus[10: 8], mstatus[3], mstatus[ 6: 4],       1'b0, mstatus[ 2: 0]}:
                              ret_flag                                      ? {mstatus_sd_value, mstatus[62:13], 2'b00, mstatus[10: 8], 1'b1      , mstatus[ 6: 4], mstatus[7], mstatus[ 2: 0]}:
                              (w_ena == 1'b1) && (w_addr == `CSR_MSTATUS)   ? {mstatus_sd_value, w_data[62: 0]}    : mstatus;

    assign mstatus_sd_value = (w_ena == 1'b1) && (w_addr == `CSR_MSTATUS) && (w_data[16:15] == 2'b11 || w_data[14:13] == 2'b11) ? 1'b1 :
                              (w_ena == 1'b1) && (w_addr == `CSR_MSTATUS) && (w_data[16:15] == 2'b00 && w_data[14:13] == 2'b00) ? 1'b0 : mstatus[63];

    assign sstatus_value    = (w_ena == 1'b1) && (w_addr == `CSR_MSTATUS) && (w_data[16:15] == 2'b11 || w_data[14:13] == 2'b11) ? 64'h8000000000006000 :
                              (w_ena == 1'b1) && (w_addr == `CSR_MSTATUS) && (w_data[16:15] == 2'b00 && w_data[14:13] == 2'b00) ? 64'h0 : sstatus;

    assign mtvec_value      = (w_ena == 1'b1) && (w_addr == `CSR_MTVEC)     ? w_data    : mtvec;
    
    assign mepc_value       = exception_flag                                ? {{64 - `RAM_ADDR_WIDTH{1'b0}}, inst_addr} :
                              (w_ena == 1'b1) && (w_addr == `CSR_MEPC)      ? w_data                                    : mepc;
    
    assign mcause_value     = exception_flag                                ? exception_code :
                              (w_ena == 1'b1) && (w_addr == `CSR_MCAUSE)    ? w_data         : mcause;

    assign mip_mtip         = timer_interrupt;
    assign mip_value        = {mip[63: 8], mip_mtip, mip[ 6: 0]};

    assign mie_value        = (w_ena == 1'b1) && (w_addr == `CSR_MIE)       ? w_data    : mie;

    assign mscratch_value   = (w_ena == 1'b1) && (w_addr == `CSR_MSCRATCH)  ? w_data    : mscratch;
    //中断
    assign timer_interrupt_flag_o = mstatus[3] & mie[7] & mip[7];

    always @(*) begin
        if (rst == 1'b1) begin
            r_data = `ZERO_WORD;
        end else if (r_ena == 1'b1) begin
            case (r_addr)
                `CSR_MCYCLE:    begin
                    r_data = mcycle;
                end
                `CSR_MSTATUS:   begin
                    r_data = mstatus;
                end
                `CSR_MTVEC:     begin
                    r_data = mtvec;
                end
                `CSR_MEPC:      begin
                    r_data = mepc;
                end
                `CSR_MCAUSE:    begin
                    r_data = mcause;
                end
                `CSR_MSCRATCH:  begin
                    r_data = mscratch; 
                end
                default: begin
                    r_data = `ZERO_WORD;
                end
            endcase
        end else begin
            r_data = `ZERO_WORD; 
        end
    end

    always @(posedge clk)begin
        if ( rst == 1'b1 ) begin
            mcycle  <= `ZERO_WORD;
            mstatus <= {51'h0, 2'b11, 11'b0};
            sstatus <= `ZERO_WORD;
            mtvec   <= `ZERO_WORD;
            mepc    <= `ZERO_WORD;
            mcause  <= `ZERO_WORD;
            mip     <= `ZERO_WORD;
            mie     <= `ZERO_WORD;
            mscratch<= `ZERO_WORD;
        end
        else begin
            mcycle  <= mcycle_value;
            mstatus <= mstatus_value;
            sstatus <= sstatus_value;
            mtvec   <= mtvec_value;
            mepc    <= mepc_value;
            mcause  <= mcause_value;
            mip     <= mip_value;
            mie     <= mie_value;
            mscratch<= mscratch_value;
        end
    end

endmodule


module ysyx_210413_ctrl (

    input  wire                 stall_pc_flag_i,

    input  wire                 flush_if_id_flag_i,
    
    input  wire                 stall_flag_from_id_i,
    
    input  wire                 flush_flag_from_exe_i,

    input  wire                 stall_3_2_1_flag_i,

    input  wire                 csr_transfer_flag_i,

    output wire[4:0]            stall_o,
    output wire[3:0]            flush_o
);

    /*******************
    index:  4       3       2       1       0
            pc      if/id   id/exe  exe/mem mem/wb
    *****************************************************
                                        stall       flush
    flush_flag_from_exe_i                           01100

    stall_flag_from_id_i                11000       00100
    
    stall_pc_flag_i                     10000
    
    flush_if_id_flag_i                  01000
    
    stall_3_2_1_flag_i                  11110       00001                当mem是访存指令时，在arbiter_to_axi中，在完成上一个取指transaction后，会暂停继续取指，如果不暂停pc的话，pc会不断自增且地址未发送出去。

    csr_transfer_flag_i                             01111
    *******************/

    // //flush_flag_from_exe_i 与 stall_flag_from_id_i同一时间只能发生一个，所以顺序无所谓

    assign stall_o = {5{stall_flag_from_id_i}}  & 5'b01000
                   | {5{stall_pc_flag_i}}       & 5'b10000
                   | {5{stall_3_2_1_flag_i}}    & 5'b11110;

    assign flush_o = {4{csr_transfer_flag_i}}   & 4'b1111
                   | {4{flush_flag_from_exe_i}} & 4'b1100
                   | {4{stall_flag_from_id_i}}  & 4'b0100
                   | {4{flush_if_id_flag_i}}    & 4'b1000
                   | {4{stall_3_2_1_flag_i}}    & 4'b0001;
endmodule



module ysyx_210413_if_stage(
    input  wire                             clk,
    input  wire                             rst,

    input  wire                             stall_i,

    input  wire                             transfer_flag_i,
    input  wire [`RAM_ADDR_WIDTH - 1 : 0]   transfer_addr_i,

    input  wire                             exception_flag_i,
    input  wire [`RAM_ADDR_WIDTH - 1 : 0]   exception_addr_i,

    output wire [`RAM_ADDR_WIDTH - 1 : 0]   iram_addr,
    input  wire [`RAM_DATA_WIDTH - 1 : 0]   iram_rdata,
    output wire                             iram_valid,
    input  wire                             iram_ready,

    output wire                             stall_pc_flag_o,    
    output wire                             flush_if_id_flag_o,

    output wire [`RAM_ADDR_WIDTH - 1 : 0]   inst_addr,
    output wire [`INST_WIDTH - 1: 0]        inst
);
    reg  [`RAM_ADDR_WIDTH - 1 : 0] pc;
    
    wire [`RAM_ADDR_WIDTH - 1 : 0] pc_add_4;
    wire [`RAM_ADDR_WIDTH - 1 : 0] pc_value;
    
    reg fetch_state;

    reg                             transfer_flag;
    reg [`RAM_ADDR_WIDTH - 1 : 0]   transfer_addr;
    wire                            transfer_flag_value;
    wire[`RAM_ADDR_WIDTH - 1 : 0]   transfer_addr_value;

    reg                             exception_flag;
    reg [`RAM_ADDR_WIDTH - 1 : 0]   exception_addr;
    wire                            exception_flag_value;
    wire[`RAM_ADDR_WIDTH - 1 : 0]   exception_addr_value;

    assign transfer_flag_value  = fetch_state == 1'b0    && iram_ready == 1'b0 &&  transfer_flag_i == 1'b1 ? 1'b1 :
                                  transfer_flag == 1'b1  && iram_ready == 1'b1                             ? 1'b0 : transfer_flag;
    assign exception_flag_value = fetch_state == 1'b0    && iram_ready == 1'b0 && exception_flag_i == 1'b1 ? 1'b1 :
                                  exception_flag == 1'b1 && iram_ready == 1'b1                             ? 1'b0 : exception_flag;

    assign transfer_addr_value  =  transfer_flag == 1'b0 &&  transfer_flag_i == 1'b1 ?  transfer_addr_i : transfer_addr;
    assign exception_addr_value = exception_flag == 1'b0 && exception_flag_i == 1'b1 ? exception_addr_i : exception_addr;
    
    assign pc_add_4 = pc + 4;
    assign pc_value = exception_flag    ? exception_addr   :
                      exception_flag_i  ? exception_addr_i :
                      transfer_flag     ? transfer_addr    :
                      transfer_flag_i   ? transfer_addr_i  :
                                          pc_add_4;

    always @(posedge clk) begin
        if(rst == 1'b1) begin
            transfer_flag  <= 0;
            transfer_addr  <= 0;

            exception_flag <= 0;
            exception_addr <= 0;
        end
        else begin
            transfer_flag  <= transfer_flag_value;
            transfer_addr  <= transfer_addr_value;

            exception_flag <= exception_flag_value;
            exception_addr <= exception_addr_value;
        end 
    end
    // fetch an instruction
    always@(posedge clk)
    begin
        if(rst == 1'b1) begin
            pc <= `PC_START;
        end
        else begin
            if(stall_i == 1'b1) begin
                pc <= pc;
            end
            else begin
                pc <= pc_value;
            end 
        end
    end
    always @(posedge clk) begin
        if(rst == 1'b1) begin
            fetch_state <= 0;
        end 
        else begin
            case (fetch_state)
                1'b0: begin
                    if(iram_ready == 1'b0 && (transfer_flag_i | exception_flag_i) == 1'b1) begin
                        fetch_state <= 1'b1;
                    end
                end
                1'b1: begin
                    if(iram_ready) begin
                        fetch_state <= 1'b0;
                    end
                end
                default:;
            endcase
        end
    end
    //
    //
    // to axi
    assign iram_addr  = pc;
    assign iram_valid = rst == 1'b1 ? 0 : 1;
    //
    //
    // to ctrl
    assign stall_pc_flag_o = ~iram_ready;
    assign flush_if_id_flag_o = fetch_state == 1'b0 && iram_ready == 1'b1 && (transfer_flag_i | exception_flag_i) == 1'b0 ? 1'b0 : 1'b1;
    //
    //
    //to if_id
    // assign inst      = pc[2] == 1'b1 ? iram_rdata[63:32] : iram_rdata[31: 0];
    assign inst = iram_rdata[31: 0];
    assign inst_addr = pc;
endmodule



module ysyx_210413_if_id (
    input wire                              clk,
    input wire                              rst,

    input wire                              stall_i,
    input wire                              flush_i,

    input wire [`RAM_ADDR_WIDTH - 1 : 0]    inst_addr_i,
    input wire [`INST_WIDTH - 1: 0]         inst_i,

    output reg [`RAM_ADDR_WIDTH - 1 : 0]    inst_addr_o,
    output reg [`INST_WIDTH - 1: 0]         inst_o
);

    always @(posedge clk) begin
        if(rst == 1'b1) begin
            inst_addr_o <= 0;
            inst_o      <= 0;
        end
        else begin
            if(stall_i == 1'b1) begin
                inst_addr_o <= inst_addr_o;
                inst_o      <= inst_o;
            end
            else if(flush_i == 1'b1) begin
                inst_addr_o <= 0;
                inst_o      <= 0;
            end
            else begin
                inst_addr_o <= inst_addr_i;
                inst_o      <= inst_i;
            end
        end
        
    end
endmodule


module ysyx_210413_id_stage(
    input wire                              rst,

    input wire                              timer_interrupt_flag_i,

    input wire [`RAM_ADDR_WIDTH - 1 : 0]    inst_addr_i,
    input wire [`INST_WIDTH - 1: 0]         inst_i,

    input wire [11: 0]                      exe_csr_w_addr_i,
    input wire [`REG_BUS]                   exe_csr_w_data_i,
    input wire                              exe_csr_w_ena_i,

    input wire [11: 0]                      mem_csr_w_addr_i,
    input wire [`REG_BUS]                   mem_csr_w_data_i,
    input wire                              mem_csr_w_ena_i,

    input wire [11: 0]                      wb_csr_w_addr_i,
    input wire [`REG_BUS]                   wb_csr_w_data_i,
    input wire                              wb_csr_w_ena_i,

    input wire [`REG_BUS]                   csr_r_data_i,

    output wire                             csr_r_ena_o,
    output wire [11: 0]                     csr_r_addr_o,

    input wire                              exe_mem_load_en_i,

    input wire                              exe_rd_w_ena_i,
    input wire [4 : 0]                      exe_rd_w_addr_i,
    input wire [`REG_BUS]                   exe_rd_w_data_i,

    input wire                              mem_rd_w_ena_i,
    input wire [4 : 0]                      mem_rd_w_addr_i,
    input wire [`REG_BUS]                   mem_rd_w_data_i,

    input wire                              wb_rd_w_ena_i,
    input wire [4 : 0]                      wb_rd_w_addr_i,
    input wire [`REG_BUS]                   wb_rd_w_data_i,

    input wire [`REG_BUS]                   rs1_r_data_i,
    input wire [`REG_BUS]                   rs2_r_data_i,
    
    output wire                             rs1_r_ena_o,
    output wire [4 : 0]                     rs1_r_addr_o,
    output wire                             rs2_r_ena_o,
    output wire [4 : 0]                     rs2_r_addr_o,


    output wire [`RAM_ADDR_WIDTH - 1 : 0]   inst_addr_o,
    output wire [`INST_WIDTH - 1: 0]        inst_o,

    output wire                             rd_w_ena_o,
    output wire [4 : 0]                     rd_w_addr_o,
    output wire                             csr_w_ena_o,
    output wire [11: 0]                     csr_w_addr_o,
    output wire [`REG_BUS]                  op1_o,
    output wire [`REG_BUS]                  op2_o,
    output wire [`REG_BUS]                  op3_o,
    
    output wire[`ALU_SEL_BUS]               alu_sel_o,
    output wire                             alu_sub_flag_o,
    output wire                             alu_word_flag_o,
    output wire                             alu_symbol_flag_o,

    output wire                             transfer_en_o,
    output wire[`TRANSFER_SEL_BUS]          transfer_sel_o,

    output wire                             mem_load_en_o,
    output wire                             mem_store_en_o,
    output wire[`MEM_SEL_BUS]               mem_sel_o,

    // output wire                             csr_en_o,
    output wire[`CSR_SEL_BUS]               csr_sel_o,

    output wire[`RD_SEL_BUS]                rd_sel_o,

    output wire [`REG_BUS]                  exception_type_o,

    output wire                             valid_o,
    output wire                             stall_flag_o
);


    assign inst_addr_o = inst_addr_i;
    assign inst_o      = inst_i;
    
    //exception
    wire exception_type_ecall_flag;
    wire exception_type_mret_flag;
    wire freeze_flag;

    wire [6  : 0]opcode;
    wire [4  : 0]rd;
    wire [2  : 0]funct3;
    wire [4  : 0]rs1;

    wire [4  : 0]rs2;
    // wire [6  : 0]funct7;

    // wire [5  : 0]shamt;

    wire [11: 0]csr_addr;

    assign opcode   = inst_i[6 : 0];
    assign rd       = inst_i[11: 7];
    assign funct3   = inst_i[14:12];
    assign rs1      = inst_i[19:15];

    assign rs2      = inst_i[24:20];
    // assign funct7   = inst_i[31:25];

    // assign shamt    = inst_i[25:20];

    assign csr_addr = inst_i[31:20];
    //imm
    wire [63: 0]imm_i;
    wire [63: 0]imm_s;
    wire [63: 0]imm_b;
    wire [63: 0]imm_u;
    wire [63: 0]imm_j;
    wire [63: 0]imm_csr;

    assign imm_i   = {{52{inst_i[31]}}, inst_i[31:20]};
    assign imm_s   = {{52{inst_i[31]}}, inst_i[31:25] , inst_i[11: 7]};
    assign imm_b   = {{52{inst_i[31]}}, inst_i[ 7], inst_i[30:25] , inst_i[11: 8], 1'b0};
    assign imm_u   = {{32{inst_i[31]}}, inst_i[31:12], 12'h0};
    assign imm_j   = {{43{inst_i[31]}}, inst_i[31], inst_i[19:12], inst_i[20], inst_i[30:21], 1'b0};
    assign imm_csr = {{59{1'b0}}, rs1};
    /**************************************************************************************************************
    ***************************************************************************************************************
        
    ***************************************************************************************************************
    ***************************************************************************************************************/
    // base U-type
    wire inst_lui   =   ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] &  opcode[2];
    wire inst_auipc =   ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] &  opcode[2];
    
    // base J-type(jump and link)
    wire inst_jal   =    opcode[6] &  opcode[5] & ~opcode[4] &  opcode[3] &  opcode[2];

    // base I-type(jump and link)
    wire inst_jalr  =    opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] &  opcode[2];

    // base B-type(branch)
    wire inst_beq   =    opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] & ~funct3[1] & ~funct3[0];
    wire inst_bne   =    opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] & ~funct3[1] &  funct3[0];
    wire inst_blt   =    opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] & ~funct3[1] & ~funct3[0];
    wire inst_bge   =    opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] & ~funct3[1] &  funct3[0];
    wire inst_bltu  =    opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] &  funct3[1] & ~funct3[0];
    wire inst_bgeu  =    opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] &  funct3[1] &  funct3[0];

    // base I-type(load)
    wire inst_lb    =   ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  opcode[1] &  opcode[0]
                      & ~funct3[2] & ~funct3[1] & ~funct3[0];
    wire inst_lh    =   ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] & ~funct3[1] &  funct3[0];
    wire inst_lw    =   ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] &  funct3[1] & ~funct3[0];
    wire inst_ld   =   ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] &  funct3[1] &  funct3[0];
    wire inst_lbu   =   ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] & ~funct3[1] & ~funct3[0];
    wire inst_lhu   =   ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] & ~funct3[1] &  funct3[0];
    wire inst_lwu   =   ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] &  funct3[1] & ~funct3[0];
    // base S-type(store)
    wire inst_sb    =   ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] & ~funct3[1] & ~funct3[0];
    wire inst_sh    =   ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] & ~funct3[1] &  funct3[0];
    wire inst_sw    =   ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] &  funct3[1] & ~funct3[0];
    wire inst_sd    =   ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] &  funct3[1] &  funct3[0];
    // base I-type
    wire inst_addi  =   ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] & ~funct3[1] & ~funct3[0];
    wire inst_slti  =   ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] &  funct3[1] & ~funct3[0];
    wire inst_sltiu =   ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] &  funct3[1] &  funct3[0]; 
    wire inst_xori  =   ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] & ~funct3[1] & ~funct3[0];
    wire inst_ori   =   ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] &  funct3[1] & ~funct3[0];
    wire inst_andi  =   ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] &  funct3[1] &  funct3[0];

    wire inst_slli  =   ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] & ~funct3[1] &  funct3[0];
    wire inst_srli  =   ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] & ~funct3[1] &  funct3[0]
                      & ~inst_i[30];
    wire inst_srai  =   ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] & ~funct3[1] &  funct3[0]
                      &  inst_i[30];
    wire inst_addiw =   ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2]
                      & ~funct3[2] & ~funct3[1] & ~funct3[0];
    wire inst_slliw =   ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2]
                      & ~funct3[2] & ~funct3[1] &  funct3[0]
                    //   & ~shamt[5];
                      & ~inst_i[25];
    wire inst_srliw =   ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2]
                      &  funct3[2] & ~funct3[1] &  funct3[0]
                      & ~inst_i[30]
                    //   & ~shamt[5];
                      & ~inst_i[25];
    wire inst_sraiw =   ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2]
                      &  funct3[2] & ~funct3[1] &  funct3[0]
                      &  inst_i[30]
                    //   & ~shamt[5];
                      & ~inst_i[25];

    wire inst_ecall =    opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] & ~funct3[1] & ~funct3[0]
                      & ~inst_i[31] & ~inst_i[30] & ~inst_i[29] & ~inst_i[28] & ~inst_i[27] & ~inst_i[26] & ~inst_i[25] & ~inst_i[24] & ~inst_i[23] & ~inst_i[22] & ~inst_i[21] & ~inst_i[20];
    wire inst_mret  =    opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] & ~funct3[1] & ~funct3[0]
                      & ~inst_i[31] & ~inst_i[30] &  inst_i[29] &  inst_i[28] & ~inst_i[27] & ~inst_i[26] & ~inst_i[25] & ~inst_i[24] & ~inst_i[23] & ~inst_i[22] &  inst_i[21] & ~inst_i[20];

    // base R-type
    wire inst_add   =   ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] & ~funct3[1] & ~funct3[0]
                    //   & ~funct7[5];
                      & ~inst_i[30];
    wire inst_sub   =   ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] & ~funct3[1] & ~funct3[0]
                    //   &  funct7[5];
                      &  inst_i[30];
    wire inst_sll   =   ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] & ~funct3[1] &  funct3[0];
    wire inst_slt   =   ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] &  funct3[1] & ~funct3[0];
    wire inst_sltu  =   ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] &  funct3[1] &  funct3[0];
    wire inst_xor   =   ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] & ~funct3[1] & ~funct3[0];
    wire inst_srl   =   ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] & ~funct3[1] &  funct3[0]
                    //   & ~funct7[5];
                      & ~inst_i[30];
    wire inst_sra   =   ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] & ~funct3[1] &  funct3[0]
                    //   &  funct7[5];
                      &  inst_i[30];
    wire inst_or    =   ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] &  funct3[1] & ~funct3[0];
    wire inst_and   =   ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] &  funct3[1] &  funct3[0];
    wire inst_addw  =   ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2]
                      & ~funct3[2] & ~funct3[1] & ~funct3[0]
                    //   & ~funct7[5];
                      & ~inst_i[30];
    wire inst_subw  =   ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2]
                      & ~funct3[2] & ~funct3[1] & ~funct3[0]
                    //   &  funct7[5];
                      &  inst_i[30];
    wire inst_sllw  =   ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2]
                      & ~funct3[2] & ~funct3[1] &  funct3[0];
    wire inst_srlw  =   ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2]
                      &  funct3[2] & ~funct3[1] &  funct3[0]
                    //   & ~funct7[5];
                      & ~inst_i[30];
    wire inst_sraw  =   ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2]
                      &  funct3[2] & ~funct3[1] &  funct3[0]
                    //   &  funct7[5];
                      &  inst_i[30];
    // zicsr
    wire inst_csrrw =    opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] & ~funct3[1] &  funct3[0];
    wire inst_csrrs =    opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] &  funct3[1] & ~funct3[0];
    wire inst_csrrc =    opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      & ~funct3[2] &  funct3[1] &  funct3[0];
    wire inst_csrrwi=    opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] & ~funct3[1] &  funct3[0];
    wire inst_csrrsi=    opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] &  funct3[1] & ~funct3[0];
    wire inst_csrrci=    opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2]
                      &  funct3[2] &  funct3[1] &  funct3[0];

    // wire inst_fence_i = ~opcode[6] & ~opcode[5] & ~opcode[4] &  opcode[3] &  opcode[2]
    //                   & ~funct3[2] & ~funct3[1] &  funct3[0];
    // for print
    wire inst_print = inst_i == 32'h7b;
    /**************************************************************************************************************
    ***************************************************************************************************************
        
    ***************************************************************************************************************
    ***************************************************************************************************************/
    assign valid_o =   rst == 1'b1 ? 1'b0 
                                   :  inst_lui
                                    | inst_auipc
                                    | inst_jal
                                    | inst_jalr
                                    | inst_beq
                                    | inst_bne
                                    | inst_blt
                                    | inst_bge
                                    | inst_bltu
                                    | inst_bgeu

                                    | inst_lb
                                    | inst_lh
                                    | inst_lw
                                    | inst_ld
                                    | inst_lbu
                                    | inst_lhu
                                    | inst_lwu
                                    | inst_sb
                                    | inst_sh
                                    | inst_sw
                                    | inst_sd

                                    | inst_addi
                                    | inst_slti
                                    | inst_sltiu
                                    | inst_xori
                                    | inst_ori
                                    | inst_andi
                                    | inst_slli
                                    | inst_srli
                                    | inst_srai
                                    | inst_addiw
                                    | inst_slliw
                                    | inst_srliw
                                    | inst_sraiw

                                    | inst_ecall
                                    | inst_mret
                                    | inst_csrrw
                                    | inst_csrrs
                                    | inst_csrrc
                                    | inst_csrrwi
                                    | inst_csrrsi
                                    | inst_csrrci

                                    | inst_add
                                    | inst_sub
                                    | inst_sll
                                    | inst_slt
                                    | inst_sltu
                                    | inst_xor
                                    | inst_srl
                                    | inst_sra
                                    | inst_or
                                    | inst_and
                                    | inst_addw
                                    | inst_subw
                                    | inst_sllw
                                    | inst_srlw
                                    | inst_sraw
                                    | inst_print;
    /**************************************************************************************************************
    ***************************************************************************************************************
        
    ***************************************************************************************************************
    ***************************************************************************************************************/
    wire inst_base_i;
    wire inst_base_r;
    wire inst_base_s;
    wire inst_base_b;
    wire inst_base_u;
    wire inst_base_j;
    wire inst_zicsr;
    wire inst_zicsr_r;
    wire inst_zicsr_i;
    // wire inst_ecall_and_pri;

    // assign inst_ecall_and_pri = inst_ecall | inst_mret;

    assign inst_zicsr_r = inst_csrrw  | inst_csrrs  | inst_csrrc;
    assign inst_zicsr_i = inst_csrrwi | inst_csrrsi | inst_csrrci;
    assign inst_zicsr        = inst_zicsr_r | inst_zicsr_i;

    //I-type 除ecall mret
    assign inst_base_i = ( rst == 1'b1 ) ? 0
                                         : (   inst_jalr
                                           |   inst_lb
                                           |   inst_lh
                                           |   inst_lw
                                           |   inst_ld
                                           |   inst_lbu
                                           |   inst_lhu
                                           |   inst_lwu
                                           |   inst_addi
                                           |   inst_slti
                                           |   inst_sltiu
                                           |   inst_xori
                                           |   inst_ori
                                           |   inst_andi
                                           |   inst_slli
                                           |   inst_srli
                                           |   inst_srai
                                           |   inst_addiw
                                           |   inst_slliw
                                           |   inst_srliw
                                           |   inst_sraiw );
    //R-type
    assign inst_base_r = ( rst == 1'b1 ) ? 0
                                         : (   inst_add
                                           |   inst_sub
                                           |   inst_sll
                                           |   inst_slt
                                           |   inst_sltu
                                           |   inst_xor
                                           |   inst_srl
                                           |   inst_sra
                                           |   inst_or
                                           |   inst_and
                                           |   inst_addw
                                           |   inst_subw
                                           |   inst_sllw
                                           |   inst_srlw
                                           |   inst_sraw );
    //S-type
    assign inst_base_s = ( rst == 1'b1 ) ? 0 : (inst_sb | inst_sh | inst_sw | inst_sd);
    //B-type
    assign inst_base_b = ( rst == 1'b1 ) ? 0 : (inst_beq | inst_bne | inst_blt | inst_bge | inst_bltu | inst_bgeu);
    //U-type
    assign inst_base_u = ( rst == 1'b1 ) ? 0 : (inst_lui | inst_auipc);
    //J-type
    assign inst_base_j = ( rst == 1'b1 ) ? 0 : inst_jal;



    // inst_base_i
    // inst_base_r
    // inst_base_s
    // inst_base_b
    // inst_base_u
    // inst_base_j
    // inst_zicsr
    // inst_ecall_and_pri
    assign rs1_r_ena_o  = (rst == 1'b1) ? 0 : (inst_base_i | inst_base_r | inst_base_s | inst_base_b | inst_zicsr);
    assign rs1_r_addr_o = (rst == 1'b1) ? 0 : rs1_r_ena_o == 1'b1 ? rs1 : 0;
    assign rs2_r_ena_o  = (rst == 1'b1) ? 0 : (inst_base_r | inst_base_s | inst_base_b);
    assign rs2_r_addr_o = (rst == 1'b1) ? 0 : rs2_r_ena_o == 1'b1 ? rs2 : 0;
    
    assign csr_r_ena_o  = (rst == 1'b1) ?  1'h0 : inst_zicsr;
    assign csr_r_addr_o = (rst == 1'b1) ? 12'h0 : (csr_r_ena_o == 1'b1) ? csr_addr : 12'h0;
    
    assign rd_w_ena_o   = (rst == 1'b1) ? 0 : (inst_base_i | inst_base_r | inst_base_u | inst_base_j | inst_zicsr);
    assign rd_w_addr_o  = (rst == 1'b1) ? 0 : rd_w_ena_o == 1'b1 ? rd  : 0;

    assign csr_w_ena_o  = (rst == 1'b1) ? 0 : inst_zicsr;
    assign csr_w_addr_o = (rst == 1'b1) ? 0 : csr_w_ena_o == 1'b1 ? csr_addr : 0;

    wire [`REG_BUS]   rs1_r_data_i_real;
    wire [`REG_BUS]   rs2_r_data_i_real;
    assign rs1_r_data_i_real = (rs1_r_addr_o   == 5'h0)                                    ? `ZERO_WORD      :
                               (exe_rd_w_ena_i == 1'b1 && exe_rd_w_addr_i == rs1_r_addr_o) ? exe_rd_w_data_i :
                               (mem_rd_w_ena_i == 1'b1 && mem_rd_w_addr_i == rs1_r_addr_o) ? mem_rd_w_data_i :
                               ( wb_rd_w_ena_i == 1'b1 &&  wb_rd_w_addr_i == rs1_r_addr_o) ? wb_rd_w_data_i  : rs1_r_data_i;
    assign rs2_r_data_i_real = (  rs2_r_addr_o == 5'h0)                                    ? `ZERO_WORD      :
                               (exe_rd_w_ena_i == 1'b1 && exe_rd_w_addr_i == rs2_r_addr_o) ? exe_rd_w_data_i :
                               (mem_rd_w_ena_i == 1'b1 && mem_rd_w_addr_i == rs2_r_addr_o) ? mem_rd_w_data_i :
                               ( wb_rd_w_ena_i == 1'b1 &&  wb_rd_w_addr_i == rs2_r_addr_o) ? wb_rd_w_data_i  : rs2_r_data_i;
    wire [`REG_BUS]   csr_r_data_i_real;
    assign csr_r_data_i_real = (exe_csr_w_ena_i == 1'b1 && exe_csr_w_addr_i == csr_r_addr_o) ? exe_csr_w_data_i :
                               (mem_csr_w_ena_i == 1'b1 && mem_csr_w_addr_i == csr_r_addr_o) ? mem_csr_w_data_i :
                               ( wb_csr_w_ena_i == 1'b1 &&  wb_csr_w_addr_i == csr_r_addr_o) ? wb_csr_w_data_i  : csr_r_data_i;

    assign op1_o = ( rst == 1'b1 ) ? 0 : (inst_auipc == 1'b1) ? {{64 - `RAM_ADDR_WIDTH{1'b0}}, inst_addr_i} :
                                         (inst_zicsr == 1'b1) ? csr_r_data_i_real :
                                         ((inst_base_i | inst_base_r | inst_base_s | inst_base_b) == 1'b1) ? rs1_r_data_i_real : 0;

    assign op2_o = ( rst == 1'b1 ) ? 0 : (inst_zicsr_r == 1'b1)                 ? rs1_r_data_i_real :
                                         (inst_zicsr_i == 1'b1)                 ? imm_csr :
                                         (inst_base_i  == 1'b1)                 ? imm_i : 
                                         ((inst_base_r | inst_base_b) == 1'b1)   ? rs2_r_data_i_real :
                                         (inst_base_s == 1'b1)                  ? imm_s :
                                         (inst_base_u == 1'b1)                  ? imm_u : 0;

    assign op3_o = ( rst == 1'b1 ) ? 0 : (inst_base_s == 1'b1) ? rs2_r_data_i_real :
                                         (inst_base_b == 1'b1) ? imm_b :
                                         (inst_base_j == 1'b1) ? imm_j : 0;

    /**************************************************************************************************************
    ***************************************************************************************************************
        ALU_SEL
    ***************************************************************************************************************
    ***************************************************************************************************************/

    // 不需要alu
    // inst_beq    
    // inst_bne    
    // inst_ecall  
    // inst_mret   
    // inst_csrrw  
    // inst_csrrwi 
    wire                alu_add_flag;
    wire                alu_slt_flag;
    wire                alu_or_flag;
    wire                alu_and_flag;
    wire                alu_xor_flag;
    wire                alu_sll_flag;
    wire                alu_srl_flag;
    wire                alu_sra_flag;

    assign alu_add_flag = inst_lui
                        | inst_auipc
                        | inst_jalr
                        | inst_lb
                        | inst_lh
                        | inst_lw
                        | inst_ld
                        | inst_lbu
                        | inst_lhu
                        | inst_lwu
                        | inst_sb
                        | inst_sh
                        | inst_sw
                        | inst_sd
                        | inst_add
                        | inst_addi
                        | inst_sub
                        | inst_addw
                        | inst_addiw
                        | inst_subw;

    assign alu_slt_flag = inst_blt
                        | inst_bge
                        | inst_bltu
                        | inst_bgeu
                        | inst_slt
                        | inst_slti
                        | inst_sltu
                        | inst_sltiu;

    assign alu_and_flag = inst_and
                        | inst_andi
                        | inst_csrrc
                        | inst_csrrci;

    assign alu_or_flag  = inst_or
                        | inst_ori
                        | inst_csrrs
                        | inst_csrrsi;

    assign alu_xor_flag = inst_xor
                        | inst_xori;

    assign alu_sll_flag = inst_sll
                        | inst_slli
                        | inst_sllw
                        | inst_slliw;

    assign alu_srl_flag = inst_srl
                        | inst_srli
                        | inst_srlw
                        | inst_srliw;

    assign alu_sra_flag = inst_sra
                        | inst_srai
                        | inst_sraw
                        | inst_sraiw;

    wire                alu_en;

    assign alu_sub_flag_o = inst_sub
                          | inst_subw
                          | alu_slt_flag;
    assign alu_word_flag_o = inst_addw
                           | inst_addiw
                           | inst_subw
                           | inst_sllw
                           | inst_slliw
                           | inst_srlw
                           | inst_srliw
                           | inst_sraw
                           | inst_sraiw;
    assign alu_symbol_flag_o = inst_slt | inst_slti | inst_blt | inst_bge;

    assign alu_en = alu_add_flag
                  | alu_slt_flag
                  | alu_or_flag 
                  | alu_and_flag
                  | alu_xor_flag
                  | alu_sll_flag
                  | alu_srl_flag
                  | alu_sra_flag;
    assign alu_sel_o = ( rst == 1'b1 ) ? 0 :  ( {`ALU_SEL_WIDTH{alu_add_flag}} & `ALU_SEL_ADD
                                              | {`ALU_SEL_WIDTH{alu_slt_flag}} & `ALU_SEL_SLT
                                              | {`ALU_SEL_WIDTH{alu_or_flag }} & `ALU_SEL_OR
                                              | {`ALU_SEL_WIDTH{alu_and_flag}} & `ALU_SEL_AND
                                              | {`ALU_SEL_WIDTH{alu_xor_flag}} & `ALU_SEL_XOR
                                              | {`ALU_SEL_WIDTH{alu_sll_flag}} & `ALU_SEL_SLL
                                              | {`ALU_SEL_WIDTH{alu_srl_flag}} & `ALU_SEL_SRL
                                              | {`ALU_SEL_WIDTH{alu_sra_flag}} & `ALU_SEL_SRA );

    /**************************************************************************************************************
    ***************************************************************************************************************
        TRANSFER_SEL
    ***************************************************************************************************************
    ***************************************************************************************************************/
    assign transfer_en_o = inst_jal | inst_jalr | inst_beq | inst_bne | inst_blt | inst_bge | inst_bltu| inst_bgeu;
    assign transfer_sel_o = ( rst == 1'b1 ) ? 0 : ( {`TRANSFER_SEL_WIDTH{inst_jal }} & `TRANSFER_JAL 
                                                  | {`TRANSFER_SEL_WIDTH{inst_jalr}} & `TRANSFER_JALR
                                                  | {`TRANSFER_SEL_WIDTH{inst_beq }} & `TRANSFER_BEQ 
                                                  | {`TRANSFER_SEL_WIDTH{inst_bne }} & `TRANSFER_BNE 
                                                  | {`TRANSFER_SEL_WIDTH{inst_blt }} & `TRANSFER_BLT 
                                                  | {`TRANSFER_SEL_WIDTH{inst_bge }} & `TRANSFER_BGE 
                                                  | {`TRANSFER_SEL_WIDTH{inst_bltu}} & `TRANSFER_BLTU
                                                  | {`TRANSFER_SEL_WIDTH{inst_bgeu}} & `TRANSFER_BGEU );

    /**************************************************************************************************************
    ***************************************************************************************************************
        MEM_SEL
    ***************************************************************************************************************
    ***************************************************************************************************************/

    assign mem_load_en_o = inst_lb | inst_lh | inst_lw | inst_ld | inst_lbu | inst_lhu | inst_lwu;
    assign mem_store_en_o = inst_sb | inst_sh | inst_sw | inst_sd;
    assign mem_sel_o    = ( rst == 1'b1 ) ? 0 :  ( {`MEM_SEL_WIDTH{inst_lb }} & `MEM_LB
                                                 | {`MEM_SEL_WIDTH{inst_lh }} & `MEM_LH
                                                 | {`MEM_SEL_WIDTH{inst_lw }} & `MEM_LW
                                                 | {`MEM_SEL_WIDTH{inst_ld }} & `MEM_LD
                                                 | {`MEM_SEL_WIDTH{inst_lbu}} & `MEM_LBU
                                                 | {`MEM_SEL_WIDTH{inst_lhu}} & `MEM_LHU
                                                 | {`MEM_SEL_WIDTH{inst_lwu}} & `MEM_LWU
                                                 | {`MEM_SEL_WIDTH{inst_sb }} & `MEM_SB
                                                 | {`MEM_SEL_WIDTH{inst_sh }} & `MEM_SH
                                                 | {`MEM_SEL_WIDTH{inst_sw }} & `MEM_SW
                                                 | {`MEM_SEL_WIDTH{inst_sd }} & `MEM_SD );
    /**************************************************************************************************************
    ***************************************************************************************************************
        CSR_SEL
    ***************************************************************************************************************
    ***************************************************************************************************************/
    // assign csr_en_o  = inst_zicsr;
    assign csr_sel_o = ( rst == 1'b1 ) ? 0 :  ( {`CSR_SEL_WIDTH{inst_csrrw | inst_csrrwi}} & `CSR_CSRRW
                                            | {`CSR_SEL_WIDTH{inst_csrrs | inst_csrrsi}} & `CSR_CSRRS
                                            | {`CSR_SEL_WIDTH{inst_csrrc | inst_csrrci}} & `CSR_CSRRC );
    /**************************************************************************************************************
    ***************************************************************************************************************
        rd_sel
    ***************************************************************************************************************
    ***************************************************************************************************************/    
    assign rd_sel_o = ( rst == 1'b1 ) ? 0 :( {`RD_SEL_WIDTH{alu_en              }} & `RD_SEL_ALU 
                                           | {`RD_SEL_WIDTH{inst_jal | inst_jalr}} & `RD_SEL_LINK
                                           | {`RD_SEL_WIDTH{inst_zicsr          }} & `RD_SEL_CSR 
                                           | {`RD_SEL_WIDTH{mem_load_en_o       }} & `RD_SEL_LOAD );
    /**************************************************************************************************************
    ***************************************************************************************************************
        load相关
    ***************************************************************************************************************
    ***************************************************************************************************************/
    wire pre_inst_is_load;
    
    wire stall_flag_for_reg1_loadrelate;
    wire stall_flag_for_reg2_loadrelate;
    
    assign pre_inst_is_load = (exe_mem_load_en_i == 1'b1) ? 1'b1 : 1'b0;  
    assign stall_flag_for_reg1_loadrelate = (rs1_r_ena_o == 1'h1) && (pre_inst_is_load == 1'b1) && (exe_rd_w_addr_i == rs1_r_addr_o) ? 1'h1 : 1'h0;
    assign stall_flag_for_reg2_loadrelate = (rs2_r_ena_o == 1'h1) && (pre_inst_is_load == 1'b1) && (exe_rd_w_addr_i == rs2_r_addr_o) ? 1'h1 : 1'h0;

    assign stall_flag_o = freeze_flag == 1'b1 ? 1'b0 : stall_flag_for_reg1_loadrelate | stall_flag_for_reg2_loadrelate;
    /**************************************************************************************************************
    ***************************************************************************************************************
        exception
    ***************************************************************************************************************
    ***************************************************************************************************************/
    //exception flag

    assign exception_type_ecall_flag = inst_ecall;
    assign exception_type_mret_flag  = inst_mret;
    //[ 5]   : ecall
    //[32]   : mret
    //[39]   : timer_interrupt
    assign exception_type_o = valid_o == 1'b1 ? {24'h0, timer_interrupt_flag_i, 6'b0, exception_type_mret_flag, 26'h0, exception_type_ecall_flag, 5'h0} : `ZERO_WORD;


    assign freeze_flag = exception_type_o == `ZERO_WORD ? 1'b0 : 1'b1;
endmodule


module ysyx_210413_id_exe (
    input wire                              clk,
    input wire                              rst,

    input wire                              stall_i,
    input wire                              flush_i,

    input wire [`RAM_ADDR_WIDTH - 1 : 0]    inst_addr_i,
    input wire [`INST_WIDTH - 1: 0]         inst_i,

    input wire                              rd_w_ena_i,
    input wire [4 : 0]                      rd_w_addr_i,
    input wire                              csr_w_ena_i,
    input wire [11: 0]                      csr_w_addr_i,
    input wire [`REG_BUS]                   op1_i,
    input wire [`REG_BUS]                   op2_i,
    input wire [`REG_BUS]                   op3_i,

    input wire[`ALU_SEL_BUS]                alu_sel_i,
    input wire                              alu_sub_flag_i,
    input wire                              alu_word_flag_i,
    input wire                              alu_symbol_flag_i,

    input wire                              transfer_en_i,
    input wire[`TRANSFER_SEL_BUS]           transfer_sel_i,

    input wire                              mem_load_en_i,
    input wire                              mem_store_en_i,
    input wire[`MEM_SEL_BUS]                mem_sel_i,

    // input wire                              csr_en_i,
    input wire[`CSR_SEL_BUS]                csr_sel_i,

    input wire[`RD_SEL_BUS]                 rd_sel_i,

    input wire [`REG_BUS]                   exception_type_i,
    input wire                              valid_i,

    output reg [`RAM_ADDR_WIDTH - 1 : 0]    inst_addr_o,
    output reg [`INST_WIDTH - 1: 0]         inst_o,

    output reg                              rd_w_ena_o,
    output reg [4 : 0]                      rd_w_addr_o,
    output reg                              csr_w_ena_o,
    output reg [11: 0]                      csr_w_addr_o,
    output reg [`REG_BUS]                   op1_o,
    output reg [`REG_BUS]                   op2_o,
    output reg [`REG_BUS]                   op3_o,

    output reg [`ALU_SEL_BUS]               alu_sel_o,
    output reg                              alu_sub_flag_o,
    output reg                              alu_word_flag_o,
    output reg                              alu_symbol_flag_o,

    output reg                              transfer_en_o,
    output reg [`TRANSFER_SEL_BUS]          transfer_sel_o,

    output reg                              mem_load_en_o,
    output reg                              mem_store_en_o,
    output reg [`MEM_SEL_BUS]               mem_sel_o,

    // output reg                              csr_en_o,
    output reg [`CSR_SEL_BUS]               csr_sel_o,

    output reg [`RD_SEL_BUS]                rd_sel_o,

    output reg [`REG_BUS]                   exception_type_o,
    output reg                              valid_o
);
    always @(posedge clk) begin
        if(rst == 1'b1) begin
            inst_addr_o         <= 0;
            inst_o              <= 0;

            rd_w_ena_o          <= 1'b0;
            rd_w_addr_o         <= 5'h0;
            csr_w_ena_o         <= 1'b0;
            csr_w_addr_o        <= 12'h0;
            op1_o               <= `ZERO_WORD;
            op2_o               <= `ZERO_WORD;
            op3_o               <= `ZERO_WORD;

            alu_sel_o           <= 0;
            alu_sub_flag_o      <= 0;
            alu_word_flag_o     <= 0;
            alu_symbol_flag_o   <= 0;

            transfer_en_o       <= 0;
            transfer_sel_o      <= 0;

            mem_load_en_o       <= 0;
            mem_store_en_o      <= 0;
            mem_sel_o           <= 0;

            // csr_en_o            <= 0;
            csr_sel_o           <= 0;

            rd_sel_o            <= 0;

            exception_type_o    <= `ZERO_WORD;
            valid_o             <= 1'b0;
        end
        else begin
            if(stall_i == 1'b1) begin
                inst_addr_o         <= inst_addr_o;
                inst_o              <= inst_o;

                inst_addr_o         <= inst_addr_o;

                rd_w_ena_o          <= rd_w_ena_o;
                rd_w_addr_o         <= rd_w_addr_o;
                csr_w_ena_o         <= csr_w_ena_o;
                csr_w_addr_o        <= csr_w_addr_o;
                op1_o               <= op1_o;
                op2_o               <= op2_o;
                op3_o               <= op3_o;

                alu_sel_o           <= alu_sel_o;
                alu_sub_flag_o      <= alu_sub_flag_o;
                alu_word_flag_o     <= alu_word_flag_o;
                alu_symbol_flag_o   <= alu_symbol_flag_o;

                transfer_en_o       <= transfer_en_o;
                transfer_sel_o      <= transfer_sel_o;

                mem_load_en_o       <= mem_load_en_o;
                mem_store_en_o      <= mem_store_en_o;
                mem_sel_o           <= mem_sel_o;

                // csr_en_o            <= csr_en_o;
                csr_sel_o           <= csr_sel_o;

                rd_sel_o            <= rd_sel_o;

                exception_type_o    <= exception_type_o;
                valid_o             <= valid_o;
            end
            else if(flush_i == 1'b1) begin
                inst_addr_o         <= 0;
                inst_o              <= 0;

                rd_w_ena_o          <= 1'b0;
                rd_w_addr_o         <= 5'h0;
                csr_w_ena_o         <= 1'b0;
                csr_w_addr_o        <= 12'h0;
                op1_o               <= `ZERO_WORD;
                op2_o               <= `ZERO_WORD;
                op3_o               <= `ZERO_WORD;

                alu_sel_o           <= 0;
                alu_sub_flag_o      <= 0;
                alu_word_flag_o     <= 0;
                alu_symbol_flag_o   <= 0;

                transfer_en_o       <= 0;
                transfer_sel_o      <= 0;

                mem_load_en_o       <= 0;
                mem_store_en_o      <= 0;
                mem_sel_o           <= 0;

                // csr_en_o            <= 0;
                csr_sel_o           <= 0;

                rd_sel_o            <= 0;

                exception_type_o    <= `ZERO_WORD;
                valid_o             <= 1'b0;
            end 
            else begin
                inst_addr_o         <= inst_addr_i;
                inst_o              <= inst_i;

                inst_addr_o         <= inst_addr_i;

                rd_w_ena_o          <= rd_w_ena_i;
                rd_w_addr_o         <= rd_w_addr_i;
                csr_w_ena_o         <= csr_w_ena_i;
                csr_w_addr_o        <= csr_w_addr_i;
                op1_o               <= op1_i;
                op2_o               <= op2_i;
                op3_o               <= op3_i;

                alu_sel_o           <= alu_sel_i;
                alu_sub_flag_o      <= alu_sub_flag_i;
                alu_word_flag_o     <= alu_word_flag_i;
                alu_symbol_flag_o   <= alu_symbol_flag_i;

                transfer_en_o       <= transfer_en_i;
                transfer_sel_o      <= transfer_sel_i;

                mem_load_en_o       <= mem_load_en_i;
                mem_store_en_o      <= mem_store_en_i;
                mem_sel_o           <= mem_sel_i;

                // csr_en_o            <= csr_en_i;
                csr_sel_o           <= csr_sel_i;

                rd_sel_o            <= rd_sel_i;

                exception_type_o    <= exception_type_i;
                valid_o             <= valid_i;
            end
        end 
    end
endmodule


module ysyx_210413_exe_stage(
    input wire                              rst,

    input wire [`RAM_ADDR_WIDTH - 1 : 0]    inst_addr_i,
    input wire [`INST_WIDTH - 1: 0]         inst_i,

    input wire                              rd_w_ena_i,
    input wire [4 : 0]                      rd_w_addr_i,
    input wire                              csr_w_ena_i,
    input wire [11: 0]                      csr_w_addr_i,    
    input wire [`REG_BUS]                   op1_i,
    input wire [`REG_BUS]                   op2_i,
    input wire [`REG_BUS]                   op3_i,
    
    input wire[`ALU_SEL_BUS]                alu_sel_i,
    input wire                              alu_sub_flag_i,
    input wire                              alu_word_flag_i,
    input wire                              alu_symbol_flag_i,

    input wire                              transfer_en_i,
    input wire[`TRANSFER_SEL_BUS]           transfer_sel_i,

    // input wire                              csr_en_i,
    input wire[`CSR_SEL_BUS]                csr_sel_i,

    input wire                              mem_load_en_i,
    input wire                              mem_store_en_i,
    input wire[`MEM_SEL_BUS]                mem_sel_i,

    input wire[`RD_SEL_BUS]                 rd_sel_i,

    input wire [`REG_BUS]                   exception_type_from_wb_i,
    input wire [`REG_BUS]                   exception_type_from_mem_i,
    input wire [`REG_BUS]                   exception_type_i,
    input wire                              valid_i,

    output wire [`RAM_ADDR_WIDTH - 1 : 0]   inst_addr_o,
    output wire [`INST_WIDTH - 1: 0]        inst_o,

    output wire                             rd_w_ena_o,
    output wire [4 : 0]                     rd_w_addr_o,
    output wire [`REG_BUS]                  rd_w_data_o,

    output wire                             csr_w_ena_o,
    output wire [11: 0]                     csr_w_addr_o,
    output wire [`REG_BUS]                  csr_w_data_o,

    output wire [`RAM_ADDR_WIDTH - 1 : 0]   mem_addr_o,
    output wire [`RAM_DATA_WIDTH - 1: 0]    mem_w_data_o,
    
    output wire                             transfer_flag_o,
    output wire [`RAM_ADDR_WIDTH - 1 : 0]   transfer_addr_o,

    output wire                             mem_load_en_o,
    output wire                             mem_store_en_o,
    output wire[`MEM_SEL_BUS]               mem_sel_o,

    output wire [`REG_BUS]                  exception_type_o,
    output wire                             valid_o
);
    assign inst_addr_o   = inst_addr_i;
    assign inst_o        = inst_i;

    assign rd_w_ena_o  = (rst == 1'h0) ? rd_w_ena_i : 1'b0;
    assign rd_w_addr_o  = rd_w_addr_i;

    assign csr_w_ena_o = csr_w_ena_i;
    assign csr_w_addr_o = csr_w_addr_i;

    assign mem_load_en_o  = mem_load_en_i;
    assign mem_store_en_o = mem_store_en_i;
    assign mem_sel_o      = mem_sel_i;

    assign exception_type_o = exception_type_i;
    assign valid_o = valid_i;

    //exception
    wire freeze_flag;
    assign freeze_flag = exception_type_o == `ZERO_WORD && exception_type_from_mem_i == `ZERO_WORD && exception_type_from_wb_i == `ZERO_WORD ? 1'b0 : 1'b1;
    //ALU
    /**********************************
    *logic
    ***********************************/
    wire[`REG_BUS] logic_or_result;
    wire[`REG_BUS] logic_and_result;
    wire[`REG_BUS] logic_xor_result;

    assign logic_or_result  = op1_i | op2_i;
    assign logic_and_result = op1_i & op2_i;
    assign logic_xor_result = op1_i ^ op2_i;

    /**********************************
    *shift
    ***********************************/

    wire[`REG_BUS] shift_sll_dw_result;
    wire[`REG_BUS] shift_srl_dw_result;
    wire[`REG_BUS] shift_sra_dw_result;
    
    wire [`REG_BUS]shift_dw_src;
    wire [`REG_BUS]shift_dw_result_pre;
    wire [`REG_BUS]shift_dw_mask;

    wire[`REG_BUS] shift_sll_w_result;
    wire[`REG_BUS] shift_srl_w_result;
    wire[`REG_BUS] shift_sra_w_result;
    wire[31: 0] shift_sra_w_result_pre;

    wire [31: 0]shift_w_src;
    wire [31: 0]shift_w_result_pre;
    wire [31: 0]shift_w_mask;
    
    wire[`REG_BUS] shift_sll_result;
    wire[`REG_BUS] shift_srl_result;
    wire[`REG_BUS] shift_sra_result;

    assign shift_dw_src = (alu_sel_i == `ALU_SEL_SLL) ? {
                                                            op1_i[ 0], op1_i[ 1], op1_i[ 2], op1_i[ 3], op1_i[ 4], op1_i[ 5], op1_i[ 6], op1_i[ 7], 
                                                            op1_i[ 8], op1_i[ 9], op1_i[10], op1_i[11], op1_i[12], op1_i[13], op1_i[14], op1_i[15], 
                                                            op1_i[16], op1_i[17], op1_i[18], op1_i[19], op1_i[20], op1_i[21], op1_i[22], op1_i[23], 
                                                            op1_i[24], op1_i[25], op1_i[26], op1_i[27], op1_i[28], op1_i[29], op1_i[30], op1_i[31], 
                                                            op1_i[32], op1_i[33], op1_i[34], op1_i[35], op1_i[36], op1_i[37], op1_i[38], op1_i[39], 
                                                            op1_i[40], op1_i[41], op1_i[42], op1_i[43], op1_i[44], op1_i[45], op1_i[46], op1_i[47], 
                                                            op1_i[48], op1_i[49], op1_i[50], op1_i[51], op1_i[52], op1_i[53], op1_i[54], op1_i[55], 
                                                            op1_i[56], op1_i[57], op1_i[58], op1_i[59], op1_i[60], op1_i[61], op1_i[62], op1_i[63]
                                                        }
                                                      : op1_i;
    assign shift_dw_result_pre = shift_dw_src >> op2_i[5:0];
    assign shift_dw_mask = ~(64'hffffffff_ffffffff >> op2_i[5:0]);
    assign shift_sll_dw_result = {
                                    shift_dw_result_pre[ 0], shift_dw_result_pre[ 1], shift_dw_result_pre[ 2], shift_dw_result_pre[ 3], shift_dw_result_pre[ 4], shift_dw_result_pre[ 5], shift_dw_result_pre[ 6], shift_dw_result_pre[ 7], 
                                    shift_dw_result_pre[ 8], shift_dw_result_pre[ 9], shift_dw_result_pre[10], shift_dw_result_pre[11], shift_dw_result_pre[12], shift_dw_result_pre[13], shift_dw_result_pre[14], shift_dw_result_pre[15], 
                                    shift_dw_result_pre[16], shift_dw_result_pre[17], shift_dw_result_pre[18], shift_dw_result_pre[19], shift_dw_result_pre[20], shift_dw_result_pre[21], shift_dw_result_pre[22], shift_dw_result_pre[23], 
                                    shift_dw_result_pre[24], shift_dw_result_pre[25], shift_dw_result_pre[26], shift_dw_result_pre[27], shift_dw_result_pre[28], shift_dw_result_pre[29], shift_dw_result_pre[30], shift_dw_result_pre[31], 
                                    shift_dw_result_pre[32], shift_dw_result_pre[33], shift_dw_result_pre[34], shift_dw_result_pre[35], shift_dw_result_pre[36], shift_dw_result_pre[37], shift_dw_result_pre[38], shift_dw_result_pre[39], 
                                    shift_dw_result_pre[40], shift_dw_result_pre[41], shift_dw_result_pre[42], shift_dw_result_pre[43], shift_dw_result_pre[44], shift_dw_result_pre[45], shift_dw_result_pre[46], shift_dw_result_pre[47], 
                                    shift_dw_result_pre[48], shift_dw_result_pre[49], shift_dw_result_pre[50], shift_dw_result_pre[51], shift_dw_result_pre[52], shift_dw_result_pre[53], shift_dw_result_pre[54], shift_dw_result_pre[55], 
                                    shift_dw_result_pre[56], shift_dw_result_pre[57], shift_dw_result_pre[58], shift_dw_result_pre[59], shift_dw_result_pre[60], shift_dw_result_pre[61], shift_dw_result_pre[62], shift_dw_result_pre[63]
                                };
                                                           
    assign shift_srl_dw_result = shift_dw_result_pre;
    assign shift_sra_dw_result = ({64{op1_i[63]}} & shift_dw_mask | shift_dw_result_pre);

    assign shift_w_src = (alu_sel_i == `ALU_SEL_SLL) ? {
                                                            op1_i[ 0], op1_i[ 1], op1_i[ 2], op1_i[ 3], op1_i[ 4], op1_i[ 5], op1_i[ 6], op1_i[ 7], 
                                                            op1_i[ 8], op1_i[ 9], op1_i[10], op1_i[11], op1_i[12], op1_i[13], op1_i[14], op1_i[15], 
                                                            op1_i[16], op1_i[17], op1_i[18], op1_i[19], op1_i[20], op1_i[21], op1_i[22], op1_i[23], 
                                                            op1_i[24], op1_i[25], op1_i[26], op1_i[27], op1_i[28], op1_i[29], op1_i[30], op1_i[31]
                                                       }
                                                       : op1_i[31: 0];
    assign shift_w_result_pre = shift_w_src >> op2_i[4:0];
    assign shift_w_mask = ~(32'hffffffff >> op2_i[4:0]);
    assign shift_sll_w_result = {
                                    {32{shift_w_result_pre[ 0]}},
                                    shift_w_result_pre[ 0], shift_w_result_pre[ 1], shift_w_result_pre[ 2], shift_w_result_pre[ 3], shift_w_result_pre[ 4], shift_w_result_pre[ 5], shift_w_result_pre[ 6], shift_w_result_pre[ 7], 
                                    shift_w_result_pre[ 8], shift_w_result_pre[ 9], shift_w_result_pre[10], shift_w_result_pre[11], shift_w_result_pre[12], shift_w_result_pre[13], shift_w_result_pre[14], shift_w_result_pre[15], 
                                    shift_w_result_pre[16], shift_w_result_pre[17], shift_w_result_pre[18], shift_w_result_pre[19], shift_w_result_pre[20], shift_w_result_pre[21], shift_w_result_pre[22], shift_w_result_pre[23], 
                                    shift_w_result_pre[24], shift_w_result_pre[25], shift_w_result_pre[26], shift_w_result_pre[27], shift_w_result_pre[28], shift_w_result_pre[29], shift_w_result_pre[30], shift_w_result_pre[31]
                                };
    assign shift_srl_w_result = {{32{shift_w_result_pre[31]}}, shift_w_result_pre};
    assign shift_sra_w_result_pre = ({32{op1_i[31]}} & shift_w_mask | shift_w_result_pre);
    assign shift_sra_w_result = {{32{shift_sra_w_result_pre[31]}}, shift_sra_w_result_pre};

    assign shift_sll_result = alu_word_flag_i == 1'b1 ? shift_sll_w_result : shift_sll_dw_result;
    assign shift_srl_result = alu_word_flag_i == 1'b1 ? shift_srl_w_result : shift_srl_dw_result;
    assign shift_sra_result = alu_word_flag_i == 1'b1 ? shift_sra_w_result : shift_sra_dw_result;
    /****************************
    *add
    *****************************/
    wire[`REG_BUS] operand2_i_mux;
    wire[`REG_BUS] result_sum;
    // wire           overflow_sum;

    wire operand1_lt_operand2;

    wire[`REG_BUS] arithmetic_slt_result;
    wire[`REG_BUS] arithmetic_add_result;

    assign operand2_i_mux       = alu_sub_flag_i == 1'b1 ? (~op2_i) + 1 : op2_i; 
    assign result_sum           = op1_i + operand2_i_mux;
    // assign overflow_sum         = ((~op1_i[31] & ~operand2_i_mux[31]) &   result_sum[31]) |
    //                               (( op1_i[31] &  operand2_i_mux[31]) & (~result_sum[31]));
    //如果是有符号数则特殊
    //如果是无符号数或者符号相同则直接比较
    assign operand1_lt_operand2 = alu_symbol_flag_i ? ( ( op1_i[63] & ~op2_i[63])
                                                    | (~op1_i[63] & ~op2_i[63] & result_sum[63])
                                                    | ( op1_i[63] &  op2_i[63] & result_sum[63])
                                                    ) 
                                                  : (op1_i < op2_i);

    assign arithmetic_slt_result = {63'h0, operand1_lt_operand2};

    assign arithmetic_add_result = alu_word_flag_i == 1'b1 ? {{32{result_sum[31]}}, result_sum[31: 0]} : result_sum;

    reg[`REG_BUS] alu_result;
    always @(*) begin
        case(alu_sel_i)
            `ALU_SEL_OR:  begin
                alu_result = logic_or_result;
            end
            `ALU_SEL_AND: begin
                alu_result = logic_and_result;
            end
            `ALU_SEL_XOR: begin
                alu_result = logic_xor_result;
            end
            `ALU_SEL_SLL: begin
                alu_result = shift_sll_result;
            end
            `ALU_SEL_SRL: begin
                alu_result = shift_srl_result;
            end
            `ALU_SEL_SRA: begin
                alu_result = shift_sra_result;
            end
            `ALU_SEL_SLT: begin
                alu_result = arithmetic_slt_result;
            end
            `ALU_SEL_ADD: begin
                alu_result = arithmetic_add_result;
            end
            `ALU_SEL_SUB: begin
                alu_result = arithmetic_add_result;
            end
            default: begin
                alu_result = `ZERO_WORD;
            end
        endcase
    end
    /**********************************
    *加载存储指令
    ***********************************/
    
    assign mem_addr_o = result_sum[`RAM_ADDR_WIDTH - 1 : 0];

    assign mem_w_data_o = op3_i;

    /**********************************
    *转移指令
    ***********************************/
    
    //branch
    
    wire[`RAM_ADDR_WIDTH - 1 : 0] branch_address;

    assign branch_address = inst_addr_i + op3_i[`RAM_ADDR_WIDTH - 1 : 0];

    wire inst_beq_flag ;
    wire inst_bne_flag ;
    wire inst_blt_flag ;
    wire inst_bge_flag ;
    wire inst_bltu_flag;
    wire inst_bgeu_flag;

    assign inst_beq_flag  = (transfer_en_i == 1'b1) && (transfer_sel_i == `TRANSFER_BEQ ) ? 1'h1 : 1'h0;
    assign inst_bne_flag  = (transfer_en_i == 1'b1) && (transfer_sel_i == `TRANSFER_BNE ) ? 1'h1 : 1'h0;
    assign inst_blt_flag  = (transfer_en_i == 1'b1) && (transfer_sel_i == `TRANSFER_BLT ) ? 1'h1 : 1'h0;
    assign inst_bge_flag  = (transfer_en_i == 1'b1) && (transfer_sel_i == `TRANSFER_BGE ) ? 1'h1 : 1'h0;
    assign inst_bltu_flag = (transfer_en_i == 1'b1) && (transfer_sel_i == `TRANSFER_BLTU) ? 1'h1 : 1'h0;
    assign inst_bgeu_flag = (transfer_en_i == 1'b1) && (transfer_sel_i == `TRANSFER_BGEU) ? 1'h1 : 1'h0;
    
    //jump and link
    wire inst_jal_flag;
    wire inst_jalr_flag;
    wire[`RAM_ADDR_WIDTH - 1 : 0] pc_plus_4;

    assign pc_plus_4 = inst_addr_i + 4;

    assign inst_jal_flag  = (transfer_en_i == 1'b1) && (transfer_sel_i == `TRANSFER_JAL ) ? 1'h1 : 1'h0;
    assign inst_jalr_flag = (transfer_en_i == 1'b1) && (transfer_sel_i == `TRANSFER_JALR) ? 1'h1 : 1'h0;
    
    wire[`REG_BUS] link_result;
    assign link_result = inst_jal_flag | inst_jalr_flag ? {{64 - `RAM_ADDR_WIDTH{1'b0}}, pc_plus_4} : 0;

    assign transfer_flag_o = rst         ? 1'b0 :
                             freeze_flag ? 1'b0 : (  inst_jal_flag
                                                  || inst_jalr_flag
                                                  || inst_beq_flag  && (op1_i == op2_i)              
                                                  || inst_bne_flag  && (op1_i != op2_i)              
                                                  || inst_blt_flag  && (operand1_lt_operand2 == 1'h1)
                                                  || inst_bge_flag  && (operand1_lt_operand2 == 1'h0)
                                                  || inst_bltu_flag && (operand1_lt_operand2 == 1'h1)
                                                  || inst_bgeu_flag && (operand1_lt_operand2 == 1'h0) );

    assign transfer_addr_o = (inst_jalr_flag  == 1'b1) ? result_sum[`RAM_ADDR_WIDTH - 1 : 0]:
                                (transfer_flag_o == 1'b1) ? branch_address : 0;
    /**********************************
    *CSR
    ***********************************/
    wire [`REG_BUS] csr_result;
    assign csr_result = op1_i;
    assign csr_w_data_o = (csr_sel_i == `CSR_CSRRW) ? op2_i          :
                          (csr_sel_i == `CSR_CSRRS) ? op1_i | op2_i  :
                          (csr_sel_i == `CSR_CSRRC) ? op1_i & ~op2_i : `ZERO_WORD;

/////////////////////////////////////////////////////////////////////////////
    assign rd_w_data_o  = rd_sel_i == `RD_SEL_ALU  ? alu_result :
                          rd_sel_i == `RD_SEL_LINK ? link_result:
                          rd_sel_i == `RD_SEL_CSR  ? csr_result : 0;

endmodule


module ysyx_210413_exe_mem (
    input wire                              clk,
    input wire                              rst,
    
    input wire                              stall_i,
    input wire                              flush_i,

    input wire [`RAM_ADDR_WIDTH - 1 : 0]    inst_addr_i,
    input wire [`INST_WIDTH - 1: 0]         inst_i,

    input wire                              rd_w_ena_i,
    input wire [4 : 0]                      rd_w_addr_i,
    input wire [`REG_BUS]                   rd_w_data_i,

    input wire                              csr_w_ena_i,
    input wire [11: 0]                      csr_w_addr_i,
    input wire [`REG_BUS]                   csr_w_data_i,

    input wire [`RAM_ADDR_WIDTH - 1 : 0]    mem_addr_i,
    input wire [`RAM_DATA_WIDTH - 1: 0]     mem_w_data_i,

    input wire                              mem_load_en_i,
    input wire                              mem_store_en_i,
    input wire[`MEM_SEL_BUS]                mem_sel_i,

    input wire [`REG_BUS]                   exception_type_i,
    input wire                              valid_i,

    output reg [`RAM_ADDR_WIDTH - 1 : 0]    inst_addr_o,
    output reg [`INST_WIDTH - 1: 0]         inst_o,

    output reg                              rd_w_ena_o,
    output reg [4 : 0]                      rd_w_addr_o,
    output reg [`REG_BUS]                   rd_w_data_o,

    output reg                              csr_w_ena_o,
    output reg [11: 0]                      csr_w_addr_o,
    output reg [`REG_BUS]                   csr_w_data_o,

    output reg [`RAM_ADDR_WIDTH - 1 : 0]    mem_addr_o,
    output reg [`RAM_DATA_WIDTH - 1: 0]     mem_w_data_o,

    output reg                              mem_load_en_o,
    output reg                              mem_store_en_o,
    output reg [`MEM_SEL_BUS]               mem_sel_o,

    output reg [`REG_BUS]                   exception_type_o,
    output reg                              valid_o
);
    always @(posedge clk) begin
        if(rst == 1'b1) begin
            inst_addr_o         <= 0;
            inst_o              <= 0;

            rd_w_ena_o          <= 1'b0;
            rd_w_addr_o         <= 5'h0;
            rd_w_data_o         <= 64'h0;

            csr_w_ena_o         <= 1'b0;
            csr_w_addr_o        <= 12'h0;
            csr_w_data_o        <= 64'h0;

            mem_addr_o          <= 0;
            mem_w_data_o        <= 0;

            mem_load_en_o       <= 0;
            mem_store_en_o      <= 0;
            mem_sel_o           <= 0;

            exception_type_o    <= `ZERO_WORD;
            valid_o             <= 1'b0;
        end
        else begin
            if(stall_i == 1'b1) begin
                inst_addr_o         <= inst_addr_o;
                inst_o              <= inst_o;

                rd_w_ena_o          <= rd_w_ena_o;
                rd_w_addr_o         <= rd_w_addr_o;
                rd_w_data_o         <= rd_w_data_o;

                csr_w_ena_o         <= csr_w_ena_o;
                csr_w_addr_o        <= csr_w_addr_o;
                csr_w_data_o        <= csr_w_data_o;

                mem_addr_o          <= mem_addr_o;
                mem_w_data_o        <= mem_w_data_o;
                
                mem_load_en_o       <= mem_load_en_o;
                mem_store_en_o      <= mem_store_en_o;
                mem_sel_o           <= mem_sel_o;

                exception_type_o    <= exception_type_o;
                valid_o             <= valid_o;
            end
            else if(flush_i == 1'b1) begin
                inst_addr_o         <= 0;
                inst_o              <= 0;

                rd_w_ena_o          <= 1'b0;
                rd_w_addr_o         <= 5'h0;
                rd_w_data_o         <= 64'h0;

                csr_w_ena_o         <= 1'b0;
                csr_w_addr_o        <= 12'h0;
                csr_w_data_o        <= 64'h0;

                mem_addr_o          <= 0;
                mem_w_data_o        <= 0;

                mem_load_en_o       <= 0;
                mem_store_en_o      <= 0;
                mem_sel_o           <= 0;

                exception_type_o    <= `ZERO_WORD;
                valid_o             <= 1'b0;
            end
            else begin
                inst_addr_o         <= inst_addr_i;
                inst_o              <= inst_i;

                rd_w_ena_o          <= rd_w_ena_i;
                rd_w_addr_o         <= rd_w_addr_i;
                rd_w_data_o         <= rd_w_data_i;
                
                csr_w_ena_o         <= csr_w_ena_i;
                csr_w_addr_o        <= csr_w_addr_i;
                csr_w_data_o        <= csr_w_data_i;

                mem_addr_o          <= mem_addr_i;
                mem_w_data_o        <= mem_w_data_i;

                mem_load_en_o       <= mem_load_en_i;
                mem_store_en_o      <= mem_store_en_i;
                mem_sel_o           <= mem_sel_i;

                exception_type_o    <= exception_type_i;
                valid_o             <= valid_i;
            end 
        end
    end
endmodule


module ysyx_210413_mem_stage(
    input wire                                  rst,

    input  wire [`RAM_ADDR_WIDTH - 1 : 0]       inst_addr_i,
    input  wire [`INST_WIDTH - 1: 0]            inst_i,

    input  wire                                 rd_w_ena_i,
    input  wire [4 : 0]                         rd_w_addr_i,
    input  wire [`REG_BUS]                      rd_w_data_i,

    input  wire                                 csr_w_ena_i,
    input  wire [11: 0]                         csr_w_addr_i,
    input  wire [`REG_BUS]                      csr_w_data_i,

    input  wire [`RAM_ADDR_WIDTH - 1 : 0]       mem_addr_i,
    input  wire [`RAM_DATA_WIDTH - 1: 0]        mem_w_data_i,

    input  wire [`RAM_DATA_WIDTH - 1 : 0]       mem_r_data_i,

    input  wire                                 mem_load_en_i,
    input  wire                                 mem_store_en_i,
    input  wire [`MEM_SEL_BUS]                  mem_sel_i,


    input  wire [`REG_BUS]                      exception_type_from_wb_i,
    input  wire [`REG_BUS]                      exception_type_i,
    input  wire                                 valid_i,

    output wire [`RAM_ADDR_WIDTH - 1 : 0]       inst_addr_o,
    output wire [`INST_WIDTH - 1: 0]            inst_o,

    output wire                                 rd_w_ena_o,
    output wire [4 : 0]                         rd_w_addr_o,
    output wire [`REG_BUS]                      rd_w_data_o,

    output wire                                 csr_w_ena_o,
    output wire [11: 0]                         csr_w_addr_o,
    output wire [`REG_BUS]                      csr_w_data_o,

    output wire [`RAM_DATA_WIDTH / 8 - 1: 0]    dram_w_mask_o,
    output wire [`RAM_DATA_WIDTH - 1 : 0]       dram_w_data_o,
    output wire                                 dram_w_en_o,
    output wire [`RAM_ADDR_WIDTH - 1 : 0]       dram_addr_o,
    output wire [2:0]                           dram_rw_size_o,

    output wire                                 dram_valid,
    input  wire                                 dram_ready,

    output wire                                 stall_3_2_1_flag_o,

    output wire [`REG_BUS]                      exception_type_o,
    output wire                                 valid_o
);

    assign inst_addr_o = inst_addr_i;
    assign inst_o      = inst_i;

    assign rd_w_ena_o  = (rst == 1'h0) ? rd_w_ena_i : 1'b0;
    assign rd_w_addr_o = rd_w_addr_i;
    
    assign csr_w_ena_o = csr_w_ena_i;
    assign csr_w_addr_o= csr_w_addr_i;
    assign csr_w_data_o= csr_w_data_i;
    
    assign exception_type_o = exception_type_i;
    assign valid_o = valid_i;

    //exception
    wire freeze_flag;
    assign freeze_flag = exception_type_o == `ZERO_WORD && exception_type_from_wb_i == `ZERO_WORD ? 1'b0 : 1'b1;

    wire inst_lb_flag;
    wire inst_lh_flag;
    wire inst_lw_flag;
    wire inst_ld_flag;
    wire inst_lbu_flag;
    wire inst_lhu_flag;
    wire inst_lwu_flag;
    wire inst_sb_flag;
    wire inst_sh_flag;
    wire inst_sw_flag;
    wire inst_sd_flag;
    
    assign inst_lb_flag     = (mem_load_en_i  == 1'b1) && (mem_sel_i == `MEM_LB ) ? 1'h1 : 1'h0;
    assign inst_lh_flag     = (mem_load_en_i  == 1'b1) && (mem_sel_i == `MEM_LH ) ? 1'h1 : 1'h0;
    assign inst_lw_flag     = (mem_load_en_i  == 1'b1) && (mem_sel_i == `MEM_LW ) ? 1'h1 : 1'h0;
    assign inst_ld_flag     = (mem_load_en_i  == 1'b1) && (mem_sel_i == `MEM_LD ) ? 1'h1 : 1'h0;
    assign inst_lbu_flag    = (mem_load_en_i  == 1'b1) && (mem_sel_i == `MEM_LBU) ? 1'h1 : 1'h0;
    assign inst_lhu_flag    = (mem_load_en_i  == 1'b1) && (mem_sel_i == `MEM_LHU) ? 1'h1 : 1'h0;
    assign inst_lwu_flag    = (mem_load_en_i  == 1'b1) && (mem_sel_i == `MEM_LWU) ? 1'h1 : 1'h0;

    assign inst_sb_flag     = (mem_store_en_i == 1'b1) && (mem_sel_i == `MEM_SB ) ? 1'h1 : 1'h0;
    assign inst_sh_flag     = (mem_store_en_i == 1'b1) && (mem_sel_i == `MEM_SH ) ? 1'h1 : 1'h0;
    assign inst_sw_flag     = (mem_store_en_i == 1'b1) && (mem_sel_i == `MEM_SW ) ? 1'h1 : 1'h0;
    assign inst_sd_flag     = (mem_store_en_i == 1'b1) && (mem_sel_i == `MEM_SD ) ? 1'h1 : 1'h0;

    /****************************
    *load
    *****************************/
    wire[`REG_BUS] load_lb_result;
    wire[`REG_BUS] load_lbu_result;
    wire[`REG_BUS] load_lh_result;
    wire[`REG_BUS] load_lhu_result;
    wire[`REG_BUS] load_lw_result;
    wire[`REG_BUS] load_lwu_result;
    wire[`REG_BUS] load_ld_result;
    
    wire[`REG_BUS] load_result;

    
    assign load_lb_result  = {64{inst_lb_flag  &  mem_addr_i[2] &  mem_addr_i[1] &  mem_addr_i[0]}} & {{56{mem_r_data_i[63]}}, mem_r_data_i[63:56]}
                           | {64{inst_lb_flag  &  mem_addr_i[2] &  mem_addr_i[1] & ~mem_addr_i[0]}} & {{56{mem_r_data_i[55]}}, mem_r_data_i[55:48]}
                           | {64{inst_lb_flag  &  mem_addr_i[2] & ~mem_addr_i[1] &  mem_addr_i[0]}} & {{56{mem_r_data_i[47]}}, mem_r_data_i[47:40]}
                           | {64{inst_lb_flag  &  mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0]}} & {{56{mem_r_data_i[39]}}, mem_r_data_i[39:32]}
                           | {64{inst_lb_flag  & ~mem_addr_i[2] &  mem_addr_i[1] &  mem_addr_i[0]}} & {{56{mem_r_data_i[31]}}, mem_r_data_i[31:24]}
                           | {64{inst_lb_flag  & ~mem_addr_i[2] &  mem_addr_i[1] & ~mem_addr_i[0]}} & {{56{mem_r_data_i[23]}}, mem_r_data_i[23:16]}
                           | {64{inst_lb_flag  & ~mem_addr_i[2] & ~mem_addr_i[1] &  mem_addr_i[0]}} & {{56{mem_r_data_i[15]}}, mem_r_data_i[15: 8]}
                           | {64{inst_lb_flag  & ~mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0]}} & {{56{mem_r_data_i[ 7]}}, mem_r_data_i[ 7: 0]};

    assign load_lbu_result = {64{inst_lbu_flag &  mem_addr_i[2] &  mem_addr_i[1] &  mem_addr_i[0]}} & {{56{1'b0}}, mem_r_data_i[63:56]}
                           | {64{inst_lbu_flag &  mem_addr_i[2] &  mem_addr_i[1] & ~mem_addr_i[0]}} & {{56{1'b0}}, mem_r_data_i[55:48]}
                           | {64{inst_lbu_flag &  mem_addr_i[2] & ~mem_addr_i[1] &  mem_addr_i[0]}} & {{56{1'b0}}, mem_r_data_i[47:40]}
                           | {64{inst_lbu_flag &  mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0]}} & {{56{1'b0}}, mem_r_data_i[39:32]}
                           | {64{inst_lbu_flag & ~mem_addr_i[2] &  mem_addr_i[1] &  mem_addr_i[0]}} & {{56{1'b0}}, mem_r_data_i[31:24]}
                           | {64{inst_lbu_flag & ~mem_addr_i[2] &  mem_addr_i[1] & ~mem_addr_i[0]}} & {{56{1'b0}}, mem_r_data_i[23:16]}
                           | {64{inst_lbu_flag & ~mem_addr_i[2] & ~mem_addr_i[1] &  mem_addr_i[0]}} & {{56{1'b0}}, mem_r_data_i[15: 8]}
                           | {64{inst_lbu_flag & ~mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0]}} & {{56{1'b0}}, mem_r_data_i[ 7: 0]};

    assign load_lh_result  = {64{inst_lh_flag  &  mem_addr_i[2] &  mem_addr_i[1] & ~mem_addr_i[0]}} & {{48{mem_r_data_i[63]}}, mem_r_data_i[63:48]}
                           | {64{inst_lh_flag  &  mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0]}} & {{48{mem_r_data_i[47]}}, mem_r_data_i[47:32]}
                           | {64{inst_lh_flag  & ~mem_addr_i[2] &  mem_addr_i[1] & ~mem_addr_i[0]}} & {{48{mem_r_data_i[31]}}, mem_r_data_i[31:16]}
                           | {64{inst_lh_flag  & ~mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0]}} & {{48{mem_r_data_i[15]}}, mem_r_data_i[15: 0]};
    
    assign load_lhu_result = {64{inst_lhu_flag &  mem_addr_i[2] &  mem_addr_i[1] & ~mem_addr_i[0]}} & {{48{1'b0}}, mem_r_data_i[63:48]}
                           | {64{inst_lhu_flag &  mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0]}} & {{48{1'b0}}, mem_r_data_i[47:32]}
                           | {64{inst_lhu_flag & ~mem_addr_i[2] &  mem_addr_i[1] & ~mem_addr_i[0]}} & {{48{1'b0}}, mem_r_data_i[31:16]}
                           | {64{inst_lhu_flag & ~mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0]}} & {{48{1'b0}}, mem_r_data_i[15: 0]};

    assign load_lw_result  = {64{inst_lw_flag  &  mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0]}} & {{32{mem_r_data_i[63]}}, mem_r_data_i[63: 32]}
                           | {64{inst_lw_flag  & ~mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0]}} & {{32{mem_r_data_i[31]}}, mem_r_data_i[31: 0]};

    assign load_lwu_result = {64{inst_lwu_flag &  mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0]}} & {{32{1'b0}}, mem_r_data_i[63: 32]}
                           | {64{inst_lwu_flag & ~mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0]}} & {{32{1'b0}}, mem_r_data_i[31: 0]};

    assign load_ld_result  = {64{inst_ld_flag  & ~mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0]}} & mem_r_data_i;

    assign load_result = load_lb_result | load_lbu_result | load_lh_result | load_lhu_result | load_lw_result | load_lwu_result | load_ld_result;
    
    assign rd_w_data_o = (mem_load_en_i == 1'b1) ? load_result : rd_w_data_i;
    /****************************
    *store
    *****************************/
    wire[`RAM_DATA_WIDTH / 8 - 1: 0]   store_sb_mask;
    wire[`RAM_DATA_WIDTH / 8 - 1: 0]   store_sh_mask;
    wire[`RAM_DATA_WIDTH / 8 - 1: 0]   store_sw_mask;
    wire[`RAM_DATA_WIDTH / 8 - 1: 0]   store_sd_mask;

    wire[`REG_BUS]   store_sb_data;
    wire[`REG_BUS]   store_sh_data;
    wire[`REG_BUS]   store_sw_data;
    wire[`REG_BUS]   store_sd_data;
    assign store_sb_mask = {8{inst_sb_flag & ~mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0] }} & 8'b0000_0001
                         | {8{inst_sb_flag & ~mem_addr_i[2] & ~mem_addr_i[1] &  mem_addr_i[0] }} & 8'b0000_0010
                         | {8{inst_sb_flag & ~mem_addr_i[2] &  mem_addr_i[1] & ~mem_addr_i[0] }} & 8'b0000_0100
                         | {8{inst_sb_flag & ~mem_addr_i[2] &  mem_addr_i[1] &  mem_addr_i[0] }} & 8'b0000_1000
                         | {8{inst_sb_flag &  mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0] }} & 8'b0001_0000
                         | {8{inst_sb_flag &  mem_addr_i[2] & ~mem_addr_i[1] &  mem_addr_i[0] }} & 8'b0010_0000
                         | {8{inst_sb_flag &  mem_addr_i[2] &  mem_addr_i[1] & ~mem_addr_i[0] }} & 8'b0100_0000
                         | {8{inst_sb_flag &  mem_addr_i[2] &  mem_addr_i[1] &  mem_addr_i[0] }} & 8'b1000_0000;

    assign store_sh_mask = {8{inst_sh_flag & ~mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0] }} & 8'b0000_0011
                         | {8{inst_sh_flag & ~mem_addr_i[2] &  mem_addr_i[1] & ~mem_addr_i[0] }} & 8'b0000_1100
                         | {8{inst_sh_flag &  mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0] }} & 8'b0011_0000
                         | {8{inst_sh_flag &  mem_addr_i[2] &  mem_addr_i[1] & ~mem_addr_i[0] }} & 8'b1100_0000;

    assign store_sw_mask = {8{inst_sw_flag & ~mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0] }} & 8'b0000_1111
                         | {8{inst_sw_flag &  mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0] }} & 8'b1111_0000;

    assign store_sd_mask = {8{inst_sd_flag & ~mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0] }} & 8'b1111_1111;

    assign store_sb_data = {64{inst_sb_flag & ~mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0] }} & {56'h0, mem_w_data_i[7:0]}
                         | {64{inst_sb_flag & ~mem_addr_i[2] & ~mem_addr_i[1] &  mem_addr_i[0] }} & {48'h0, mem_w_data_i[7:0],  8'h0}
                         | {64{inst_sb_flag & ~mem_addr_i[2] &  mem_addr_i[1] & ~mem_addr_i[0] }} & {40'h0, mem_w_data_i[7:0], 16'h0}
                         | {64{inst_sb_flag & ~mem_addr_i[2] &  mem_addr_i[1] &  mem_addr_i[0] }} & {32'h0, mem_w_data_i[7:0], 24'h0}
                         | {64{inst_sb_flag &  mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0] }} & {24'h0, mem_w_data_i[7:0], 32'h0}
                         | {64{inst_sb_flag &  mem_addr_i[2] & ~mem_addr_i[1] &  mem_addr_i[0] }} & {16'h0, mem_w_data_i[7:0], 40'h0}
                         | {64{inst_sb_flag &  mem_addr_i[2] &  mem_addr_i[1] & ~mem_addr_i[0] }} & { 8'h0, mem_w_data_i[7:0], 48'h0}
                         | {64{inst_sb_flag &  mem_addr_i[2] &  mem_addr_i[1] &  mem_addr_i[0] }} & {       mem_w_data_i[7:0], 56'h0};

    assign store_sh_data = {64{inst_sh_flag & ~mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0] }} & {48'h0, mem_w_data_i[15: 0]}
                         | {64{inst_sh_flag & ~mem_addr_i[2] &  mem_addr_i[1] & ~mem_addr_i[0] }} & {32'h0, mem_w_data_i[15: 0], 16'h0}
                         | {64{inst_sh_flag &  mem_addr_i[2] & ~mem_addr_i[1] & ~mem_addr_i[0] }} & {16'h0, mem_w_data_i[15: 0], 32'h0}
                         | {64{inst_sh_flag &  mem_addr_i[2] &  mem_addr_i[1] & ~mem_addr_i[0] }} & {       mem_w_data_i[15: 0], 48'h0};

    assign store_sw_data = {64{inst_sw_flag & ~mem_addr_i[2] &  ~mem_addr_i[1] & ~mem_addr_i[0] }} & {32'h0, mem_w_data_i[31:0]}
                         | {64{inst_sw_flag &  mem_addr_i[2] &  ~mem_addr_i[1] & ~mem_addr_i[0] }} & {mem_w_data_i[31:0], 32'h0};

    assign store_sd_data = {64{inst_sd_flag & ~mem_addr_i[2] &  ~mem_addr_i[1] & ~mem_addr_i[0] }} & mem_w_data_i;
    ////////////////////////
    assign dram_w_mask_o = store_sb_mask
                         | store_sh_mask
                         | store_sw_mask
                         | store_sd_mask;

    assign dram_w_data_o = store_sb_data
                         | store_sh_data
                         | store_sw_data
                         | store_sd_data;

    assign dram_w_en_o   = mem_store_en_i;

    assign dram_addr_o = mem_addr_i;
    
    wire dram_w_ce;
    assign dram_w_ce = freeze_flag ? 1'b0 : inst_lb_flag
                                          | inst_lh_flag
                                          | inst_lw_flag
                                          | inst_ld_flag
                                          | inst_lbu_flag
                                          | inst_lhu_flag
                                          | inst_lwu_flag
                                          | inst_sb_flag
                                          | inst_sh_flag
                                          | inst_sw_flag
                                          | inst_sd_flag;

    assign dram_rw_size_o = inst_ld_flag | inst_sd_flag                 ? 3'b011 :
                            inst_lw_flag | inst_lwu_flag | inst_sw_flag ? 3'b010 :
                            inst_lh_flag | inst_lhu_flag | inst_sh_flag ? 3'b001 : 3'b000;
    // assign dram_rw_size_o = 3'b011;

    assign dram_valid = dram_w_ce;
    assign stall_3_2_1_flag_o = dram_w_ce == 1'b1 && dram_ready == 1'b0 ? 1'b1 : 1'b0;

endmodule


module ysyx_210413_mem_filter (
    
    input  wire [`RAM_DATA_WIDTH / 8 - 1: 0]    dram_w_mask_i,
    input  wire [`RAM_DATA_WIDTH - 1 : 0]       dram_w_data_i,
    input  wire                                 dram_w_en_i,
    output wire [`RAM_DATA_WIDTH - 1 : 0]       dram_r_data_o,
    input  wire [`RAM_ADDR_WIDTH - 1 : 0]       dram_addr_i,

    input  wire                                 dram_valid_i,
    output wire                                 dram_ready_o,

    output wire [`RAM_DATA_WIDTH / 8 - 1: 0]    dram_w_mask_o,
    output wire [`RAM_DATA_WIDTH - 1 : 0]       dram_w_data_o,
    output wire                                 dram_w_en_o,
    output wire [`RAM_ADDR_WIDTH - 1 : 0]       dram_addr_o,

    input  wire [`RAM_DATA_WIDTH - 1 : 0]       dram_r_data_i,
    output wire                                 dram_valid_o,
    input  wire                                 dram_ready_i,

    input  wire [`REG_BUS]                      clint_r_data_i,
    output wire                                 clint_valid_o,
    input  wire                                 clint_ready_i,

    output wire                                 skip_o
);
    wire   clint_addr_flag;
    assign clint_addr_flag = (dram_addr_i >= `RAM_ADDR_WIDTH'h200_0000) && (dram_addr_i <= `RAM_ADDR_WIDTH'h200_BFFF);
    assign clint_addr_flag = dram_addr_i[`RAM_ADDR_WIDTH - 1:16] == {{`RAM_ADDR_WIDTH - 28{1'b0}}, 12'h200};

    assign dram_r_data_o   = clint_addr_flag == 1'b0 ? dram_r_data_i : clint_r_data_i;
    assign dram_ready_o    = dram_ready_i | clint_ready_i;

    assign dram_w_mask_o   = dram_w_mask_i;
    assign dram_w_data_o   = dram_w_data_i;
    assign dram_w_en_o     = dram_w_en_i;
    assign dram_addr_o     = dram_addr_i;

    assign dram_valid_o    = clint_addr_flag == 1'b0 ? dram_valid_i : 1'b0;

    assign clint_valid_o   = clint_addr_flag == 1'b1 ? dram_valid_i : 1'b0;



    assign skip_o = dram_valid_i == 1'b1 && clint_addr_flag == 1'b1 ? 1'b1 : 1'b0;
endmodule


module ysyx_210413_mem_wb (
    input wire                              clk,
    input wire                              rst,
    
    input  wire                             stall_i,
    input  wire                             flush_i,

    input  wire[`RAM_ADDR_WIDTH - 1 : 0]    inst_addr_i,
    input  wire[`INST_WIDTH - 1: 0]         inst_i,

    input  wire                             rd_w_ena_i,
    input  wire[4 : 0]                      rd_w_addr_i,
    input  wire[`REG_BUS]                   rd_w_data_i,

    input  wire                             csr_w_ena_i,
    input  wire[11: 0]                      csr_w_addr_i,
    input  wire[`REG_BUS]                   csr_w_data_i,

    input  wire[`REG_BUS]                   exception_type_i,
    input  wire                             valid_i,

    input  wire                             skip_i,

    output reg [`RAM_ADDR_WIDTH - 1 : 0]    inst_addr_o,
    output reg [`INST_WIDTH - 1: 0]         inst_o,

    output reg                              rd_w_ena_o,
    output reg [4 : 0]                      rd_w_addr_o,
    output reg [`REG_BUS]                   rd_w_data_o,

    output reg                              csr_w_ena_o,
    output reg [11: 0]                      csr_w_addr_o,
    output reg [`REG_BUS]                   csr_w_data_o,

    output reg [`REG_BUS]                   exception_type_o,
    output reg                              valid_o,

    output reg                              skip_o
);
    always @(posedge clk) begin
        if(rst == 1'b1) begin
            inst_addr_o         <= 0;
            inst_o              <= 0;

            rd_w_ena_o          <= 1'b0;
            rd_w_addr_o         <= 5'h0;
            rd_w_data_o         <= 64'h0;

            csr_w_ena_o         <= 1'b0;
            csr_w_addr_o        <= 12'h0;
            csr_w_data_o        <= 64'h0;

            exception_type_o    <= `ZERO_WORD;
            valid_o             <= 1'b0;
            skip_o              <= 1'b0;
        end
        else begin
            if(stall_i == 1'b1) begin
                inst_addr_o         <= inst_addr_o;
                inst_o              <= inst_o;

                rd_w_ena_o          <= rd_w_ena_o;
                rd_w_addr_o         <= rd_w_addr_o;
                rd_w_data_o         <= rd_w_data_o;

                csr_w_ena_o         <= csr_w_ena_o;
                csr_w_addr_o        <= csr_w_addr_o;
                csr_w_data_o        <= csr_w_data_o;

                exception_type_o    <= exception_type_o;
                valid_o             <= valid_o;
                
                skip_o              <= skip_o;
            end
            else if(flush_i == 1'b1) begin
                inst_addr_o         <= 0;
                inst_o              <= 0;

                rd_w_ena_o          <= 1'b0;
                rd_w_addr_o         <= 5'h0;
                rd_w_data_o         <= 64'h0;

                csr_w_ena_o         <= 1'b0;
                csr_w_addr_o        <= 12'h0;
                csr_w_data_o        <= 64'h0;

                exception_type_o    <= `ZERO_WORD;
                valid_o             <= 1'b0;
                skip_o              <= 1'b0;
            end
            else begin
                inst_addr_o         <= inst_addr_i;
                inst_o              <= inst_i;

                rd_w_ena_o          <= rd_w_ena_i;
                rd_w_addr_o         <= rd_w_addr_i;
                rd_w_data_o         <= rd_w_data_i;

                csr_w_ena_o         <= csr_w_ena_i;
                csr_w_addr_o        <= csr_w_addr_i;
                csr_w_data_o        <= csr_w_data_i;

                exception_type_o    <= exception_type_i;
                valid_o             <= valid_i;
                skip_o              <= skip_i;
            end
        end
    end
endmodule


module ysyx_210413_wb_stage(
    input wire                              rst,

    input wire [`RAM_ADDR_WIDTH - 1 : 0]    inst_addr_i,
    input wire [`INST_WIDTH - 1: 0]         inst_i,

    input wire                              rd_w_ena_i,
    input wire [4 : 0]                      rd_w_addr_i,
    input wire [`REG_BUS]                   rd_w_data_i,

    input wire                              csr_w_ena_i,
    input wire [11: 0]                      csr_w_addr_i,
    input wire [`REG_BUS]                   csr_w_data_i,

    input wire [`REG_BUS]                   exception_type_i,
    input wire                              valid_i,

    input wire                              skip_i,

    output wire [`RAM_ADDR_WIDTH - 1 : 0]   inst_addr_o,
    output wire [`INST_WIDTH - 1: 0]        inst_o,

    output wire                             rd_w_ena_o,
    output wire [4 : 0]                     rd_w_addr_o,
    output wire [`REG_BUS]                  rd_w_data_o,

    output wire                             csr_w_ena_o,
    output wire [11: 0]                     csr_w_addr_o,
    output wire [`REG_BUS]                  csr_w_data_o,

    output wire [`REG_BUS]                  exception_type_o,
    output wire                             valid_o,

    output wire                             skip_o
);
    assign inst_addr_o = inst_addr_i;
    assign inst_o      = inst_i;

    assign rd_w_ena_o  = (rst == 1'b1)                  ? 1'b0 :
                         exception_type_i == `ZERO_WORD ? rd_w_ena_i : 1'b0;
    assign rd_w_addr_o = rd_w_addr_i;
    assign rd_w_data_o = rd_w_data_i;

    assign csr_w_ena_o = exception_type_i == `ZERO_WORD ? csr_w_ena_i : 1'b0;
    assign csr_w_addr_o= csr_w_addr_i;
    assign csr_w_data_o= csr_w_data_i;

    assign exception_type_o = exception_type_i;
    // assign valid_o = exception_type_i == `ZERO_WORD ? valid_i : 1'b0;
    assign valid_o = exception_type_i[39] == 1'b0 && exception_type_i[5] == 1'b0 ? valid_i : 1'b0;
    // assign valid_o = valid_i;
    // assign skip_o  = skip_i;
    assign skip_o  = inst_i == 32'h7b ? 1'b1 : skip_i;
endmodule
