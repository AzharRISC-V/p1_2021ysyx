/* verilator lint_off DECLFILENAME */

// ZhengpuShi

// Definitions


`define ZERO_WORD           64'h00000000_00000000

`ifdef YSYXSOC
  `define PC_START            64'h00000000_30000000 
`else
  `define PC_START            64'h00000000_80000000 
`endif

`define SIZE_B              3'b000
`define SIZE_H              3'b001
`define SIZE_W              3'b010
`define SIZE_D              3'b011

`define REQ_READ            1'b0
`define REQ_WRITE           1'b1

`define RW_DATA_WIDTH       512
`define AXI_ID_WIDTH        4

`define RISCV_PRIV_MODE_U   0
`define RISCV_PRIV_MODE_S   1
`define RISCV_PRIV_MODE_M   3

// mem_stage三种类型的动作
`define MEM_ACTION_NONE     0     // 普通指令，不访存
`define MEM_ACTION_LOAD     1     // load指令，数据要写入 rd
`define MEM_ACTION_STORE    2     // store指令，存入数据


`define CLOCKS_PER_SECOND   64'd240_0000        // 每秒的clock数，约240万

`define BUS_8               7:0
`define BUS_16              15:0
`define BUS_32              31:0
`define BUS_64              63:0
`define BUS_256             255:0
`define BUS_RIDX            4:0                 // 寄存器索引的总线
`define BUS_FUNCT3          2:0                 // funct3的总线
`define BUS_FUNCT7          6:0                 // funct7的总线
`define BUS_OPCODE          6:0                 // opcode的总线

// 指令状态机
`define STATE_BUS           3:0
`define STATE_NONE          4'd0
`define STATE_IF            4'd1
`define STATE_ID            4'd2
`define STATE_EX            4'd3
`define STATE_MEM           4'd4
`define STATE_WB            4'd5
`define STATE_CMT           4'd6

// CSR
`define BUS_CSR_ADDR        11 : 0          // CSR存储器地址

// CSR addr
`define CSR_ADR_MCYCLE      12'hB00
`define CSR_ADR_MSTATUS     12'h300         // machine status register
`define CSR_ADR_MIE         12'h304         // machine interrupt-enable register
`define CSR_ADR_MTVEC       12'h305         // machine trap-handler base address
`define CSR_ADR_MSCRATCH    12'h340         // scratch register for machine trap handlers.
`define CSR_ADR_MEPC        12'h341         // machine exception program counter
`define CSR_ADR_MCAUSE      12'h342         // machine trap cause
`define CSR_ADR_MIP         12'h344         // machine interrupt pending

// CSR index in local memory
`define CSR_IDX_NONE        4'd0
`define CSR_IDX_MCYCLE      4'd1
`define CSR_IDX_MSTATUS     4'd2
`define CSR_IDX_MIE         4'd3
`define CSR_IDX_MTVEC       4'd4
`define CSR_IDX_MSCRATCH    4'd5
`define CSR_IDX_MEPC        4'd6
`define CSR_IDX_MCAUSE      4'd7
`define CSR_IDX_MIP         4'd8

// 寄存器配置
`define REG_BITS            64              // 寄存器位数
`define REG_BUS_old         63:0            // 寄存器总线
`define REG_ADDR_BITS       5               // 寄存器地址位数
`define REG_ADDR_BUS        4:0             // 寄存器地址总线
`define REG_NUM             32              // 寄存器个数
`define REG_ZERO            64'd0           // 寄存器数值0

// 指令配置
`define INST_BITS           32              // 指令位数
`define INST_BUS            31:0            // 指令总线

// RAM配置(4KB)
`define RAM_DATA_BITS       32              // RAM数据位数
`define RAM_DATA_BUS        31:0            // RAM数据总线
`define RAM_ADDR_BITS       12              // RAM地址位数
`define RAM_ADDR_BUS        11:0            // RAM地址总线
`define RAM_DATA_ZERO       32'd0           // RAM数据0
`define RAM_SIZE_BUS        4095:0          // RAM单元数总线

// ROM配置(4KB)
`define ROM_DATA_BITS       32              // ROM数据位数
`define ROM_DATA_BUS        31:0            // ROM数据总线
`define ROM_ADDR_BITS       12              // ROM地址位数
`define ROM_ADDR_BUS        11:0            // ROM地址总线
`define ROM_DATA_ZERO       32'd0           // ROM数据0
`define ROM_SIZE_BUS        4095:0          // ROM单元数总线

// 已编码的指令
`define INST_NOP            32'h0000_0013   // addi x0,x0,0

// 自定义的指令码
`define INST_LUI            8'b0000_0001    // d1
`define INST_AUIPC          8'b0000_0010    //
`define INST_JAL            8'b0000_0011    //
`define INST_JALR           8'b0000_0100    // 
`define INST_BEQ            8'b0000_0101    //
`define INST_BNE            8'b0000_0110    //
`define INST_BLT            8'b0000_0111    //
`define INST_BGE            8'b0000_1000    //
`define INST_BLTU           8'b0000_1001    //
`define INST_BGEU           8'b0000_1010    //
`define INST_LB             8'b0000_1011    //
`define INST_LH             8'b0000_1100    //
`define INST_LW             8'b0000_1101    //
`define INST_LBU            8'b0000_1110    //
`define INST_LHU            8'b0000_1111    // 
`define INST_SB             8'b0001_0000    //
`define INST_SH             8'b0001_0001    //
`define INST_SW             8'b0001_0010    //
`define INST_ADDI           8'b0001_0011    //
`define INST_SLTI           8'b0001_0100    //
`define INST_SLTIU          8'b0001_0101    //
`define INST_XORI           8'b0001_0110    //
`define INST_ORI            8'b0001_0111    //
`define INST_ANDI           8'b0001_1000    //
`define INST_SLLI           8'b0001_1001    //
`define INST_SRLI           8'b0001_1010    //
`define INST_SRAI           8'b0001_1011    //
`define INST_ADD            8'b0001_1100    //
`define INST_SUB            8'b0001_1101    //
`define INST_SLL            8'b0001_1110    //
`define INST_SLT            8'b0001_1111    //
`define INST_SLTU           8'b0010_0000    //
`define INST_XOR            8'b0010_0001    //
`define INST_SRL            8'b0010_0010    //
`define INST_SRA            8'b0010_0011    //
`define INST_OR             8'b0010_0100    //
`define INST_AND            8'b0010_0101    //
`define INST_FENCE          8'b0010_0110    //
`define INST_FENCEI         8'b0010_0111    //
`define INST_ECALL          8'b0010_1000    //
`define INST_EBREAK         8'b0010_1001    //
`define INST_CSRRW          8'b0010_1010    //
`define INST_CSRRS          8'b0010_1011    //
`define INST_CSRRC          8'b0010_1100    //
`define INST_CSRRWI         8'b0010_1101    //
`define INST_CSRRSI         8'b0010_1110    //
`define INST_CSRRCI         8'b0010_1111    // d47 = h2F

`define INST_LWU            8'b0011_0000    //
`define INST_LD             8'b0011_0001    //
`define INST_SD             8'b0011_0010    //
`define INST_ADDIW          8'b0011_0011    //
`define INST_SLLIW          8'b0011_0100    //
`define INST_SRLIW          8'b0011_0101    //
`define INST_SRAIW          8'b0011_0110    //
`define INST_ADDW           8'b0011_0111    //
`define INST_SUBW           8'b0011_1000    //
`define INST_SLLW           8'b0011_1001    //
`define INST_SRLW           8'b0011_1010    //
`define INST_SRAW           8'b0011_1011    //
`define INST_MRET           8'b0011_1100    //

// CSR Operation
`define CSROP_NONE          2'b00     // none
`define CSROP_READ_WRITE    2'b01     // read and write
`define CSROP_READ_SET      2'b10     // read and set
`define CSROP_READ_CLEAR    2'b11     // read and clear

// === Devices

`define DEV_BASEADDR        64'h0200_0000

// RTC
`define DEV_RTC_OFFSET      64'h0100
`define DEV_RTC             (`DEV_BASEADDR + `DEV_RTC_OFFSET)

// Machine time register，以恒定频率增加，廉价的RTC软件方案
// mcycle与mtime的区别：
// 1. mcycle可随外接时钟而变化
// 2. mtime必须以恒定的频率增加（估计是因指令执行耗费的clock数不同而引起，这里需要封装差异吗）
`define DEV_MTIME_OFFSET    64'hbff8
`define DEV_MTIME           (`DEV_BASEADDR + `DEV_MTIME_OFFSET)
// Machien time compare register
// 当 mtime >= mtimecmp 时，产生计时器中断
// mip的MTIP位置1。
`define DEV_MTIMECMP_OFFSET 64'h4000
`define DEV_MTIMECMP        (`DEV_BASEADDR + `DEV_MTIMECMP_OFFSET)


// AXI Read & Write Unit


// Burst types
`define AXI_BURST_TYPE_FIXED                                2'b00
`define AXI_BURST_TYPE_INCR                                 2'b01
`define AXI_BURST_TYPE_WRAP                                 2'b10
// Access permissions
`define AXI_PROT_UNPRIVILEGED_ACCESS                        3'b000
`define AXI_PROT_PRIVILEGED_ACCESS                          3'b001
`define AXI_PROT_SECURE_ACCESS                              3'b000
`define AXI_PROT_NON_SECURE_ACCESS                          3'b010
`define AXI_PROT_DATA_ACCESS                                3'b000
`define AXI_PROT_INSTRUCTION_ACCESS                         3'b100
// Memory types (AR)
`define AXI_ARCACHE_DEVICE_NON_BUFFERABLE                   4'b0000
`define AXI_ARCACHE_DEVICE_BUFFERABLE                       4'b0001
`define AXI_ARCACHE_NORMAL_NON_CACHEABLE_NON_BUFFERABLE     4'b0010
`define AXI_ARCACHE_NORMAL_NON_CACHEABLE_BUFFERABLE         4'b0011
`define AXI_ARCACHE_WRITE_THROUGH_NO_ALLOCATE               4'b1010
`define AXI_ARCACHE_WRITE_THROUGH_READ_ALLOCATE             4'b1110
`define AXI_ARCACHE_WRITE_THROUGH_WRITE_ALLOCATE            4'b1010
`define AXI_ARCACHE_WRITE_THROUGH_READ_AND_WRITE_ALLOCATE   4'b1110
`define AXI_ARCACHE_WRITE_BACK_NO_ALLOCATE                  4'b1011
`define AXI_ARCACHE_WRITE_BACK_READ_ALLOCATE                4'b1111
`define AXI_ARCACHE_WRITE_BACK_WRITE_ALLOCATE               4'b1011
`define AXI_ARCACHE_WRITE_BACK_READ_AND_WRITE_ALLOCATE      4'b1111
// Memory types (AW)
`define AXI_AWCACHE_DEVICE_NON_BUFFERABLE                   4'b0000
`define AXI_AWCACHE_DEVICE_BUFFERABLE                       4'b0001
`define AXI_AWCACHE_NORMAL_NON_CACHEABLE_NON_BUFFERABLE     4'b0010
`define AXI_AWCACHE_NORMAL_NON_CACHEABLE_BUFFERABLE         4'b0011
`define AXI_AWCACHE_WRITE_THROUGH_NO_ALLOCATE               4'b0110
`define AXI_AWCACHE_WRITE_THROUGH_READ_ALLOCATE             4'b0110
`define AXI_AWCACHE_WRITE_THROUGH_WRITE_ALLOCATE            4'b1110
`define AXI_AWCACHE_WRITE_THROUGH_READ_AND_WRITE_ALLOCATE   4'b1110
`define AXI_AWCACHE_WRITE_BACK_NO_ALLOCATE                  4'b0111
`define AXI_AWCACHE_WRITE_BACK_READ_ALLOCATE                4'b0111
`define AXI_AWCACHE_WRITE_BACK_WRITE_ALLOCATE               4'b1111
`define AXI_AWCACHE_WRITE_BACK_READ_AND_WRITE_ALLOCATE      4'b1111

`define AXI_SIZE_BYTES_1                                    3'b000
`define AXI_SIZE_BYTES_2                                    3'b001
`define AXI_SIZE_BYTES_4                                    3'b010
`define AXI_SIZE_BYTES_8                                    3'b011
`define AXI_SIZE_BYTES_16                                   3'b100
`define AXI_SIZE_BYTES_32                                   3'b101
`define AXI_SIZE_BYTES_64                                   3'b110
`define AXI_SIZE_BYTES_128                                  3'b111

module ysyx_210544_axi_rw (
    input                               clock,
    input                               reset,

	  input                               user_valid_i,
	  output                              user_ready_o,
    input                               user_req_i,         // read or write
    input  [7:0]                        user_blks_i,          // blocks: 0 ~ 7， means 1~8 (后端硬件资源限制为8)
    output reg [`RW_DATA_WIDTH-1:0]     user_rdata_o,
    input  [`RW_DATA_WIDTH-1:0]         user_wdata_i,
    input  [63:0]                       user_addr_i,
    input  [2:0]                        user_size_i,
    output [1:0]                        user_resp_o,

    // Advanced eXtensible Interface
    input                               axi_aw_ready_i,
    output                              axi_aw_valid_o,
    output [63:0]                       axi_aw_addr_o,
    output [`AXI_ID_WIDTH-1:0]          axi_aw_id_o,
    output [7:0]                        axi_aw_len_o,
    output [2:0]                        axi_aw_size_o,
    output [1:0]                        axi_aw_burst_o,

    input                               axi_w_ready_i,
    output                              axi_w_valid_o,
    output [63:0]                       axi_w_data_o,
    output [7:0]                        axi_w_strb_o,
    output                              axi_w_last_o,
    
    output                              axi_b_ready_o,
    input                               axi_b_valid_i,
    input  [1:0]                        axi_b_resp_i,
    input  [`AXI_ID_WIDTH-1:0]          axi_b_id_i,

    input                               axi_ar_ready_i,
    output                              axi_ar_valid_o,
    output [63:0]                       axi_ar_addr_o,
    output [`AXI_ID_WIDTH-1:0]          axi_ar_id_o,
    output [7:0]                        axi_ar_len_o,
    output [2:0]                        axi_ar_size_o,
    output [1:0]                        axi_ar_burst_o,
    
    output                              axi_r_ready_o,
    input                               axi_r_valid_i,
    input  [1:0]                        axi_r_resp_i,
    input  [63:0]                       axi_r_data_i,
    input                               axi_r_last_i,
    input  [`AXI_ID_WIDTH-1:0]          axi_r_id_i
);

    wire w_trans    = user_req_i == `REQ_WRITE;
    wire r_trans    = user_req_i == `REQ_READ;
    wire w_valid    = user_valid_i & w_trans & (!rw_ready);
    wire r_valid    = user_valid_i & r_trans & (!rw_ready);

    // handshake
    wire aw_hs      = axi_aw_ready_i & axi_aw_valid_o;
    wire w_hs       = axi_w_ready_i  & axi_w_valid_o;
    wire b_hs       = axi_b_ready_o  & axi_b_valid_i;
    wire ar_hs      = axi_ar_ready_i & axi_ar_valid_o;
    wire r_hs       = axi_r_ready_o  & axi_r_valid_i;

    wire w_done     = w_hs & axi_w_last_o;
    wire r_done     = r_hs & axi_r_last_i;
    wire trans_done = w_trans ? b_hs : r_done;

    
    // ------------------State Machine------------------
    parameter [1:0] W_STATE_IDLE = 2'b00, W_STATE_ADDR = 2'b01, W_STATE_WRITE = 2'b10, W_STATE_RESP = 2'b11;
    parameter [1:0] R_STATE_IDLE = 2'b00, R_STATE_ADDR = 2'b01, R_STATE_READ  = 2'b10;

    reg [1:0] w_state, r_state;
    wire w_state_idle = w_state == W_STATE_IDLE, w_state_addr = w_state == W_STATE_ADDR, w_state_write = w_state == W_STATE_WRITE, w_state_resp = w_state == W_STATE_RESP;
    wire r_state_idle = r_state == R_STATE_IDLE, r_state_addr = r_state == R_STATE_ADDR, r_state_read  = r_state == R_STATE_READ;

    // Wirte State Machine
    always @(posedge clock) begin
        if (reset) begin
            w_state <= W_STATE_IDLE;
        end
        else begin
            if (w_valid) begin
                case (w_state)
                    W_STATE_IDLE:               w_state <= W_STATE_ADDR;
                    W_STATE_ADDR:  if (aw_hs)   w_state <= W_STATE_WRITE;
                    W_STATE_WRITE: if (w_done)  w_state <= W_STATE_RESP;
                    W_STATE_RESP:  if (b_hs)    w_state <= W_STATE_IDLE;
                endcase
            end
        end
    end

    // Read State Machine
    always @(posedge clock) begin
        if (reset) begin
            r_state <= R_STATE_IDLE;
        end
        else begin
            if (r_valid) begin
                case (r_state)
                    R_STATE_IDLE:               r_state <= R_STATE_ADDR;
                    R_STATE_ADDR: if (ar_hs)    r_state <= R_STATE_READ;
                    R_STATE_READ: if (r_done)   r_state <= R_STATE_IDLE;
                    default:;
                endcase
            end
        end
    end


    // ------------------Number of transmission------------------
    reg [7:0] len;
    wire len_reset      = reset | (w_trans & w_state_idle) | (r_trans & r_state_idle);
    wire len_incr_en    = (len != axi_len) & (w_hs | r_hs);
    always @(posedge clock) begin
        if (len_reset) begin
            len <= 0;
        end
        else if (len_incr_en) begin
            len <= len + 1;
        end
    end


    // ------------------Process Data------------------
    parameter TRANS_LEN_MAX = 8;

    wire [7:0] axi_len      = user_blks_i;
    wire [2:0] axi_size     = user_size_i;
    
    wire [63:0] axi_addr                         = user_addr_i;
    wire [`AXI_ID_WIDTH-1:0] axi_id              = {`AXI_ID_WIDTH{1'b0}};

    reg rw_ready;
    wire rw_ready_nxt = trans_done;
    wire rw_ready_en      = trans_done | rw_ready;
    always @(posedge clock) begin
        if (reset) begin
            rw_ready <= 0;
        end
        else if (rw_ready_en) begin
            rw_ready <= rw_ready_nxt;
        end
    end
    assign user_ready_o     = rw_ready;

    reg [1:0] rw_resp;
    wire [1:0] rw_resp_nxt = w_trans ? axi_b_resp_i : axi_r_resp_i;
    wire resp_en = trans_done;
    always @(posedge clock) begin
        if (reset) begin
            rw_resp <= 0;
        end
        else if (resp_en) begin
            rw_resp <= rw_resp_nxt;
        end
    end
    assign user_resp_o      = rw_resp;


    // ------------------Write Transaction------------------

    // Read address channel signals
    assign axi_aw_valid_o   = w_state_addr & user_valid_i;
    assign axi_aw_addr_o    = axi_addr;
    assign axi_aw_id_o      = axi_id;
    assign axi_aw_len_o     = axi_len;
    assign axi_aw_size_o    = axi_size;
    assign axi_aw_burst_o   = `AXI_BURST_TYPE_INCR;

    // Write data channel signals

    // 由于 w_valid 使能之时需要同时送出 wdata，所以改用时序逻辑
    always @(posedge clock) begin
      if (reset) begin
        axi_w_valid_o <= 0;
      end
      else begin
        if (w_state_write) begin
          if (!axi_w_valid_o) begin
            axi_w_data_o  <= user_wdata_i[63:0];
            axi_w_valid_o <= 1;
          end
        end
        else if (w_state_resp) begin// (w_state_resp) begin
          axi_w_valid_o <= 0;
        end
      end
    end

    assign axi_w_last_o     = w_hs & (len == axi_len);
  
    // 仅根据size生成的wstrb，需要移位后使用，是吗？？
    reg  [7:0] axi_w_strb_orig;
    always @(*) begin
      if (reset) begin
        axi_w_strb_orig = 0;
      end
      else begin
        case (user_size_i)
          `SIZE_B: axi_w_strb_orig = 8'b0000_0001;
          `SIZE_H: axi_w_strb_orig = 8'b0000_0011;
          `SIZE_W: axi_w_strb_orig = 8'b0000_1111;
          `SIZE_D: axi_w_strb_orig = 8'b1111_1111;
          default: axi_w_strb_orig = 8'b0000_0000; // 不支持
        endcase 
      end
    end

    // 输入地址的8字节内偏移量
    // wire [2:0] axi_addr_offset = user_addr_i[2:0];

    // 移位生成最终的 w_strb。可是数据确实是在低位，可能 wdata 和 wstrb 都不需要移位
    // assign axi_w_strb_o     = 8'b1111_1111;     // 每个bit代表一个字节是否要写入
    assign axi_w_strb_o = axi_w_strb_orig;// << axi_addr_offset;

    // Wreite response channel signals
    assign axi_b_ready_o    = w_state_resp;

    generate
        for (genvar i = 0; i < TRANS_LEN_MAX - 1; i += 1) begin
            always @(posedge clock) begin
                if (w_hs) begin
                  if (len == i) begin
                    axi_w_data_o <= user_wdata_i[(i+1)*64+:64];
                  end
                end
            end
        end
    endgenerate

    
    // ------------------Read Transaction------------------

    // Read address channel signals
    assign axi_ar_valid_o   = r_state_addr & user_valid_i;
    assign axi_ar_addr_o    = axi_addr;
    assign axi_ar_id_o      = axi_id;
    assign axi_ar_len_o     = axi_len;
    assign axi_ar_size_o    = axi_size;
    assign axi_ar_burst_o   = `AXI_BURST_TYPE_INCR;

    // Read data channel signals
    assign axi_r_ready_o    = r_state_read;

    // User Data Size
    wire size_b             = user_size_i == `SIZE_B;
    wire size_h             = user_size_i == `SIZE_H;
    wire size_w             = user_size_i == `SIZE_W;
    wire size_d             = user_size_i == `SIZE_D;
    
    // Read data mask
    wire [63:0] mask_rdata  = (({ 64{size_b}} & {{64- 8{1'b0}}, 8'hff})
                              | ({64{size_h}} & {{64-16{1'b0}}, 16'hffff})
                              | ({64{size_w}} & {{64-32{1'b0}}, 32'hffffffff})
                              | ({64{size_d}} & {{64-64{1'b0}}, 64'hffffffff_ffffffff})
                              );

    // 移位的bit数。0~7 转换为 0~56
    wire [5:0] aligned_offset    = {3'b0, user_addr_i[2:0]} << 3;
    // 已掩码，已移位后的数据
    wire [63:0] axi_r_data_masked_unaligned = (axi_r_data_i >> aligned_offset) & mask_rdata;

    generate
        for (genvar i = 0; i < TRANS_LEN_MAX; i += 1) begin
            always @(posedge clock) begin
                if (reset) begin
                    user_rdata_o <= 0;
                end
                else if (r_hs) begin
                    if (len == i) begin
                        user_rdata_o[i*64+:64] <= axi_r_data_masked_unaligned;
                    end
                end
            end
        end
    endgenerate

wire _unused_ok = &{1'b0,
  axi_b_id_i,
  axi_r_id_i,
  1'b0};

endmodule


module ysyx_210544_S011HD1P_X32Y2D128_BW(
    Q, CLK, CEN, WEN, BWEN, A, D
);
parameter Bits = 128;
parameter Word_Depth = 64;
parameter Add_Width = 6;
parameter Wen_Width = 128;

output reg [Bits-1:0] Q;
input                 CLK;
input                 CEN;        // 低电平有效
input                 WEN;        // 低电平有效
input [Wen_Width-1:0] BWEN;       // 低电平有效
input [Add_Width-1:0] A;
input [Bits-1:0]      D;

wire cen  = ~CEN;
wire wen  = ~WEN;
wire [Wen_Width-1:0] bwen = ~BWEN;

reg [Bits-1:0] ram [0:Word_Depth-1];
always @(posedge CLK) begin
    if(cen && wen) begin
        ram[A] <= (D & bwen) | (ram[A] & ~bwen);
    end
    Q <= cen && !wen ? ram[A] : 0;//{4{$random}};
end

endmodule

// ZhengpuShi

// Cache AXI Unit
// Cache的AXI通信模块。
// 通过AXI更新Cache数据的，根据Cache的设计而定制的AXI访问控制
// 对外接口：访问64字节（=512bit），包括读、写
// 内部需要转换为AXI访问的多次读写。
// 1. AXI数据宽度最多64bit，已确认。
// 2. AXI burst len最多是8，这样一次最多传输64字节。


module ysyx_210544_cache_axi(
  input   wire                      clk,
  input   wire                      rst,
	input                             i_cache_axi_req,        // 请求读写
  input   wire  [63 : 0]            i_cache_axi_addr,       // 存储器地址（字节为单位），128字节对齐，低7位为0。
  input   wire                      i_cache_axi_op,         // 操作类型：0读取，1写入
  input   reg   [511 : 0]           i_cache_axi_wdata,      // 写入的数据
  output  reg   [511 : 0]           o_cache_axi_rdata,      // 读出的数据
	output  reg                       o_cache_axi_ack,        // 读写完成应答

  ///////////////////////////////////////////////
  // AXI interface
	output                            o_axi_io_op,            // 0:read, 1:write
	input                             i_axi_io_ready,
  input         [511 : 0]           i_axi_io_rdata,
	output reg                        o_axi_io_valid,
  output reg    [63 : 0]            o_axi_io_addr,
  output        [511 : 0]           o_axi_io_wdata,
  output        [2 : 0]             o_axi_io_size,
  output        [7 : 0]             o_axi_io_blks
);

// 是否为Flash外设，此时只能4字节传输，且不能使用burst模式，所以64字节需要16次传输
wire is_flash = i_cache_axi_addr[31:28] == 4'h3;

// axi一次传输完成
wire hs_ok = o_axi_io_valid & i_axi_io_ready;

// axi每次传输的大小：64bit
assign o_axi_io_size = is_flash ? `SIZE_W : `SIZE_D;

// 块数：0~7表示1~8块
assign o_axi_io_blks = is_flash ? 0 : 7;

// 操作类型：0:read, 1:write
assign o_axi_io_op = i_cache_axi_op;

// 跟踪req信号，连续两个周期的 req 才认为是开始信号，防止一结束就又开始了新的阶段
reg cache_req_his0;

// axi请求开始
wire  axi_start    = i_cache_axi_req & !cache_req_his0;

// 传输起始地址，64字节对齐
// assign o_axi_io_addr = i_cache_axi_addr & (~64'h3F);

// 控制传输次数，
// 如果是主存，  需要 1次AXI传输得512bit；
// 如果是Flash，需要16次AXI传输得到512bit，每次传输32bit（64bit是否支持？？）；
reg [3:0] trans_cnt;
reg [3:0] trans_cnt_write;
wire [8:0] offset_bits = {5'd0, trans_cnt} << 5;
wire [8:0] offset_bits_write = {5'd0, trans_cnt_write} << 5;

// 控制传输
always @( posedge clk ) begin
  if (rst) begin
    o_cache_axi_ack         <= 0;
    o_axi_io_valid          <= 0;
    cache_req_his0          <= 0;
    trans_cnt               <= 0;
  end
  else begin
    // 追踪开始信号
    cache_req_his0  <= i_cache_axi_req;

    // 收到数据：保存数据、增加计数、握手反馈
    if (hs_ok) begin
      if (is_flash) begin
          o_cache_axi_rdata[offset_bits +:32] <= i_axi_io_rdata[0+:32]; // 保存数据
        if (trans_cnt < 15) begin
          o_axi_io_wdata    <= {480'd0, i_cache_axi_wdata[offset_bits_write +:32]}; // 准备数据
          o_axi_io_addr <= o_axi_io_addr + 4;     // 地址递增
          trans_cnt <= trans_cnt + 1;             // 次数递增
          trans_cnt_write <= trans_cnt_write + 1;
        end
        else begin
          o_cache_axi_ack   <= 1;   // 完成
          o_axi_io_valid    <= 0;   // 关闭axi请求
          trans_cnt <= 0;   // 清零计数，准备下次继续
          trans_cnt_write <= 1; // 初始为1，方便计算偏移量
        end
      end
      else begin
        o_cache_axi_rdata <= i_axi_io_rdata;    // 保存数据
        o_cache_axi_ack   <= 1;   // 完成
        o_axi_io_valid    <= 0;   // 关闭axi请求
      end
    end
    else begin
      // 触发采样
      if (axi_start) begin
        // 仅在第一次进入时修改地址
        if (!o_axi_io_valid) begin
          if (is_flash) begin
            o_axi_io_addr <= i_cache_axi_addr & (~64'h3);   // 传输起始地址，4字节对齐
            o_axi_io_wdata    <= i_cache_axi_wdata;         // 准备数据
          end
          else begin
            o_axi_io_addr <= i_cache_axi_addr & (~64'h3F);  // 传输起始地址，64字节对齐
            o_axi_io_wdata    <= i_cache_axi_wdata;         // 准备数据
          end
        end
        o_axi_io_valid <= 1;
      end
      // 清除信号   
      o_cache_axi_ack    <= 0;
    end
  end
end

// assign o_cache_axi_rdata = i_axi_io_rdata;
// assign o_axi_io_wdata = i_cache_axi_wdata;

endmodule

// ZhengpuShi

// Cache Basic Unit
// 仅支持对齐访问的Cache基本单元

/*
  Cache Disign (2021.09.08, by ZhengpuShi):
    [-] --- BASIC CONFIG
    [*] word_size = 32bit (4 bytes)             -- 指令是32bit的
    [*] block_size = 512bit (64 bytes)          -- 块大小，AXI总线burst最大传输8次*8字节=64字节
    [*] offset index bits = 6 (2^6 = 64)        -- 由块大小决定
    [*] cache bytes max = 4KB * 2               -- ICache/DCache各4KB
    [*] main memory bytes = 4GB = 2^32          -- 主存地址空间0~(4GB-1)
    [*] raw-memory width = 128bit               -- 后端决定
    [*] raw-memory depth = 64                   -- 后端决定
    [-] --- CACHE CONFIG，4路16组
    [*] cache ways = 4way                       -- 2/4/8/...
    [*] cache blocks per way = 16blocks         -- 8/16/32/...
    [*] cache block index bits = 4 (2^4 = 16)   -- 由块数决定
    [*] cache data bytes = 2 * 16 * 64B = 2KB   -- 由路数、块数、块大小决定
    [*] bits_mem_tag = 32 - 4 - 6 = 22          -- 主存标记，由主存大小、cache块数、块大小决定
    [*] bits_v = 1 (data valid)                 -- 为1表示有效
    [*] bits_d = 1 (data dirty)                 -- 为1表示脏数据，在替换时需要写入主存
    [*] bits_s = 2 (sequence)                   -- FIFO策略：初始化各路分别为0,1,2,3；替换时换掉为0的一路；并将顺序循环移动。
    [-] --- CACHE STORAGE，分两块存储，数据与标记。 
    [*] cache_data_bits = 4 * (16 * 512) = 32Kbit = 4KB
    [*] cache_info_bits = 4 * (16 * (2 + 1 + 1 + 22)) = 1664bit = 208B 
    [*] --- ADDRESS TRANSFORM
      1. 主存地址 32bit：
        以字节为单位；共2^32个单元；低6位是块内偏移；接着4位是块号；接着22位是tag
      2. 主存数据 8/16/32/64bit
        可以有多种访问方式
      3. cache_data地址:
        每一路用1片RAM，1KB=1024bit，总共有8片，ICache/DCache各4片，以下都是单独一路的配置。
        共4路                            -- 2bit
        以128bit为1行；共64行；           -- 6bit                
        每4个单元组成512bit的一个块；       -- 2bit         
        共16个块                         -- 4bit
      3. cache_info地址：
        共4路                            -- 2bit
        每路又分16行                      -- 4bit
        每行21bit，从高位到低位，2bit顺序，1bit脏位，1bit有效位，17bit主存标记
      4. 支持不对齐访问，需要处理跨行、跨页访问
        可能产生跨行、跨页，使用更高层的调用方式，产生两次cache调用。
        1>. byte访问不会产生跨页
        2>. half访问，可能产生1字节的跨页
        3>. word访问，可能产生1~3字节的跨页
        4>. dword访问，可能产生1~7字节的跨页
        所以，在本模块内，访问地址、访问字节数一定是有效的，不做检查。
*/


module ysyx_210544_cache_basic (
  input   wire                clk,
  input   wire                rst,
  input   wire  [`BUS_64]     i_cache_basic_addr,         // 地址。保证与操作数大小相加后不能跨界。
  input   wire  [`BUS_64]     i_cache_basic_wdata,        // 写入的数据
  input   wire  [2 : 0]       i_cache_basic_bytes,        // 操作的字节数: 0~7表示1~8字节
	input   wire                i_cache_basic_op,           // 操作: 0:read, 1:write
	input   wire                i_cache_basic_req,          // 请求
  output  reg   [`BUS_64]     o_cache_basic_rdata,        // 读出的数据
	output  reg                 o_cache_basic_ack,          // 应答

  // AXI interface
  input   wire  [511:0]       i_axi_io_rdata,
  input   wire                i_axi_io_ready,
  output  wire                o_axi_io_valid,
  output  wire                o_axi_io_op,
  output  wire  [511:0]       o_axi_io_wdata,
  output  wire  [63:0]        o_axi_io_addr,
  output  wire  [2:0]         o_axi_io_size,
  output  wire  [7:0]         o_axi_io_blks
);


`define WAYS        4         // 路数
`define BLKS        16        // 块数
`define BUS_WAYS    0:3       // 各路的总线。4路

// =============== 物理地址解码 ===============

wire  [63: 0]                 user_blk_aligned_bytes;     // 用户地址的按块对齐地址(按字节)（64字节对齐，低6位为0）
reg   [63: 0]                 user_wmask;                 // 用户数据的写入掩码，由bytes决定，高电平有效
wire  [3 : 0]                 mem_blkno;                  // mem块号，0~15
wire  [5 : 0]                 mem_offset_bytes;           // mem块内偏移(按字节)，0~63
wire  [8 : 0]                 mem_offset_bits;            // mem块内偏移(按位)，0~511
wire  [21: 0]                 mem_tag;                    // mem标记

assign user_blk_aligned_bytes = {32'd0, i_cache_basic_addr[31:6], 6'd0};

always @(*) begin
  case (i_cache_basic_bytes)
    0:    user_wmask = 64'hFF;
    1:    user_wmask = 64'hFFFF;
    2:    user_wmask = 64'hFFFF_FF;
    3:    user_wmask = 64'hFFFF_FFFF;
    4:    user_wmask = 64'hFFFF_FFFF_FF;
    5:    user_wmask = 64'hFFFF_FFFF_FFFF;
    6:    user_wmask = 64'hFFFF_FFFF_FFFF_FF;
    7:    user_wmask = 64'hFFFF_FFFF_FFFF_FFFF;
    default: user_wmask = 0;
  endcase
end

assign mem_offset_bytes = i_cache_basic_addr[5:0];
assign mem_offset_bits = {3'b0, i_cache_basic_addr[5:0]} << 3;
assign mem_blkno = i_cache_basic_addr[9:6];
assign mem_tag = i_cache_basic_addr[31:10];


// =============== Cache Info 缓存信息 ===============

wire  [5 : 0]                 c_data_lineno;                      // cache数据行号(0~63)
wire  [3 : 0]                 c_offset_bytes;                     // cache行内偏移(按字节)(0~15)
wire  [6 : 0]                 c_offset_bits;                      // cache行内偏移(按位)(0~127)
wire  [127:0]                 c_wdata;                            // cache行要写入的数据
wire  [127:0]                 c_wmask;                            // cache行要写入的掩码

assign c_data_lineno = i_cache_basic_addr[9:4];
assign c_offset_bytes = mem_offset_bits[6:3]; 
assign c_offset_bits = mem_offset_bits[6:0];
assign c_wmask = {64'd0, user_wmask} << c_offset_bits;
assign c_wdata = {64'd0, i_cache_basic_wdata} << c_offset_bits;

`define c_tag_BUS             21:0          // cache的tag所在的总线 
`define c_v_BUS               22            // cache的v所在的总线 
`define c_d_BUS               23            // cache的d所在的总线 
`define c_s_BUS               25:24         // cache的s所在的总线

reg   [25 : 0]                cache_info[`BUS_WAYS][0:`BLKS-1];   // cache信息块
wire                          c_v[`BUS_WAYS];                     // cache valid bit 有效位，1位有效
wire                          c_d[`BUS_WAYS];                     // cache dirty bit 脏位，1为脏
wire  [1 : 0]                 c_s[`BUS_WAYS];                     // cache seqence bit 顺序位，越大越需要先被替换走
wire  [21: 0]                 c_tag[`BUS_WAYS];                   // cache标记

// cache_info
generate
  for (genvar way = 0; way < `WAYS; way += 1) begin
    parameter [1:0] w = way;
    for (genvar i = 0; i < `BLKS; i += 1) begin
      always @(posedge clk) begin
        if (rst) begin
          cache_info[w][i] <= {w, 1'b0, 1'b0, 22'b0};
        end
      end
    end
  end
endgenerate

// c_tag, c_v, c_d, c_s
generate
  for (genvar way = 0; way < `WAYS; way += 1) begin
    parameter [1:0] w = way;
    assign c_tag[w]   = cache_info[w][mem_blkno][`c_tag_BUS];
    assign c_v[w]     = cache_info[w][mem_blkno][`c_v_BUS];
    assign c_d[w]     = cache_info[w][mem_blkno][`c_d_BUS];
    assign c_s[w]     = cache_info[w][mem_blkno][`c_s_BUS];
  end
endgenerate


// =============== cache选中 ===============

wire                          hit[`BUS_WAYS];     // 各路是否命中
wire                          hit_any;            // 是否有任意一路命中？
wire [1:0]                    wayID_smin;         // s最小的是哪一路？
wire [1:0]                    wayID_hit;          // 已命中的是哪一路（至多有一路命中） 
wire [1:0]                    wayID_select;       // 选择了哪一路？方法：若命中则就是命中的那一路；否则选择smax所在的那一路

// hit
generate
  for (genvar way = 0; way < `WAYS; way += 1) begin
    parameter [1:0] w = way;
    assign hit[w] = c_v[w] && (c_tag[w] == mem_tag);
  end
endgenerate

assign hit_any = hit[0] | hit[1] | hit[2] | hit[3];
assign wayID_hit = (hit[1] ? 1 : 0) | (hit[2] ? 2 : 0) | (hit[3] ? 3 : 0);
assign wayID_smin = (c_s[1] == 0 ? 1 : 0) | (c_s[2] == 0 ? 2 : 0) | (c_s[3] == 0 ? 3 : 0);
assign wayID_select = hit_any ? wayID_hit : wayID_smin;


// =============== Cache Data 缓存数据 ===============

// 根据实际硬件模型设置有效电平
parameter bit CHIP_DATA_CEN = 0;        // cen有效的电平
parameter bit CHIP_DATA_WEN = 0;        // wen有效的电平
parameter bit CHIP_DATA_WMASK_EN = 0;   // 写掩码有效的电平

reg                           chip_data_cen[`BUS_WAYS];               // RAM 使能，低电平有效
reg                           chip_data_wen[`BUS_WAYS];               // RAM 写使能，低电平有效
reg   [5  : 0]                chip_data_addr[`BUS_WAYS];              // RAM 地址
reg   [127: 0]                chip_data_wdata[`BUS_WAYS];             // RAM 写入数据
reg   [127: 0]                chip_data_wmask[`BUS_WAYS];             // RAM 写入掩码
wire  [127: 0]                chip_data_rdata[`BUS_WAYS];             // RAM 读出数据

// RAM instantiate
generate
  for (genvar way = 0; way < `WAYS; way += 1) begin: gen_cache_data
    parameter [1:0] w = way;
    ysyx_210544_S011HD1P_X32Y2D128_BW  chip_data(
      .CLK                        (clk                  ),
      .CEN                        (chip_data_cen[w]     ),
      .WEN                        (chip_data_wen[w]     ),
      .A                          (chip_data_addr[w]    ),
      .D                          (chip_data_wdata[w]   ),
      .BWEN                       (chip_data_wmask[w]   ),
      .Q                          (chip_data_rdata[w]   )
    );
  end
endgenerate

// cen, addr
generate
  for (genvar way = 0; way < `WAYS; way += 1) begin
    parameter [1:0] w = way;
    always @(posedge clk) begin
      if (rst) begin
        chip_data_cen[w] <= !CHIP_DATA_CEN;
        chip_data_wen[w] <= !CHIP_DATA_WEN;
      end
    end
  end
endgenerate


// =============== 状态机 ===============
//  英文名称          中文名称             含义
//  IDLE            空闲                 无活动。有用户请求则进入 READY / STORE_FROM_RAM / LOAD_FROM_BUS 这三种情况
//  READY           就绪                  命中，则直接读写。读写完毕回到IDLE。
//  STORE_FROM_RAM  存储(从RAM读取数据)    不命中并选择脏的数据块，则需要写回。先以128bit为单位分4次从RAM读入数据，读取完毕跳转到 StoreToBUS
//  STORE_TO_BUS    存储(写入总线)         不命中并选择脏的数据块，则需要写回。再将512bit数据写入总线，写入完毕跳转到 LoadFromBUS
//  LOAD_FROM_BUS   加载(从总线读取数据)    不命中并选择不脏的数据块，则需要读入新数据。先从总线读取512bit数据，读取完毕跳转到 LoadToRAM
//  LOAD_TO_RAM     加载(写入RAM)         不命中并选择不脏的数据块，则需要读入新数据。再以128bit为单位分4次写入RAM，写入完毕跳转到READY
parameter [2:0] STATE_IDLE              = 3'd0;
parameter [2:0] STATE_READY             = 3'd1;
parameter [2:0] STATE_STORE_FROM_RAM    = 3'd2;
parameter [2:0] STATE_STORE_TO_BUS      = 3'd3;
parameter [2:0] STATE_LOAD_FROM_BUS     = 3'd4;
parameter [2:0] STATE_LOAD_TO_RAM       = 3'd5;

reg [2:0] state;
// wire state_idle             = state == STATE_IDLE;
// wire state_ready            = state == STATE_READY;
// wire state_store_from_ram   = state == STATE_STORE_FROM_RAM;
// wire state_store_to_bus     = state == STATE_STORE_TO_BUS;
// wire state_load_from_bus    = state == STATE_LOAD_FROM_BUS;
// wire state_load_to_ram      = state == STATE_LOAD_TO_RAM;

always @(posedge clk) begin
    if (rst) begin
        state <= STATE_IDLE;
    end
    else begin
      case (state)
          STATE_IDLE:   begin
            if (i_cache_basic_req) begin
              if (hit_any)              state <= STATE_READY;
              else begin
                if (c_d[wayID_select])  state <= STATE_STORE_FROM_RAM;
                else                    state <= STATE_LOAD_FROM_BUS;
              end
            end
          end
          
          STATE_READY:  begin
            if (hs_cache) begin
              // 处理剩余的读写请求
              state <= STATE_IDLE;
            end
          end

          STATE_STORE_FROM_RAM:     begin
            if (hs_ramread) begin
              state <= STATE_STORE_TO_BUS;
            end
          end

          STATE_STORE_TO_BUS:     begin
            if (hs_cache_axi) begin
              state <= STATE_LOAD_FROM_BUS;
            end
          end

          STATE_LOAD_FROM_BUS: begin
            if (hs_cache_axi) begin
              state <= STATE_LOAD_TO_RAM;
            end
          end

          STATE_LOAD_TO_RAM: begin
            if (hs_ramwrite) begin
              state <= STATE_READY;
            end
          end

          default: ;
      endcase
    end
end


// =============== 处理用户请求 ===============

reg   [2:0]         ram_op_cnt;                 // RAM操作计数器(0~3表示1~4次，剩余的位数用于大于4的计数)
wire  [8:0]         ram_op_offset_128;          // RAM操作的128位偏移量（延迟2个时钟周期后输出）
wire                hs_cache;                   // cache操作 握手
wire                hs_cache_axi;               // cache_axi操作 握手
wire                hs_ramwrite;                // ram操作 握手（完成4行写入）
wire                hs_ramread;                 // ram操作 握手（完成4行读取）
wire                hs_ramline;                 // ram操作 握手（完成指定1行读写）
reg   [127: 0]      rdata_line;                 // 读取一行数据
reg   [63: 0]       rdata_out;                  // 输出的数据

assign ram_op_offset_128 = ({6'd0, ram_op_cnt} - 2) << 7;
assign hs_cache = i_cache_basic_req & o_cache_basic_ack;
assign hs_cache_axi = o_cache_axi_req & i_cache_axi_ack;
assign hs_ramwrite = ram_op_cnt == 3'd4;
assign hs_ramread = ram_op_cnt == 3'd6;
assign hs_ramline = ram_op_cnt == 3'd3;
assign rdata_line = chip_data_rdata[wayID_select];
assign rdata_out = rdata_line[c_offset_bits +:64] & user_wmask;

always @(posedge clk) begin
  if (rst) begin
    o_cache_basic_ack <= 0;
  end
  else begin
    case (state)
      STATE_IDLE: begin;
        o_cache_basic_ack <= 0;
      end

      STATE_READY: begin
        if (!hs_cache) begin
          if (i_cache_basic_op == `REQ_READ) begin
            // 读取RAM一个单元
            if (!hs_ramline) begin
              chip_data_cen[wayID_select] <= CHIP_DATA_CEN;
              chip_data_addr[wayID_select] <= c_data_lineno;
              ram_op_cnt <= ram_op_cnt + 1;
            end
            else begin
              chip_data_cen[wayID_select] <= !CHIP_DATA_CEN;
              o_cache_basic_rdata <= rdata_out; // ToDo: 在跳转指令时，这一步可以用组合电路实现，更早得到新的数据
              o_cache_basic_ack <= 1;
            end
          end
          else begin
            // 写入RAM一个单元
            if (!hs_ramline) begin
              chip_data_cen[wayID_select] <= CHIP_DATA_CEN;
              chip_data_wen[wayID_select] <= CHIP_DATA_WEN;
              chip_data_addr[wayID_select] <= c_data_lineno;
              chip_data_wdata[wayID_select] <= c_wdata;
              chip_data_wmask[wayID_select] <= ~c_wmask;  // 芯片的写入掩码低电平有效，需要取反
              ram_op_cnt <= ram_op_cnt + 1;
            end
            else begin
              chip_data_cen[wayID_select] <= !CHIP_DATA_CEN;
              chip_data_wen[wayID_select] <= !CHIP_DATA_WEN;
              o_cache_basic_ack <= 1;
            end
            // cache更新记录
            cache_info[wayID_select][mem_blkno][`c_d_BUS]  <= 1;
          end
        end
        else begin
          ram_op_cnt <= 0;
        end
      end

      STATE_LOAD_FROM_BUS: begin
        // 读取主存一个块
        o_cache_axi_req <= 1;
        o_cache_axi_addr <= user_blk_aligned_bytes;
        o_cache_axi_op <= `REQ_READ;
        if (hs_cache_axi) begin
          o_cache_axi_req <= 0;
        end
      end

      STATE_LOAD_TO_RAM: begin
        // 写入RAM一个块
        if (!hs_ramwrite) begin
          ram_op_cnt <= ram_op_cnt + 1;
          // 写入cache数据一行
          chip_data_cen[wayID_select] <= CHIP_DATA_CEN;
          chip_data_wen[wayID_select] <= CHIP_DATA_WEN;
          chip_data_addr[wayID_select] <= {{2'd0, mem_blkno} << 2} | {4'd0, ram_op_cnt[1:0]};
          chip_data_wdata[wayID_select] <= i_cache_axi_rdata[{{7'd0,ram_op_cnt[1:0]} << 7}+:128];   // 128的倍数
          chip_data_wmask[wayID_select] <= {128{CHIP_DATA_WMASK_EN}};
        end
        else begin
          ram_op_cnt <= 0;
          chip_data_cen[wayID_select] <= !CHIP_DATA_CEN;
          chip_data_wen[wayID_select] <= !CHIP_DATA_WEN;
          // 更新cache记录一行的 tag,v,d 位
          cache_info[wayID_select][mem_blkno][`c_tag_BUS]      <= mem_tag; // c_tag
          cache_info[wayID_select][mem_blkno][`c_v_BUS]        <= 1;       // 有效位
          cache_info[wayID_select][mem_blkno][`c_d_BUS]        <= 0;       // 脏位
          // 更新cache记录四行的 s 位，循环移动
          cache_info[3][mem_blkno][`c_s_BUS] <= cache_info[2][mem_blkno][`c_s_BUS];
          cache_info[2][mem_blkno][`c_s_BUS] <= cache_info[1][mem_blkno][`c_s_BUS];
          cache_info[1][mem_blkno][`c_s_BUS] <= cache_info[0][mem_blkno][`c_s_BUS];
          cache_info[0][mem_blkno][`c_s_BUS] <= cache_info[3][mem_blkno][`c_s_BUS];
        end
      end

      STATE_STORE_FROM_RAM: begin
        // 读取RAM一个块
        if (!hs_ramread) begin
          ram_op_cnt <= ram_op_cnt + 1;
          // RAM控制信号在前4个周期有效
          if (ram_op_cnt <= 3) begin
            chip_data_cen[wayID_select] <= CHIP_DATA_CEN;
            chip_data_addr[wayID_select] <= {{2'd0, mem_blkno} << 2} | {4'd0, ram_op_cnt[1:0]};
          end
          // 延迟2个周期后保存RAM读出的数据
          if (ram_op_cnt >= 2) begin
            o_cache_axi_wdata[ram_op_offset_128+:128] <= chip_data_rdata[wayID_select];   // 128的倍数
          end
        end
        else begin
          ram_op_cnt <= 0;
          chip_data_cen[wayID_select] <= !CHIP_DATA_CEN;
          // 更新cache记录一行的 d 位。
          cache_info[wayID_select][mem_blkno][`c_d_BUS]        <= 0;       // 脏位
        end
      end

      STATE_STORE_TO_BUS: begin
        // 写入主存一个块
        o_cache_axi_req <= 1;
        o_cache_axi_addr <= {32'd0, c_tag[wayID_select], mem_blkno, 6'd0 };
        o_cache_axi_op <= `REQ_WRITE;

        if (hs_cache_axi) begin
          o_cache_axi_wdata <= 0;
          o_cache_axi_req <= 0;
        end
      end

      default:;
    endcase
  end
end

// =============== cache_axi 从机端，请求传输数据 ===============

reg                           o_cache_axi_req;             // 请求
reg   [63 : 0]                o_cache_axi_addr;            // 存储器地址（字节为单位），64字节对齐，低6位为0。
reg                           o_cache_axi_op;              // 操作类型：0读取，1写入
reg   [511 : 0]               o_cache_axi_wdata;           // 要写入的数据
wire  [511 : 0]               i_cache_axi_rdata;           // 已读出的数据
wire                          i_cache_axi_ack;             // 应答

ysyx_210544_cache_axi Cache_axi(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_axi_req            (o_cache_axi_req            ),
	.i_cache_axi_addr           (o_cache_axi_addr           ),
	.i_cache_axi_op             (o_cache_axi_op             ),
	.i_cache_axi_wdata          (o_cache_axi_wdata          ),
	.o_cache_axi_rdata          (i_cache_axi_rdata          ),
	.o_cache_axi_ack            (i_cache_axi_ack            ),

  .i_axi_io_ready             (i_axi_io_ready             ),
  .i_axi_io_rdata             (i_axi_io_rdata             ),
  .o_axi_io_op                (o_axi_io_op                ),
  .o_axi_io_valid             (o_axi_io_valid             ),
  .o_axi_io_wdata             (o_axi_io_wdata             ),
  .o_axi_io_addr              (o_axi_io_addr              ),
  .o_axi_io_size              (o_axi_io_size              ),
  .o_axi_io_blks              (o_axi_io_blks              )
);

wire _unused_ok = &{1'b0,
  i_cache_basic_addr[63:32],
  mem_offset_bytes,
  mem_offset_bits[8:7],
  c_offset_bytes,
  1'b0};

endmodule

// ZhengpuShi

// Cache Core Unit
// 支持不对齐访问的Cache核心模块
// 封装了 cache_basic，将不对齐的访问转换为1~2次cache访问。


module ysyx_210544_cache_core (
  input   wire                clk,
  input   wire                rst,
  input   wire  [`BUS_64]     i_cache_core_addr,          // 地址。地址与操作数相加后可以跨界。
  input   wire  [`BUS_64]     i_cache_core_wdata,         // 写入的数据
  input   wire  [2 : 0]       i_cache_core_bytes,         // 操作的字节数: 0~7表示1~8字节
	input   wire                i_cache_core_op,            // 操作: 0:read, 1:write
	input   wire                i_cache_core_req,           // 请求
  output  reg   [`BUS_64]     o_cache_core_rdata,         // 读出的数据
	output  reg                 o_cache_core_ack,           // 应答

  // AXI interface
  input   wire  [511:0]       i_axi_io_rdata,
  input   wire                i_axi_io_ready,
  output  wire                o_axi_io_valid,
  output  wire                o_axi_io_op,
  output  wire  [511:0]       o_axi_io_wdata,
  output  wire  [63:0]        o_axi_io_addr,
  output  wire  [2:0]         o_axi_io_size,
  output  wire  [7:0]         o_axi_io_blks
);

// =============== cache 从机端 ===============

reg   [63 : 0]                o_cache_basic_addr;         // 存储器地址（字节为单位），64字节对齐，低6位为0。
reg   [63 : 0]                o_cache_basic_wdata;        // 要写入的数据
reg   [2  : 0]                o_cache_basic_bytes;        // 字节数
wire                          o_cache_basic_op;           // 操作类型：0读取，1写入
reg                           o_cache_basic_req;          // 请求
wire  [63 : 0]                i_cache_basic_rdata;        // 已读出的数据
reg                           i_cache_basic_ack;          // 应答

assign o_cache_basic_op = i_cache_core_op;

ysyx_210544_cache_basic Cache_basic(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_basic_addr         (o_cache_basic_addr         ),
	.i_cache_basic_wdata        (o_cache_basic_wdata        ),
	.i_cache_basic_bytes        (o_cache_basic_bytes        ),
	.i_cache_basic_op           (o_cache_basic_op           ),
	.i_cache_basic_req          (o_cache_basic_req          ),
	.o_cache_basic_rdata        (i_cache_basic_rdata        ),
	.o_cache_basic_ack          (i_cache_basic_ack          ),

  .i_axi_io_ready             (i_axi_io_ready             ),
  .i_axi_io_rdata             (i_axi_io_rdata             ),
  .o_axi_io_op                (o_axi_io_op                ),
  .o_axi_io_valid             (o_axi_io_valid             ),
  .o_axi_io_wdata             (o_axi_io_wdata             ),
  .o_axi_io_addr              (o_axi_io_addr              ),
  .o_axi_io_size              (o_axi_io_size              ),
  .o_axi_io_blks              (o_axi_io_blks              )
);


// =============== 处理跨行问题 ===============

wire  [59:0]                  i_addr_high;                // 输入地址的高60位
wire  [3:0]                   i_addr_4;                   // 输入地址的低4位 (0~15)
wire  [3:0]                   i_bytes_4;                  // 输入字节数扩展为4位

assign i_addr_high = i_cache_core_addr[63:4];
assign i_addr_4 = i_cache_core_addr[3:0];
assign i_bytes_4 = {1'd0, i_cache_core_bytes};

wire                          en_second;                  // 第二次操作使能
wire  [2 : 0]                 bytes[0:1];                 // 字节数
wire  [63: 0]                 addr[0:1];                  // 地址
wire  [63: 0]                 wdata[0:1];                 // 写数据
reg   [63: 0]                 rdata[0:1];                 // 读数据

assign en_second = i_addr_4 + i_bytes_4 < i_addr_4;
assign bytes[0] = en_second ? {4'd15 - i_addr_4}[2:0] : i_cache_core_bytes;
assign bytes[1] = en_second ? {i_addr_4 + i_bytes_4}[2:0] : 0;
assign addr[0] = i_cache_core_addr;
assign addr[1] = {i_addr_high + 60'd1, 4'd0};
assign wdata[0] = i_cache_core_wdata;
assign wdata[1] = i_cache_core_wdata >> (({3'd0,bytes[0]} + 1) << 3);

wire hs_cache = i_cache_basic_ack & o_cache_basic_req;

assign o_cache_basic_addr = (index == 0) ? addr[0] : addr[1];
assign o_cache_basic_bytes = (index == 0) ? bytes[0] : bytes[1];
assign o_cache_basic_wdata = (index == 0) ? wdata[0] : wdata[1];

reg   index;      // 操作的序号：0,1表示两个阶段
always @(posedge clk) begin
  if (rst) begin
    index <= 0;
    o_cache_basic_req <= 0;
  end
  else begin
    // 发现用户请求
    if (i_cache_core_req & !o_cache_core_ack) begin
      // 第一次请求
      if (index == 0) begin
        // 发出请求
        if (!hs_cache) begin
          o_cache_basic_req <= 1;
        end
        // 收到回应
        else begin
          o_cache_basic_req <= 0;
          rdata[0] <= i_cache_basic_rdata;
          // 启动第二次请求，或者结束任务
          if (en_second) begin
            index <= 1;
          end
          else begin
            o_cache_core_rdata <= i_cache_basic_rdata;
            o_cache_core_ack <= 1;
          end
        end
      end
      // 第二次请求
      else if (index == 1) begin
        // 发出请求
        if (!hs_cache) begin
          o_cache_basic_req <= 1;
        end
        // 收到回应
        else begin
          rdata[1] <= i_cache_basic_rdata;
          o_cache_core_rdata <= rdata[0] + (i_cache_basic_rdata << ((bytes[0] + 1) << 3));
          o_cache_basic_req <= 0;
          o_cache_core_ack <= 1;
        end
      end
    end
    // 结束应答
    else begin
      index <= 0;
      o_cache_core_ack <= 0;
    end
  end
end


endmodule

// ZhengpuShi

// No Cache Unit
// 没有Cache的AXI总线访问，比如UART。其实Flash也可以用。


module ysyx_210544_cache_nocache (
  input   wire                clk,
  input   wire                rst,
  input   wire  [`BUS_64]     i_cache_nocache_addr,          // 地址
  input   wire  [`BUS_64]     i_cache_nocache_wdata,         // 写入的数据
  input   wire  [2 : 0]       i_cache_nocache_bytes,         // 操作的字大小: 0~7表示1~8字节
	input   wire                i_cache_nocache_op,            // 操作: 0:read, 1:write
	input   wire                i_cache_nocache_req,           // 请求
  output  reg   [`BUS_64]     o_cache_nocache_rdata,         // 读出的数据
	output  reg                 o_cache_nocache_ack,           // 应答

  // AXI interface
  input   wire  [511:0]       i_axi_io_rdata,
  input   wire                i_axi_io_ready,
  output  wire                o_axi_io_valid,
  output  wire                o_axi_io_op,
  output  wire  [511:0]       o_axi_io_wdata,
  output  wire  [63:0]        o_axi_io_addr,
  output  wire  [2:0]         o_axi_io_size,
  output  wire  [7:0]         o_axi_io_blks
);

wire hs_axi_io = o_axi_io_valid & i_axi_io_ready;

reg [2:0] nocache_size;
always @(*) begin
  case (i_cache_nocache_bytes)
    3'b000: nocache_size = `SIZE_B;
    3'b001: nocache_size = `SIZE_H;
    3'b011: nocache_size = `SIZE_W;
    3'b111: nocache_size = `SIZE_D;
    default: nocache_size = `SIZE_B;  // 这种情况应该是不支持的。
  endcase
end

always @(posedge clk) begin
  if (rst) begin
    o_axi_io_valid <= 0;
  end
  else begin
    // 发现用户请求
    if (i_cache_nocache_req & !o_cache_nocache_ack) begin
      // 发出请求
      if (!hs_axi_io) begin
        o_axi_io_addr   <= i_cache_nocache_addr;
        o_axi_io_blks   <= 0;
        o_axi_io_op     <= i_cache_nocache_op;
        o_axi_io_size   <= nocache_size;
        o_axi_io_wdata  <= {448'b0, i_cache_nocache_wdata};
        o_axi_io_valid  <= 1;
      end
      // 收到回应
      else begin
        o_axi_io_valid  <= 0;
        o_cache_nocache_rdata <= i_axi_io_rdata[63:0];
        o_cache_nocache_ack   <= 1;
      end
    end
    // 结束应答
    else begin
      o_cache_nocache_ack <= 0;
    end
  end
end

wire _unused_ok = &{1'b0,
  i_axi_io_rdata[511:64],
  1'b0};

endmodule

// ZhengpuShi

// Cache Interface
// 对ICache和DCache的统一


module ysyx_210544_cache(
    input                     clk,
    input                     rst,
    
    // ICache
    input   wire              i_icache_req,
    input   wire  [63:0]      i_icache_addr,
    output  wire              o_icache_ack,
    output  wire  [31:0]      o_icache_rdata,

    // DCache
    input   wire              i_dcache_req,
    input   wire  [63:0]      i_dcache_addr,
    input   wire              i_dcache_op,
    input   wire  [2 :0]      i_dcache_bytes,
    input   wire  [63:0]      i_dcache_wdata,
    output  wire              o_dcache_ack,
    output  wire  [63:0]      o_dcache_rdata,

    // AXI interface
    input   wire  [511:0]     i_axi_io_rdata,
    input   wire              i_axi_io_ready,
    output  wire              o_axi_io_valid,
    output  wire              o_axi_io_op,
    output  wire  [511:0]     o_axi_io_wdata,
    output  wire  [63:0]      o_axi_io_addr,
    output  wire  [2:0]       o_axi_io_size,
    output  wire  [7:0]       o_axi_io_blks
);

/////////////////////////////////////////////////
// 数据通路选择

// 0x1000_0000 ~ END, 是UART
// 0x3000_0000 ~ END, 是Flash
// 0x8000_0000 ~ END, 是主存
wire iaddr_UART   = i_icache_req & i_icache_addr[31:28] == 4'h1;
wire iaddr_FLASH  = i_icache_req & i_icache_addr[31:28] == 4'h3;
wire iaddr_MEM    = i_icache_req & i_icache_addr[31:28] == 4'h8;

wire daddr_UART   = i_dcache_req & i_dcache_addr[31:28] == 4'h1;
wire daddr_FLASH  = i_dcache_req & i_dcache_addr[31:28] == 4'h3;
wire daddr_MEM    = i_dcache_req & i_dcache_addr[31:28] == 4'h8;

// 注意： FLASH可选的使用Cache或不使用Cache，Cache已做适配。
wire ch_icache    = iaddr_MEM | iaddr_FLASH;
wire ch_dcache    = daddr_MEM | daddr_FLASH;
wire ch_nocache   = iaddr_UART | daddr_UART;// | iaddr_FLASH | daddr_FLASH;


/////////////////////////////////////////////////
// Instruction Cache

wire  [63:0]      icache_rdata;
wire              icache_ack;
wire              icache_axi_io_valid;
wire              icache_axi_io_op;
wire  [511:0]     icache_axi_io_wdata;
wire  [63:0]      icache_axi_io_addr;
wire  [2:0]       icache_axi_io_size;
wire  [7:0]       icache_axi_io_blks;

ysyx_210544_cache_core ICache(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_core_addr          (i_icache_addr              ),
	.i_cache_core_wdata         (0                          ),
	.i_cache_core_bytes         (3                          ),
	.i_cache_core_op            (`REQ_READ                  ),
	.i_cache_core_req           (ch_icache ? i_icache_req : 0),
	.o_cache_core_rdata         (icache_rdata               ),
	.o_cache_core_ack           (icache_ack                 ),

  .i_axi_io_ready             (ch_icache ? i_axi_io_ready : 0        ),
  .i_axi_io_rdata             (ch_icache ? i_axi_io_rdata : 0        ),
  .o_axi_io_op                (icache_axi_io_op           ),
  .o_axi_io_valid             (icache_axi_io_valid        ),
  .o_axi_io_wdata             (icache_axi_io_wdata        ),
  .o_axi_io_addr              (icache_axi_io_addr         ),
  .o_axi_io_size              (icache_axi_io_size         ),
  .o_axi_io_blks              (icache_axi_io_blks         )
);


/////////////////////////////////////////////////
// Data Cache

wire [63:0]       dcache_rdata;
wire              dcache_ack;
wire              dcache_axi_io_valid;
wire              dcache_axi_io_op;
wire  [511:0]     dcache_axi_io_wdata;
wire  [63:0]      dcache_axi_io_addr;
wire  [2:0]       dcache_axi_io_size;
wire  [7:0]       dcache_axi_io_blks;

ysyx_210544_cache_core DCache(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_core_addr          (i_dcache_addr              ),
	.i_cache_core_wdata         (i_dcache_wdata             ),
	.i_cache_core_bytes         (i_dcache_bytes             ),
	.i_cache_core_op            (i_dcache_op                ),
	.i_cache_core_req           (ch_dcache ? i_dcache_req : 0),
	.o_cache_core_rdata         (dcache_rdata               ),
	.o_cache_core_ack           (dcache_ack                 ),

  .i_axi_io_ready             (ch_dcache ? i_axi_io_ready : 0        ),
  .i_axi_io_rdata             (ch_dcache ? i_axi_io_rdata : 0        ),
  .o_axi_io_op                (dcache_axi_io_op           ),
  .o_axi_io_valid             (dcache_axi_io_valid        ),
  .o_axi_io_wdata             (dcache_axi_io_wdata        ),
  .o_axi_io_addr              (dcache_axi_io_addr         ),
  .o_axi_io_size              (dcache_axi_io_size         ),
  .o_axi_io_blks              (dcache_axi_io_blks         )
);


/////////////////////////////////////////////////
// NoCache, access bus directly
  
wire              nocache_req;
wire  [63:0]      nocache_addr;
wire              nocache_op;
wire  [2 :0]      nocache_bytes;
wire  [63:0]      nocache_wdata;
wire              nocache_ack;
wire  [63:0]      nocache_rdata;

wire              nocache_axi_io_valid;
wire              nocache_axi_io_op;
wire  [511:0]     nocache_axi_io_wdata;
wire  [63:0]      nocache_axi_io_addr;
wire  [2:0]       nocache_axi_io_size;
wire  [7:0]       nocache_axi_io_blks;

ysyx_210544_cache_nocache NoCache(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_cache_nocache_addr       (nocache_addr               ),
	.i_cache_nocache_wdata      (nocache_wdata              ),
	.i_cache_nocache_bytes      (nocache_bytes              ),
	.i_cache_nocache_op         (nocache_op                 ),
	.i_cache_nocache_req        (ch_nocache ? nocache_req : 0),
	.o_cache_nocache_rdata      (nocache_rdata              ),
	.o_cache_nocache_ack        (nocache_ack                ),

  .i_axi_io_ready             (ch_nocache ? i_axi_io_ready : 0        ),
  .i_axi_io_rdata             (ch_nocache ? i_axi_io_rdata : 0        ),
  .o_axi_io_op                (nocache_axi_io_op          ),
  .o_axi_io_valid             (nocache_axi_io_valid       ),
  .o_axi_io_wdata             (nocache_axi_io_wdata       ),
  .o_axi_io_addr              (nocache_axi_io_addr        ),
  .o_axi_io_size              (nocache_axi_io_size        ),
  .o_axi_io_blks              (nocache_axi_io_blks        )
);



/////////////////////////////////////////////////
// 信号互联

assign nocache_req      = ch_nocache ? (i_icache_req | i_dcache_req                     ) : 0;
assign nocache_addr     = ch_nocache ? (i_icache_req ? i_icache_addr  : i_dcache_addr   ) : 0;
assign nocache_wdata    = ch_nocache ? (i_icache_req ? 0              : i_dcache_wdata  ) : 0;
assign nocache_bytes    = ch_nocache ? (i_icache_req ? 3              : i_dcache_bytes  ) : 0;
assign nocache_op       = ch_nocache ? (i_icache_req ? `REQ_READ      : i_dcache_op     ) : 0;

assign o_axi_io_valid   = ch_icache ? icache_axi_io_valid   : (ch_dcache ? dcache_axi_io_valid  : nocache_axi_io_valid);
assign o_axi_io_op      = ch_icache ? icache_axi_io_op      : (ch_dcache ? dcache_axi_io_op     : nocache_axi_io_op);
assign o_axi_io_wdata   = ch_icache ? icache_axi_io_wdata   : (ch_dcache ? dcache_axi_io_wdata  : nocache_axi_io_wdata);
assign o_axi_io_addr    = ch_icache ? icache_axi_io_addr    : (ch_dcache ? dcache_axi_io_addr   : nocache_axi_io_addr);
assign o_axi_io_size    = ch_icache ? icache_axi_io_size    : (ch_dcache ? dcache_axi_io_size   : nocache_axi_io_size);
assign o_axi_io_blks    = ch_icache ? icache_axi_io_blks    : (ch_dcache ? dcache_axi_io_blks   : nocache_axi_io_blks);

assign o_icache_rdata   = ch_icache ? icache_rdata[31:0] : nocache_rdata[31:0];
assign o_icache_ack     = ch_icache ? icache_ack         : nocache_ack        ;

assign o_dcache_rdata   = ch_dcache ? dcache_rdata       : nocache_rdata      ;
assign o_dcache_ack     = ch_dcache ? dcache_ack         : nocache_ack        ;

wire _unused_ok = &{1'b0,
  icache_rdata[63:32],
  1'b0};

endmodule

// ZhengpuShi

// 带有缓冲区的 putch 改进版，在收到 \n 时输出，否则存入缓冲区


module ysyx_210544_putch(
  input   wire                  clk,
  input   wire                  rst,
  input   wire                  wen,
  input   wire  [`BUS_8]        wdata
);

parameter SIZE = 255;
reg [7:0]   cnt;
reg [7:0]   str [0 : SIZE - 1];

always @(posedge clk) begin
  if (rst) begin
    cnt = 0;
  end
  else begin
    if (wen) begin
      // 存入数据
      if (cnt < (SIZE - 1)) begin
        str[cnt] = wdata;
        cnt++;
      end
      // 输出
      if (wdata == 10) begin
        str[cnt] = 0;
        for (integer i = 0; (i < 255 && str[i] != 0); i++) begin
          $write("%s", str[i]);
        end
        cnt = 0;
      end
    end
  end
end


endmodule

// ZhengpuShi

// Simple RTC module


module ysyx_210544_rtc(
  input   wire              clk,
  input   wire              rst,

  input   wire              ren,
  output  [`BUS_64]         rdata
);

reg   [`BUS_64] clk_cnt     ;   // 内部计时器，用于控制秒的变化

reg   [15: 0]   year        ;   // year: 0000 ~ 9999    2^16-1=65535
reg   [3 : 0]   month       ;   // 2^4-1=15
reg   [4 : 0]   day         ;   // 2^5-1=31
reg   [5 : 0]   hour        ;   // 2^6-1=63
reg   [5 : 0]   minute      ;   // 2^6-1=63
reg   [5 : 0]   second      ;   // 2^6-1=63

wire  [`BUS_64] rtc_val = {21'b0, year, month, day, hour, minute, second};

// rtc simulate
always @(posedge clk) begin
  if (rst) begin
    year    <= 2021;
    month   <= 1;
    day     <= 2;
    hour    <= 3;
    minute  <= 4;
    second  <= 5;
  end
  else begin
    clk_cnt <= clk_cnt + 1;
    if (clk_cnt == `CLOCKS_PER_SECOND) begin
      clk_cnt <= 0;
      second <= second + 1;
      if (second == 60) begin
        second <= 0;

        minute <= minute + 1;
        if (minute == 60) begin
          minute <= 0;

          hour <= hour + 1;
          if (hour == 24) begin
            hour <= 0;

            day <= day + 1;
            if (day == 30) begin
              day <= 0;

              month <= month + 1;
              if (month == 12) begin
                month <= 0;

                year <= year + 1;
              end
            end
          end
        end
      end
    end
  end
end

// rtc read
assign rdata = (rst | !ren) ? 0 : rtc_val;

endmodule

// ZhengpuShi

// Core Local Interrupt Controller


module ysyx_210544_clint(
  input   wire                clk,
  input   wire                rst,

  input   wire [`BUS_64]      i_clint_addr,
  input   wire                i_clint_ren,
  output  reg  [`BUS_64]      o_clint_rdata,
  input   wire                i_clint_wen,
  input   reg  [`BUS_64]      i_clint_wdata,
  output  wire                o_clint_mtime_overflow
);

reg   [7:0]       reg_mtime_cnt;
reg   [`BUS_64]   reg_mtime;
reg   [`BUS_64]   reg_mtimecmp;

wire addr_mtime = i_clint_addr == `DEV_MTIME;
wire addr_mtimecmp = i_clint_addr == `DEV_MTIMECMP;

always @(posedge clk) begin
  if (rst) begin
    reg_mtime <= 0;
    reg_mtimecmp <= 5000;
  end
  else begin
    if (reg_mtime_cnt < 1) begin
      reg_mtime_cnt <= reg_mtime_cnt + 1;
    end
    else begin
      reg_mtime_cnt <= 0;
      reg_mtime <= reg_mtime + 20;
    end

    if (i_clint_wen & addr_mtimecmp) begin
      reg_mtimecmp <= i_clint_wdata;
    end
  end
end

assign o_clint_rdata = (rst | (!i_clint_ren)) ? 0 : 
  (addr_mtime ? reg_mtime :
  (addr_mtimecmp ? reg_mtimecmp : 0));

assign o_clint_mtime_overflow = reg_mtime > reg_mtimecmp;


endmodule

// ZhengpuShi


module ysyx_210544_regfile(
  input   wire                  clk,
  input   wire                  rst,

  input   wire  [`BUS_RIDX]     i_rs1,
  input   wire                  i_rs1_ren,
  input   wire  [`BUS_RIDX]     i_rs2,
  input   wire                  i_rs2_ren,
  input   wire  [`BUS_RIDX]     i_rd,
  input   wire                  i_rd_wen,
  input   wire  [`BUS_64]       i_rd_data,
  output  reg   [`BUS_64]       o_rs1_data,
  output  reg   [`BUS_64]       o_rs2_data,
  output  wire  [`BUS_64]       o_regs[0 : 31]
);

  // 32 registers
reg   [`BUS_64]   regs[0 : 31];

// register alias name
wire  [`BUS_64]   x00_zero  = regs[00];
wire  [`BUS_64]   x01_ra    = regs[01];
wire  [`BUS_64]   x02_sp    = regs[02];
wire  [`BUS_64]   x03_gp    = regs[03];
wire  [`BUS_64]   x04_tp    = regs[04];
wire  [`BUS_64]   x05_t0    = regs[05];
wire  [`BUS_64]   x06_t1    = regs[06];
wire  [`BUS_64]   x07_t2    = regs[07];
wire  [`BUS_64]   x08_s0    = regs[08];
wire  [`BUS_64]   x09_s1    = regs[09];
wire  [`BUS_64]   x10_a0    = regs[10];
wire  [`BUS_64]   x11_a1    = regs[11];
wire  [`BUS_64]   x12_a2    = regs[12];
wire  [`BUS_64]   x13_a3    = regs[13];
wire  [`BUS_64]   x14_a4    = regs[14];
wire  [`BUS_64]   x15_a5    = regs[15];
wire  [`BUS_64]   x16_a6    = regs[16];
wire  [`BUS_64]   x17_a7    = regs[17];
wire  [`BUS_64]   x18_s2    = regs[18];
wire  [`BUS_64]   x19_s3    = regs[19];
wire  [`BUS_64]   x20_s4    = regs[20];
wire  [`BUS_64]   x21_s5    = regs[21];
wire  [`BUS_64]   x22_s6    = regs[22];
wire  [`BUS_64]   x23_s7    = regs[23];
wire  [`BUS_64]   x24_s8    = regs[24];
wire  [`BUS_64]   x25_s9    = regs[25];
wire  [`BUS_64]   x26_s10   = regs[26];
wire  [`BUS_64]   x27_s11   = regs[27];
wire  [`BUS_64]   x28_t3    = regs[28];
wire  [`BUS_64]   x29_t4    = regs[29];
wire  [`BUS_64]   x30_t5    = regs[30];
wire  [`BUS_64]   x31_t6    = regs[31];

	
// i_rd 写入
always @(posedge clk) begin
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
  end else begin
    // if ((w_ena == 1'b1) && (w_addr != 5'h00))	
    // 	regs[w_addr] <= w_data;
      
    if (i_rd_wen && (i_rd != 5'h00))
      regs[i_rd] <= i_rd_data;
  end
end

// i_rs1 读取
always @(*) begin
  if (rst == 1'b1)
    o_rs1_data = `ZERO_WORD;
  else if (i_rs1_ren == 1'b1)
    o_rs1_data = regs[i_rs1];
  else
    o_rs1_data = `ZERO_WORD;
end

// i_rs2 读取
always @(*) begin
  if (rst == 1'b1)
    o_rs2_data = `ZERO_WORD;
  else if (i_rs2_ren == 1'b1)
    o_rs2_data = regs[i_rs2];
  else
    o_rs2_data = `ZERO_WORD;
end

// difftest regs接口
genvar i;
generate
  for (i = 0; i < 32; i = i + 1) begin
    assign o_regs[i] = (i_rd_wen & i_rd == i & i != 0) ? i_rd_data : regs[i];
  end
endgenerate

wire _unused_ok = &{1'b0,
  x00_zero,
  x01_ra,
  x02_sp,
  x03_gp,
  x04_tp,
  x05_t0,
  x06_t1,
  x07_t2,
  x08_s0,
  x09_s1,
  x10_a0,
  x11_a1,
  x12_a2,
  x13_a3,
  x14_a4,
  x15_a5,
  x16_a6,
  x17_a7,
  x18_s2,
  x19_s3,
  x20_s4,
  x21_s5,
  x22_s6,
  x23_s7,
  x24_s8,
  x25_s9,
  x26_s10,
  x27_s11,
  x28_t3,
  x29_t4,
  x30_t5,
  x31_t6,
  1'b0};

endmodule

// ZhengpuShi


module ysyx_210544_csrfile(
  input   wire              clk,
  input   wire              rst,

  // 读写CSR
  input                     i_csr_ren,
  input   wire  [11 : 0]    i_csr_addr,
  input                     i_csr_wen,
  input   wire  [`BUS_64]   i_csr_wdata,
  output  reg   [`BUS_64]   o_csr_rdata,

  // 中断信号，直接控制csr
  output                    o_csr_clint_mstatus_mie,
  output                    o_csr_clint_mie_mtie,

  // difftest
  output  wire  [`BUS_64]   o_csrs[0 : 15]
);


// CSR
reg [`BUS_64]   csrs[0 : 15];

assign o_csr_clint_mstatus_mie = csrs[`CSR_IDX_MSTATUS][3];
assign o_csr_clint_mie_mtie = csrs[`CSR_IDX_MIE][7];

// i_csr_addr translate to csr_idx
reg  [3 : 0]       csr_idx;
always @(*) begin
  if (rst) begin
    csr_idx = `CSR_IDX_NONE;
  end
  else begin
    case (i_csr_addr)
      `CSR_ADR_MCYCLE   : csr_idx = `CSR_IDX_MCYCLE;
      `CSR_ADR_MSTATUS  : csr_idx = `CSR_IDX_MSTATUS;
      `CSR_ADR_MIE      : csr_idx = `CSR_IDX_MIE;
      `CSR_ADR_MTVEC    : csr_idx = `CSR_IDX_MTVEC;
      `CSR_ADR_MSCRATCH : csr_idx = `CSR_IDX_MSCRATCH;
      `CSR_ADR_MEPC     : csr_idx = `CSR_IDX_MEPC;
      `CSR_ADR_MCAUSE   : csr_idx = `CSR_IDX_MCAUSE;
      `CSR_ADR_MIP      : csr_idx = `CSR_IDX_MIP;
      default           : csr_idx = `CSR_IDX_NONE;
    endcase
  end
end

// csr读取
always @(*) begin
  if (rst == 1'b1) begin
    o_csr_rdata   = 0;
  end
  else if (i_csr_ren == 1'b1) begin
    o_csr_rdata = csrs[csr_idx];
  end
  else begin
    o_csr_rdata = 0;
  end
end

wire mstatus_sd = (i_csr_wdata[14:13] == 2'b11) | (i_csr_wdata[16:15] == 2'b11);

// csr写入
always @(posedge clk) begin
  if (rst == 1'b1) begin
    csrs[`CSR_IDX_MCYCLE]   <= 0;
    csrs[`CSR_IDX_MSTATUS]  <= 64'h1800;// 64'h1808;
    csrs[`CSR_IDX_MIE]      <= 0;// 64'h80;
    csrs[`CSR_IDX_MTVEC]    <= 0;
    csrs[`CSR_IDX_MEPC]     <= 0;
    csrs[`CSR_IDX_MCAUSE]   <= 0;// 64'h80000000_00000007;
    csrs[`CSR_IDX_MIP]      <= 0;// 64'h80;
  end
  else begin

    if (i_csr_wen) begin
      if (csr_idx == `CSR_IDX_MSTATUS) begin
        csrs[csr_idx] <= {mstatus_sd, i_csr_wdata[62:0]};
      end
      else begin
        csrs[csr_idx] <= i_csr_wdata;
      end
    end
  end
end

// difftest csr_regs接口
genvar i;
generate
  for (i = 0; i < 8; i = i + 1) begin
    assign o_csrs[i] = csrs[i];
  end
endgenerate

// mcycle模拟
always @(posedge clk) begin
  if (rst) begin
    csrs[`CSR_IDX_MCYCLE] <= 0;
  end
  else begin
    csrs[`CSR_IDX_MCYCLE] <= csrs[`CSR_IDX_MCYCLE] + 1;
  end
end


endmodule

// ZhengpuShi

// Fetch Interface


module ysyx_210544_if_stage(
  input   wire                clk,
  input   wire                rst,
  input                       i_if_writebacked_req,
  output  reg                 o_if_fetched_req,

  ///////////////////////////////////////////////
  // AXI interface for Fetch
	input                       i_if_bus_ack,
  input         [`BUS_32]     i_if_bus_rdata,
	output                      o_if_bus_req,
  output        [`BUS_64]     o_if_bus_addr,
  
  ///////////////////////////////////////////////
  input   wire                i_if_pc_jmp,
  input   wire  [`BUS_64]     i_if_pc_jmpaddr,
  output  reg   [`BUS_64]     o_if_pc,
  output  reg   [`BUS_32]     o_if_inst,
  output                      o_if_nocmt
);

ysyx_210544_ifU IfU(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
	.i_bus_ack                  (i_if_bus_ack               ),
  .i_bus_rdata                (i_if_bus_rdata             ),
	.o_bus_req                  (o_if_bus_req               ),
  .o_bus_addr                 (o_if_bus_addr              ),
  .i_writebacked_req          (i_if_writebacked_req       ),
  .i_pc_jmp                   (i_if_pc_jmp                ),
  .i_pc_jmpaddr               (i_if_pc_jmpaddr            ),
  .o_pc                       (o_if_pc                    ),
  .o_inst                     (o_if_inst                  ),
  .o_fetched                  (o_if_fetched_req           ),
  .o_nocmt                    (o_if_nocmt                 )
);

endmodule

// ZhengpuShi

// Fetch Unit


module ysyx_210544_ifU(
  input   wire                clk,
  input   wire                rst,

  /////////////////////////////////////////////////////////
  // AXI interface for Fetch
	input                       i_bus_ack,
  input         [`BUS_32]     i_bus_rdata,
	output reg                  o_bus_req,
  output reg    [`BUS_64]     o_bus_addr,
  
  /////////////////////////////////////////////////////////
  input                       i_writebacked_req,    // 是否写回阶段完成
  input   wire                i_pc_jmp,
  input   wire  [`BUS_64]     i_pc_jmpaddr,
  output  reg   [`BUS_64]     o_pc,
  output  reg   [`BUS_32]     o_inst,
  output                      o_fetched,            // 取到指令的通知
  output  reg                 o_nocmt               // 由于冲刷流水线而不提交这条指令
);

assign o_nocmt = 0;

// o_bus_req
always @(posedge clk) begin
  if (rst) begin
    o_bus_req <= 1;
  end
  else begin
    // 停止信号
    if (handshake_done) begin
      // 若要求再次取指，则这次不要停止
      if (fetch_again) begin
        fetch_again <= 0;
      end
      else begin
        o_bus_req <= 0;
      end
    end
    // 启动信号
    else if (i_writebacked_req) begin
      o_bus_req <= 1;
    end
  end
end

wire handshake_done = o_bus_req & i_bus_ack;

// 跳转指令处理
reg           ignore_next_inst;     // 忽略下一条取指
reg [`BUS_64] saved_pc_jmpaddr;     // 记忆的pc跳转指令
reg           fetch_again;          // 再次取指
reg [`BUS_64] pc_pred;              // 预测的下一个PC

always @(posedge clk) begin
  if (rst) begin
    ignore_next_inst <= 0;
    saved_pc_jmpaddr <= 0;
    fetch_again <= 0;
  end
  else begin
    if (i_pc_jmp & (i_pc_jmpaddr != pc_pred)) begin
      ignore_next_inst <= 1;
      fetch_again <= 1;
      saved_pc_jmpaddr <= i_pc_jmpaddr;
    end
  end
end

// fetch an instruction
always @( posedge clk ) begin
  if (rst) begin
    o_bus_addr              <= `PC_START;
    o_pc                    <= 0;
    pc_pred                 <= 0;
    o_fetched               <= 0;
  end
  else begin
    if (handshake_done) begin
      if (ignore_next_inst) begin
        ignore_next_inst        <= 0;
        o_bus_addr              <= saved_pc_jmpaddr;
        o_pc                    <= saved_pc_jmpaddr;
        pc_pred                 <= saved_pc_jmpaddr + 4;
      end
      else begin
        o_bus_addr              <= o_bus_addr + 4;
        o_pc                    <= o_bus_addr;
        pc_pred                 <= o_bus_addr + 4;
        o_inst                  <= i_bus_rdata;
        o_fetched               <= 1;
      end
    end
    else begin
      o_inst                  <= 0;
      o_fetched               <= 0;
    end
  end
end


endmodule

// ZhengpuShi

// Instruction Decode Interface


module ysyx_210544_id_stage(
  input   wire                clk,
  input   wire                rst,
  input   reg                 i_id_fetched_req,
  input   reg                 i_id_decoded_ack,
  output  reg                 o_id_decoded_req,
  input   wire  [`BUS_64]     i_id_pc,
  input   wire  [`BUS_32]     i_id_inst,
  input   wire  [`BUS_64]     i_id_rs1_data,
  input   wire  [`BUS_64]     i_id_rs2_data,
  input   wire                i_id_nocmt,
  output  wire  [`BUS_64]     o_id_pc,
  output  wire  [`BUS_32]     o_id_inst,
  output  reg                 o_id_rs1_ren,
  output  wire  [`BUS_RIDX]   o_id_rs1,
  output  wire                o_id_rs2_ren,
  output  wire  [`BUS_RIDX]   o_id_rs2,
  output  wire  [`BUS_RIDX]   o_id_rd,
  output  wire                o_id_rd_wen,
  output  wire  [7 : 0]       o_id_inst_opcode,
  output  wire  [`BUS_64]     o_id_op1,
  output  wire  [`BUS_64]     o_id_op2,
  output  wire  [`BUS_64]     o_id_op3,
  output  wire                o_id_nocmt,
  output  wire                o_id_skipcmt
);

wire fetched_hs = i_id_fetched_req;
wire decoded_hs = i_id_decoded_ack & o_id_decoded_req;

// 是否使能组合逻辑单元部件
reg                           i_ena;


// 保存输入信息
reg   [`BUS_64]               tmp_i_id_pc;
reg   [`BUS_32]               tmp_i_id_inst;
reg                           tmp_i_id_nocmt;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_id_pc,
      tmp_i_id_inst,
      tmp_i_id_nocmt
    } <= 0;

    o_id_decoded_req      <= 0;
    i_ena                 <= 0;
  end
  else begin
    if (fetched_hs) begin
      tmp_i_id_pc         <= i_id_pc;
      tmp_i_id_inst       <= i_id_inst;
      tmp_i_id_nocmt      <= i_id_nocmt;

      o_id_decoded_req    <= 1;
      i_ena               <= 1;
    end
    else if (decoded_hs) begin
      o_id_decoded_req    <= 0;
      i_ena               <= 0;
    end
  end
end

wire i_disable = !i_ena;

assign o_id_pc      = i_disable ? 0 : tmp_i_id_pc;
assign o_id_inst    = i_disable ? 0 : tmp_i_id_inst;
assign o_id_nocmt   = i_disable ? 0 : tmp_i_id_nocmt;


ysyx_210544_idU IdU(
  .rst                        (rst                        ),
  .i_inst                     (tmp_i_id_inst              ),
  .i_rs1_data                 (i_id_rs1_data              ),
  .i_rs2_data                 (i_id_rs2_data              ),
  .i_pc                       (tmp_i_id_pc                ),
  .o_inst_opcode              (o_id_inst_opcode           ),
  .o_rs1_ren                  (o_id_rs1_ren               ),
  .o_rs1                      (o_id_rs1                   ),
  .o_rs2_ren                  (o_id_rs2_ren               ),
  .o_rs2                      (o_id_rs2                   ),
  .o_rd                       (o_id_rd                    ),
  .o_rd_wen                   (o_id_rd_wen                ),
  .o_op1                      (o_id_op1                   ),
  .o_op2                      (o_id_op2                   ),
  .o_op3                      (o_id_op3                   ),
  .o_skipcmt                  (o_id_skipcmt               )
);

endmodule

// ZhengpuShi

// Instruction Decode Unit, 组合逻辑电路


module ysyx_210544_idU(
  input   wire                rst,
  input   wire  [`BUS_32]     i_inst,
  input   wire  [`BUS_64]     i_rs1_data,
  input   wire  [`BUS_64]     i_rs2_data,
  input   wire  [`BUS_64]     i_pc,
  output  reg                 o_rs1_ren,
  output  wire  [`BUS_RIDX]   o_rs1,
  output  wire                o_rs2_ren,
  output  wire  [`BUS_RIDX]   o_rs2,
  output  wire  [`BUS_RIDX]   o_rd,
  output  wire                o_rd_wen,
  output  wire  [7 : 0]       o_inst_opcode,
  output  wire  [`BUS_64]     o_op1,
  output  wire  [`BUS_64]     o_op2,
  output  wire  [`BUS_64]     o_op3,
  output  wire                o_skipcmt
);

wire [7  : 0] inst_opcode;

assign o_inst_opcode = inst_opcode;

wire [6  : 0] opcode;
wire [4  : 0] rs1;
wire [4  : 0] rs2;
wire [4  : 0] rd;
wire [2  : 0] func3;
wire [6  : 0] func7;
wire [5  : 0] shamt;
wire [63 : 0] imm_I;
wire [63 : 0] imm_S;
wire [63 : 0] imm_B;
wire [63 : 0] imm_U;
wire [63 : 0] imm_J;

assign opcode     = i_inst[6  :  0];
assign rs1        = i_inst[19 : 15];
assign rs2        = i_inst[24 : 20];
assign rd         = i_inst[11 :  7];
assign func3      = i_inst[14 : 12];
assign func7      = i_inst[31 : 25];
assign shamt      = i_inst[25 : 20];
assign imm_I      = { {52{i_inst[31]}}, i_inst[31 : 20] };
assign imm_S      = { {52{i_inst[31]}}, i_inst[31 : 25], i_inst[11 : 7] };
assign imm_B      = { {52{i_inst[31]}}, i_inst[7], i_inst[30 : 25], i_inst[11 : 8], 1'b0 };
assign imm_U      = { {32{i_inst[31]}}, i_inst[31 : 12], 12'b0 };
assign imm_J      = { {44{i_inst[31]}}, i_inst[19 : 12], i_inst[20], i_inst[30 : 21], 1'b0 };

wire inst_lui     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] &  opcode[2];
wire inst_auipc   = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] &  opcode[2];
wire inst_jal     =  opcode[6] &  opcode[5] & ~opcode[4] &  opcode[3] &  opcode[2];
wire inst_jalr    =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] &  opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];

wire inst_beq     =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
wire inst_bne     =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
wire inst_blt     =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] & ~func3[0];
wire inst_bge     =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0];
wire inst_bltu    =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
wire inst_bgeu    =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] &  func3[0];

wire inst_lb      = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
wire inst_lh      = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
wire inst_lw      = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];
wire inst_lbu     = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] & ~func3[0];
wire inst_lhu     = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0];

wire inst_sb      = ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
wire inst_sh      = ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
wire inst_sw      = ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];

wire inst_addi    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
wire inst_slti    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];
wire inst_sltiu   = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
wire inst_xori    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] & ~func3[0];
wire inst_ori     = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
wire inst_andi    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] &  func3[0];
wire inst_slli    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
wire inst_srli    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] & ~func7[5];
wire inst_srai    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] &  func7[5];

wire inst_add     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] & ~func7[5];
wire inst_sub     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] &  func7[5];
wire inst_sll     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
wire inst_slt     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];
wire inst_sltu    = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
wire inst_xor     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] & ~func3[0];
wire inst_srl     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] & ~func7[5];
wire inst_sra     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] &  func7[5];
wire inst_or      = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
wire inst_and     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] &  func3[0];

wire inst_fence   = ~opcode[6] & ~opcode[5] & ~opcode[4] &  opcode[3] &  opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
wire inst_fencei  = ~opcode[6] & ~opcode[5] & ~opcode[4] &  opcode[3] &  opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
wire inst_ecall   =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] & ~func7[4] & ~func7[3] & ~func7[0] & ~rs2[1];
wire inst_ebreak  =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] & ~func7[4] & ~func7[3] &  func7[0] & ~rs2[1];

wire inst_csrrw   =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
wire inst_csrrs   =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];
wire inst_csrrc   =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
wire inst_csrrwi  =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0];
wire inst_csrrsi  =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
wire inst_csrrci  =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] &  func3[0];

wire inst_lwu     = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
wire inst_ld      = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
wire inst_sd      = ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
wire inst_addiw   = ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
wire inst_slliw   = ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
wire inst_srliw   = ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] & ~func7[5];
wire inst_sraiw   = ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] &  func7[5];
wire inst_addw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] & ~func7[5];
wire inst_subw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] &  func7[5];
wire inst_sllw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
wire inst_srlw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] & ~func7[5];
wire inst_sraw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] &  func7[5];

wire inst_mret    =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] &  func7[4] &  func7[3] & ~func7[0] & rs2[1];

wire inst_load    = inst_lb | inst_lbu | inst_lh | inst_lhu | inst_lw | inst_lwu | inst_ld;
wire inst_store   = inst_sb | inst_sh | inst_sw | inst_sd;

// arith inst: 10000; logic: 01000;
// load-store: 00100; j: 00010;  sys: 000001
// === I don't use the logic above!
assign inst_opcode[7] = (  rst == 1'b1 ) ? 0 : 0;
assign inst_opcode[6] = (  rst == 1'b1 ) ? 0 : 0;
assign inst_opcode[5] = (  rst == 1'b1 ) ? 0 : 
  ( inst_sltu   | inst_xor    | inst_srl    | inst_sra    | 
    inst_or     | inst_and    | inst_fence  | inst_fencei | 
    inst_ecall  | inst_ebreak | inst_csrrw  | inst_csrrs  | 
    inst_csrrc  | inst_csrrwi | inst_csrrsi | inst_csrrci |
    inst_lwu    | inst_ld     | inst_sd     | inst_addiw  |
    inst_slliw  | inst_srliw  | inst_sraiw  | inst_addw   | 
    inst_subw   | inst_sllw   | inst_srlw   | inst_sraw   |
    inst_mret   );
assign inst_opcode[4] = (  rst == 1'b1 ) ? 0 : 
  ( inst_sb     | inst_sh     | inst_sw     | inst_addi   | 
    inst_slti   | inst_sltiu  | inst_xori   | inst_ori    | 
    inst_andi   | inst_slli   | inst_srli   | inst_srai   | 
    inst_add    | inst_sub    | inst_sll    | inst_slt    |
    inst_lwu    | inst_ld     | inst_sd     | inst_addiw  |
    inst_slliw  | inst_srliw  | inst_sraiw  | inst_addw   | 
    inst_subw   | inst_sllw   | inst_srlw   | inst_sraw   |
    inst_mret   );
assign inst_opcode[3] = (  rst == 1'b1 ) ? 0 : 
  ( inst_bge    | inst_bltu   | inst_bgeu   | inst_lb     | 
    inst_lh     | inst_lw     | inst_lbu    | inst_lhu    | 
    inst_andi   | inst_slli   | inst_srli   | inst_srai   | 
    inst_add    | inst_sub    | inst_sll    | inst_slt    | 
    inst_ecall  | inst_ebreak | inst_csrrw  | inst_csrrs  | 
    inst_csrrc  | inst_csrrwi | inst_csrrsi | inst_csrrci |
    inst_sllw   | inst_srlw   | inst_sraw   | inst_subw   |
    inst_mret   );
assign inst_opcode[2] = (  rst == 1'b1 ) ? 0 : 
  ( inst_jalr   | inst_beq    | inst_bne    | inst_blt    | 
    inst_lh     | inst_lw     | inst_lbu    | inst_lhu    | 
    inst_slti   | inst_sltiu  | inst_xori   | inst_ori    | 
    inst_add    | inst_sub    | inst_sll    | inst_slt    | 
    inst_or     | inst_and    | inst_fence  | inst_fencei | 
    inst_csrrc  | inst_csrrwi | inst_csrrsi | inst_csrrci |
    inst_slliw  | inst_srliw  | inst_sraiw  | inst_mret   );
assign inst_opcode[1] = (  rst == 1'b1 ) ? 0 : 
  ( inst_auipc  | inst_jal    | inst_bne    | inst_blt    | 
    inst_bgeu   | inst_lb     | inst_lbu    | inst_lhu    | 
    inst_sw     | inst_addi   | inst_xori   | inst_ori    | 
    inst_srli   | inst_srai   | inst_sll    | inst_slt    | 
    inst_srl    | inst_sra    | inst_fence  | inst_fencei | 
    inst_csrrw  | inst_csrrs  | inst_csrrsi | inst_csrrci |
    inst_sd     | inst_addiw  | inst_sraiw  | inst_addw   | 
    inst_srlw   | inst_sraw   );
assign inst_opcode[0] = (  rst == 1'b1 ) ? 0 : 
  ( inst_lui    | inst_jal    | inst_beq    | inst_blt    | 
    inst_bltu   | inst_lb     | inst_lw     | inst_lhu    | 
    inst_sh     | inst_addi   | inst_sltiu  | inst_ori    | 
    inst_slli   | inst_srai   | inst_sub    | inst_slt    | 
    inst_xor    | inst_sra    | inst_and    | inst_fencei | 
    inst_ebreak | inst_csrrs  | inst_csrrwi | inst_csrrci |
    inst_ld     | inst_addiw  | inst_srliw  | inst_addw   | 
    inst_sllw   | inst_sraw   ); 

wire inst_type_R;
wire inst_type_I;
wire inst_type_S;
wire inst_type_B;
wire inst_type_U;
wire inst_type_J;
wire inst_type_CSRI;  // csr immediate

assign inst_type_R    = ( rst == 1'b1 ) ? 0 : 
  ( inst_add    | inst_sub    | inst_sll    | inst_slt    | 
    inst_sltu   | inst_xor    | inst_srl    | inst_sra    | 
    inst_or     | inst_and    | inst_addw   | inst_subw   | 
    inst_sllw   | inst_srlw   | inst_sraw   );
assign inst_type_I    = ( rst == 1'b1 ) ? 0 : 
  ( inst_jalr   | inst_lb     | inst_lh     | inst_lw     | 
    inst_ld     | inst_lbu    | inst_lhu    | inst_lwu    | 
    inst_addi   | inst_slti   | inst_sltiu  | inst_xori   | 
    inst_ori    | inst_andi   | inst_slli   | inst_srli   | 
    inst_srai   | inst_csrrw  | inst_csrrs  | inst_csrrc  |
    inst_lwu    | inst_ld     | inst_addiw  | inst_slliw  | 
    inst_srliw  | inst_sraiw  | inst_csrrwi | inst_csrrsi | 
    inst_csrrci );
assign inst_type_S    = ( rst == 1'b1 ) ? 0 : 
  ( inst_sb     | inst_sh     | inst_sw     | inst_sd     );
assign inst_type_B    = ( rst == 1'b1 ) ? 0 : 
  ( inst_beq    | inst_bne    | inst_blt    | inst_bge   | 
    inst_bltu   | inst_bgeu   );
assign inst_type_U    = ( rst == 1'b1 ) ? 0 : 
  ( inst_lui    | inst_auipc  );
assign inst_type_J    = ( rst == 1'b1 ) ? 0 : 
  ( inst_jal    );
assign inst_type_CSRI = ( rst == 1'b1 ) ? 0 : 
  ( inst_csrrwi | inst_csrrsi | inst_csrrci );

assign o_rs1_ren  = ( rst == 1'b1 ) ? 0 : ( inst_type_R | inst_type_I | inst_type_S | inst_type_B);
assign o_rs1      = ( rst == 1'b1 ) ? 0 : ((inst_type_R | inst_type_I | inst_type_S | inst_type_B) ? rs1 : 0 );
assign o_rs2_ren  = ( rst == 1'b1 ) ? 0 : ( inst_type_R | inst_type_S | inst_type_B);
assign o_rs2      = ( rst == 1'b1 ) ? 0 : ((inst_type_R | inst_type_S | inst_type_B) ? rs2 : 0 );

assign o_rd_wen   = ( rst == 1'b1 ) ? 0 : ( inst_type_R | inst_type_I | inst_type_U | inst_type_J | inst_type_CSRI);
assign o_rd       = ( rst == 1'b1 ) ? 0 : ((inst_type_R | inst_type_I | inst_type_U | inst_type_J | inst_type_CSRI) ? rd  : 0 );

always @(*) begin
  if (rst == 1'b1) begin
    o_op1 = 0;
  end
  else begin
    if (inst_type_R | inst_type_I | inst_type_S | inst_type_B) begin
      if (inst_csrrwi | inst_csrrsi | inst_csrrci) begin
        o_op1 = {59'd0, rs1};
      end
      else begin
        o_op1 = i_rs1_data;
      end
    end
    else if (inst_type_U) begin
      o_op1 = imm_U;
    end
    else if (inst_type_J) begin
      o_op1 = i_pc;
    end
    else if (inst_type_CSRI) begin
      o_op1 = {59'd0, rs1};
    end
    else begin
      o_op1 = 0;
    end
  end
end


always @(*) begin
  if (rst == 1'b1) begin
    o_op2 = 0;
  end
  else begin
    if (inst_type_R | inst_type_S | inst_type_B) begin
      o_op2 = i_rs2_data;
    end
    else if (inst_type_J) begin
      o_op2 = 4;
    end
    else if (inst_type_I) begin
      if (inst_slliw | inst_srai) begin
        o_op2 = {58'd0, shamt};
      end
      else begin
        o_op2 = imm_I;
      end
    end
    else if (inst_type_U) begin
      o_op2 = i_pc;
    end
    else begin
      o_op2 = 0;
    end
  end
end


// o_op3
always @(*) begin
  if (rst == 1'b1) begin
    o_op3 = 0;
  end
  else begin
    if (inst_type_B) begin
      o_op3 = i_pc + imm_B;
    end
    else if (inst_type_J) begin
      o_op3 = i_pc + imm_J;
    end
    else if (inst_type_S) begin
      o_op3 = imm_S;
    end
    else if (inst_type_I) begin
      if (inst_jalr) begin
        o_op3 = i_pc + 4;
      end
      else if (inst_load | inst_store) begin
        o_op3 = imm_I;
      end
      else begin
        o_op3 = 0;
      end
    end
    else begin
      o_op3 = 0;
    end
  end
end


// 某些自定义指令，需要通知difftest跳过比对（提交，但不对比）
assign o_skipcmt = 
  (i_inst == 32'h7b)                 // putch
  // | (o_opcode == `OPCODE_CSR)   
  // | mem_addr_is_device
  ;

wire _unused_ok = &{1'b0,
  opcode[1:0],
  func7[6],
  func7[2:1],
  1'b0};

endmodule

// ZhengpuShi

// Execute Interface


module ysyx_210544_exe_stage(
  input   wire                rst,
  input   wire                clk,
  input   reg                 i_ex_decoded_req,
  output  reg                 o_ex_decoded_ack,
  output  reg                 o_ex_executed_req,
  input   reg                 i_ex_executed_ack,
  input   wire  [7 : 0]       i_ex_inst_opcode,
  input   wire  [`BUS_64]     i_ex_pc,
  input   wire  [`BUS_32]     i_ex_inst,
  input   wire  [`BUS_64]     i_ex_op1,
  input   wire  [`BUS_64]     i_ex_op2,
  input   wire  [`BUS_64]     i_ex_op3,
  input   wire  [`BUS_RIDX]   i_ex_rd,
  input   reg                 i_ex_rd_wen,
  input   wire                i_ex_nocmt,
  input   wire                i_ex_clint_mstatus_mie,
  input   wire                i_ex_clint_mie_mtie,
  input   wire                i_ex_clint_mtime_overflow,
  input   wire                i_ex_skipcmt,
  input   reg   [`BUS_64]     i_ex_csr_rdata,
  output  reg   [11 : 0]      o_ex_csr_addr,
  output  reg                 o_ex_csr_ren,
  output  reg                 o_ex_csr_wen,
  output  reg   [`BUS_64]     o_ex_csr_wdata,
  output  reg   [`BUS_64]     o_ex_pc,
  output  reg   [`BUS_32]     o_ex_inst,
  output  reg                 o_ex_pc_jmp,
  output  reg   [`BUS_64]     o_ex_pc_jmpaddr,
  output  reg   [`BUS_RIDX]   o_ex_rd,
  output  reg                 o_ex_rd_wen,
  output  reg   [`BUS_64]     o_ex_rd_wdata,
  output  wire  [7 : 0]       o_ex_inst_opcode,
  output  wire  [`BUS_64]     o_ex_op1,
  output  wire  [`BUS_64]     o_ex_op2,
  output  wire  [`BUS_64]     o_ex_op3,
  output  wire                o_ex_nocmt,
  output  wire                o_ex_skipcmt,
  output  reg   [`BUS_32]     o_ex_intrNo
);

assign o_ex_decoded_ack = 1'b1;

wire decoded_hs = i_ex_decoded_req & o_ex_decoded_ack;
wire executed_hs = i_ex_executed_ack & o_ex_executed_req;

wire exeU_skip_cmt;

// 是否为异常指令：ecall, mret
wire is_inst_exceptionU = (i_ex_inst_opcode == `INST_ECALL) |
  (i_ex_inst_opcode == `INST_MRET);
// 是否产生了时钟中断？
wire is_time_int_req = i_ex_clint_mstatus_mie & i_ex_clint_mie_mtie & i_ex_clint_mtime_overflow;

// 通道选择
reg o_ena_exeU;
reg o_ena_exceptionU;

wire            exeU_pc_jmp;
wire [`BUS_64]  exeU_pc_jmpaddr;

wire            exceptionU_req;
wire            exceptionU_pc_jmp;
wire [`BUS_64]  exceptionU_pc_jmpaddr;


// 保存输入信息
reg   [7 : 0]                 tmp_i_ex_inst_opcode;
reg   [`BUS_64]               tmp_i_ex_pc;
reg   [`BUS_32]               tmp_i_ex_inst;
reg   [`BUS_64]               tmp_i_ex_op1;
reg   [`BUS_64]               tmp_i_ex_op2;
reg   [`BUS_64]               tmp_i_ex_op3;
reg   [4 : 0]                 tmp_i_ex_rd;
reg                           tmp_i_ex_rd_wen;
reg                           tmp_i_ex_nocmt;
reg                           tmp_i_ex_skipcmt;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_ex_inst_opcode,
      tmp_i_ex_pc,
      tmp_i_ex_inst,
      tmp_i_ex_op1, 
      tmp_i_ex_op2, 
      tmp_i_ex_op3,
      tmp_i_ex_rd,
      tmp_i_ex_rd_wen,
      tmp_i_ex_nocmt,
      tmp_i_ex_skipcmt
    } <= 0;

    o_ex_executed_req   <= 0;
    o_ena_exceptionU    <= 0;
    o_ex_intrNo <= 0;
  end
  else begin
    // 启动
    if (decoded_hs) begin
      tmp_i_ex_inst_opcode <= i_ex_inst_opcode;
      tmp_i_ex_pc       <= i_ex_pc;
      tmp_i_ex_inst     <= i_ex_inst;
      tmp_i_ex_op1      <= i_ex_op1;
      tmp_i_ex_op2      <= i_ex_op2;
      tmp_i_ex_op3      <= i_ex_op3;
      tmp_i_ex_rd       <= i_ex_rd;
      tmp_i_ex_rd_wen   <= i_ex_rd_wen;
      tmp_i_ex_nocmt    <= i_ex_nocmt;
      tmp_i_ex_skipcmt  <= i_ex_skipcmt;
      
      o_ex_intrNo <= is_time_int_req ? 7 : 0;

      // 通道选择
      if (!is_inst_exceptionU && !is_time_int_req) begin
        o_ena_exeU        <= 1;
        // exeU立即结束，请求信号置位
        o_ex_executed_req <= 1;
      end
      else begin
        o_ena_exceptionU  <= 1;
      end
    end
    // exeU或exceptionU收到应答，请求信号撤销
    else if (executed_hs) begin
      o_ex_executed_req <= 0;
      o_ena_exeU        <= 0;
      o_ena_exceptionU  <= 0;
      o_ex_intrNo <= 0;
    end
    // exceptionU结束，请求信号置位
    else if (exceptionU_req) begin
      o_ex_executed_req <= 1;
    end
  end
end

wire i_disable = rst | (!executed_hs);

assign o_ex_pc            = i_disable ? 0 : tmp_i_ex_pc;
assign o_ex_inst          = i_disable ? 0 : tmp_i_ex_inst;
assign o_ex_rd            = i_disable ? 0 : tmp_i_ex_rd;
assign o_ex_op1           = i_disable ? 0 : tmp_i_ex_op1;
assign o_ex_op2           = i_disable ? 0 : tmp_i_ex_op2;
assign o_ex_op3           = i_disable ? 0 : tmp_i_ex_op3;
assign o_ex_inst_opcode   = i_disable ? 0 : tmp_i_ex_inst_opcode;
assign o_ex_rd            = i_disable ? 0 : (!o_ena_exeU ? 0 : tmp_i_ex_rd);
assign o_ex_rd_wen        = i_disable ? 0 : (!o_ena_exeU ? 0 : tmp_i_ex_rd_wen);
assign o_ex_nocmt         = i_disable ? 0 : tmp_i_ex_nocmt;
assign o_ex_skipcmt       = i_disable ? 0 : (tmp_i_ex_skipcmt | exeU_skip_cmt);


wire   [11 : 0]      exeU_csr_addr;
wire                 exeU_csr_ren;
wire                 exeU_csr_wen;
wire   [`BUS_64]     exeU_csr_wdata;
wire   [11 : 0]      exceptionU_csr_addr;
wire                 exceptionU_csr_ren;
wire                 exceptionU_csr_wen;
wire   [`BUS_64]     exceptionU_csr_wdata;


assign o_ex_pc_jmp      = rst ? 0 : (o_ena_exeU ? exeU_pc_jmp     : exceptionU_pc_jmp);
assign o_ex_pc_jmpaddr  = rst ? 0 : (o_ena_exeU ? exeU_pc_jmpaddr : exceptionU_pc_jmpaddr);
assign o_ex_csr_addr    = rst ? 0 : (o_ena_exeU ? exeU_csr_addr   : exceptionU_csr_addr);
assign o_ex_csr_ren     = rst ? 0 : (o_ena_exeU ? exeU_csr_ren    : exceptionU_csr_ren);
assign o_ex_csr_wen     = rst ? 0 : (o_ena_exeU ? exeU_csr_wen    : exceptionU_csr_wen);
assign o_ex_csr_wdata   = rst ? 0 : (o_ena_exeU ? exeU_csr_wdata  : exceptionU_csr_wdata);

ysyx_210544_exeU ExeU(
  .ena                        (o_ena_exeU                 ),
  .i_inst_opcode              (tmp_i_ex_inst_opcode       ),
  .i_op1                      (tmp_i_ex_op1               ),
  .i_op2                      (tmp_i_ex_op2               ),
  .i_op3                      (tmp_i_ex_op3               ),
  .i_csr_rdata                (i_ex_csr_rdata             ),
  .o_csr_addr                 (exeU_csr_addr              ),
  .o_csr_ren                  (exeU_csr_ren               ),
  .o_csr_wen                  (exeU_csr_wen               ),
  .o_csr_wdata                (exeU_csr_wdata             ),
  .o_pc_jmp                   (exeU_pc_jmp                ),
  .o_pc_jmpaddr               (exeU_pc_jmpaddr            ),
  .o_rd_wdata                 (o_ex_rd_wdata              ),
  .o_exeU_skip_cmt            (exeU_skip_cmt              )
);

ysyx_210544_exceptionU ExceptionU(
  .rst                        (rst                        ),
  .clk                        (clk                        ),
  .ena                        (o_ena_exceptionU & (!o_ex_executed_req)),
  .ack                        (i_ex_executed_ack          ),
  .req                        (exceptionU_req             ),
  .i_inst_opcode              (i_ex_inst_opcode           ),
  .i_pc                       (tmp_i_ex_pc                ),
  .i_csr_rdata                (i_ex_csr_rdata             ),
  .o_pc_jmp                   (exceptionU_pc_jmp          ),
  .o_pc_jmpaddr               (exceptionU_pc_jmpaddr      ),
  .o_csr_addr                 (exceptionU_csr_addr        ),
  .o_csr_ren                  (exceptionU_csr_ren         ),
  .o_csr_wen                  (exceptionU_csr_wen         ),
  .o_csr_wdata                (exceptionU_csr_wdata       )
);

endmodule

// ZhengpuShi

// Execute Unit, 组合逻辑电路


module ysyx_210544_exeU(
  input   wire                ena,
  input   wire  [7 : 0]       i_inst_opcode,
  input   wire  [`BUS_64]     i_op1,
  input   wire  [`BUS_64]     i_op2,
  input   wire  [`BUS_64]     i_op3,
  input   reg   [`BUS_64]     i_csr_rdata,
  output  reg   [11 : 0]      o_csr_addr,
  output  reg                 o_csr_ren,
  output  reg                 o_csr_wen,
  output  reg   [`BUS_64]     o_csr_wdata,
  output  reg                 o_pc_jmp,
  output  reg   [`BUS_64]     o_pc_jmpaddr,
  output  wire  [`BUS_64]     o_rd_wdata,
  output  reg                 o_exeU_skip_cmt    // 这里也会发现需要跳过提交的指令，比如 csr mcycle
);

wire i_disable = !ena;

wire [63:0] reg64_t1 = i_op1 + i_op2;
wire [63:0] reg64_t2 = i_op1 << i_op2[5:0];
wire [63:0] reg64_t3 = i_op1 - $signed(i_op2);
wire [63:0] reg64_t4 = i_op1 << i_op2[4:0];
wire [31:0] reg32_t1 = i_op1[31:0] >> i_op2[4:0];
always@( * )
begin
  if( i_disable )
  begin
    o_rd_wdata = `ZERO_WORD;
  end
  else
  begin
    case( i_inst_opcode )
	  `INST_ADDI    : begin o_rd_wdata = i_op1 + i_op2;  end
	  `INST_ADD     : begin o_rd_wdata = i_op1 + i_op2;  end
	  `INST_SUB     : begin o_rd_wdata = i_op1 - i_op2;  end
	  `INST_SUBW    : begin o_rd_wdata = {{33{reg64_t3[31]}}, reg64_t3[30:0]}; end
	  `INST_ADDIW   : begin o_rd_wdata = {{33{reg64_t1[31]}}, reg64_t1[30:0]}; end
	  `INST_AND     : begin o_rd_wdata = i_op1 & i_op2;  end
	  `INST_ANDI    : begin o_rd_wdata = i_op1 & i_op2;  end
	  `INST_OR      : begin o_rd_wdata = i_op1 | i_op2;  end
	  `INST_ORI     : begin o_rd_wdata = i_op1 | i_op2;  end
	  `INST_XOR     : begin o_rd_wdata = i_op1 ^ i_op2;  end
	  `INST_XORI    : begin o_rd_wdata = i_op1 ^ i_op2;  end
    `INST_SLL     : begin o_rd_wdata = i_op1 << i_op2[5:0]; end
    `INST_SLLI    : begin o_rd_wdata = i_op1 << i_op2[5:0]; end
    `INST_SLLIW   : begin o_rd_wdata = {{33{reg64_t2[31]}}, reg64_t2[30:0]}; end
    `INST_SLLW    : begin o_rd_wdata = {{33{reg64_t4[31]}}, reg64_t4[30:0]}; end
    `INST_SLT     : begin o_rd_wdata = ($signed(i_op1) < $signed(i_op2)) ? 1 : 0; end
    `INST_SLTI    : begin o_rd_wdata = ($signed(i_op1) < $signed(i_op2)) ? 1 : 0; end
    `INST_SLTIU   : begin o_rd_wdata = i_op1 < i_op2 ? 1 : 0; end
    `INST_SLTU    : begin o_rd_wdata = (i_op1 < i_op2) ? 1 : 0; end
    `INST_SRA     : begin o_rd_wdata = $signed(i_op1) >>> i_op2[5:0]; end
    `INST_SRAW    : begin o_rd_wdata = $signed({{33{i_op1[31]}}, i_op1[30:0]}) >>> i_op2[4:0]; end
    `INST_SRAI    : begin o_rd_wdata = $signed(i_op1) >>> i_op2[5:0]; end
    `INST_SRAIW   : begin o_rd_wdata = $signed({{33{i_op1[31]}}, i_op1[30:0]}) >>> i_op2[4:0]; end
    `INST_SRL     : begin o_rd_wdata = i_op1 >> i_op2[5:0]; end
    `INST_SRLI    : begin o_rd_wdata = i_op1 >> i_op2[5:0]; end
    `INST_SRLW    : begin o_rd_wdata = {{32{reg32_t1[31]}}, reg32_t1}; end
    `INST_SRLIW   : begin o_rd_wdata = {{32{reg32_t1[31]}}, reg32_t1}; end
    `INST_LUI     : begin o_rd_wdata = i_op1; end
    `INST_AUIPC   : begin o_rd_wdata = i_op1 + i_op2; end
    `INST_JAL     : begin o_rd_wdata = i_op1 + i_op2; end
    `INST_JALR    : begin o_rd_wdata = i_op3; end
    `INST_CSRRW   : begin o_rd_wdata = i_csr_rdata; end
    `INST_CSRRS   : begin o_rd_wdata = i_csr_rdata; end
    `INST_CSRRC   : begin o_rd_wdata = i_csr_rdata; end
    `INST_CSRRWI  : begin o_rd_wdata = i_csr_rdata; end
    `INST_CSRRSI  : begin o_rd_wdata = i_csr_rdata; end
    `INST_CSRRCI  : begin o_rd_wdata = i_csr_rdata; end
	  default       : begin o_rd_wdata = `ZERO_WORD; end
	endcase
  end
end

// o_pc_jmp
always @(*) begin
  if ( i_disable ) begin
    o_pc_jmp = 0;
  end
  else begin
    case (i_inst_opcode)
      `INST_BEQ   : begin o_pc_jmp = (i_op1 == i_op2) ? 1 : 0; end
      `INST_BNE   : begin o_pc_jmp = (i_op1 != i_op2) ? 1 : 0; end
      `INST_BLT   : begin o_pc_jmp = ($signed(i_op1) < $signed(i_op2)) ? 1 : 0; end
      `INST_BGE   : begin o_pc_jmp = ($signed(i_op1) >= $signed(i_op2)) ? 1 : 0; end
      `INST_BLTU  : begin o_pc_jmp = (i_op1 < i_op2) ? 1 : 0; end
      `INST_BGEU  : begin o_pc_jmp = (i_op1 >= i_op2) ? 1 : 0; end
      `INST_JAL   : begin o_pc_jmp = 1; end
      `INST_JALR  : begin o_pc_jmp = 1; end
      default     : begin o_pc_jmp = 0; end
    endcase
  end
end

// o_pc_jmpaddr
always @(*) begin
  if ( i_disable ) begin
    o_pc_jmpaddr = 0;
  end
  else begin
    case (i_inst_opcode)
      `INST_JAL   : begin o_pc_jmpaddr = i_op3; end
      `INST_JALR  : begin o_pc_jmpaddr = (i_op1 + i_op2) & ~1; end
      `INST_BEQ   : begin o_pc_jmpaddr = i_op3; end
      `INST_BNE   : begin o_pc_jmpaddr = i_op3; end
      `INST_BLT   : begin o_pc_jmpaddr = i_op3; end
      `INST_BGE   : begin o_pc_jmpaddr = i_op3; end
      `INST_BLTU  : begin o_pc_jmpaddr = i_op3; end
      `INST_BGEU  : begin o_pc_jmpaddr = i_op3; end
      default     : begin o_pc_jmpaddr = 0; end
    endcase
  end
end



// ------------- csr -----------------

wire inst_csr = 
  (i_inst_opcode == `INST_CSRRW ) | (i_inst_opcode == `INST_CSRRS ) | 
  (i_inst_opcode == `INST_CSRRC ) | (i_inst_opcode == `INST_CSRRWI) | 
  (i_inst_opcode == `INST_CSRRSI) | (i_inst_opcode == `INST_CSRRCI) ;

assign o_csr_ren  = (i_disable) ? 0 : inst_csr;
assign o_csr_wen  = (i_disable) ? 0 : inst_csr;
assign o_csr_addr = (i_disable) ? 0 : (inst_csr ? i_op2[11:0] : 0);

always @(*) begin
  if (i_disable) begin
    o_csr_wdata = 0;
  end
  else begin
    case (i_inst_opcode)
      `INST_CSRRW   : o_csr_wdata = i_op1;
      `INST_CSRRS   : o_csr_wdata = i_csr_rdata | i_op1;
      `INST_CSRRC   : o_csr_wdata = i_csr_rdata & (~i_op1);
      `INST_CSRRWI  : o_csr_wdata = i_op1;
      `INST_CSRRSI  : o_csr_wdata = i_csr_rdata | i_op1;
      `INST_CSRRCI  : o_csr_wdata = i_csr_rdata & (~i_op1);
      default       : o_csr_wdata = 0;
    endcase
  end
end

assign o_exeU_skip_cmt = (inst_csr && (o_csr_addr == 12'hB00));

wire _unused_ok = &{1'b0,
  reg64_t1[63:32],
  reg64_t2[63:32],
  reg64_t3[63:32],
  reg64_t4[63:32],
  1'b0};

endmodule

// ZhengpuShi

// Exception Unit, 时序电路


module ysyx_210544_exceptionU(
  input   wire                rst,
  input   wire                clk,
  input   wire                ena,
  input   wire                ack,
  output  reg                 req,
  input   wire  [7 : 0]       i_inst_opcode,
  input   wire  [`BUS_64]     i_pc,
  output  reg                 o_pc_jmp,
  output  reg   [`BUS_64]     o_pc_jmpaddr,
  input   reg   [`BUS_64]     i_csr_rdata,
  output  reg   [11 : 0]      o_csr_addr,
  output  reg                 o_csr_ren,
  output  reg                 o_csr_wen,
  output  reg   [`BUS_64]     o_csr_wdata
);

parameter [3:0] STATE_NULL                    = 4'd0;
// 异常或中断进入：ecall、定时器中断等
parameter [3:0] STATE_ENTER_WRITE_MEPC        = 4'd1;   // machine exception program counter
parameter [3:0] STATE_ENTER_WRITE_MCAUSE      = 4'd2;   // machine trap cause
parameter [3:0] STATE_ENTER_READ_MTVEC        = 4'd3;   // machine trap-handler base address
parameter [3:0] STATE_ENTER_READ_MSTATUS      = 4'd4;   // machine status register
parameter [3:0] STATE_ENTER_WRITE_MSTATUS     = 4'd5;   // machine status register
// 异常或中断返回：mret
parameter [3:0] STATE_LEAVE_READ_MSTATUS      = 4'd6;   // machine status register
parameter [3:0] STATE_LEAVE_READ_MEPC         = 4'd7;   // machine exception program counter
parameter [3:0] STATE_LEAVE_WRITE_MSTATUS     = 4'd8;   // machine status register

reg [3:0] state;
reg [1:0] step;
// 在异常发生的第一个时钟周期就确定下来，因为有些输入信号只保持一个周期
reg [63:0] exception_cause;     // 异常原因

wire hs = ack & req;

always @(posedge clk) begin
  if (rst) begin
    state <= STATE_NULL;
    step <= 0;
    exception_cause <= 0;
  end
  else begin
    if (!hs) begin
      case (state)
        STATE_NULL:   begin
          if (ena) begin
            if (i_inst_opcode == `INST_ECALL) begin
              state <= STATE_ENTER_WRITE_MEPC;
              exception_cause <= 64'd11;
              //$write("#ecall\n"); $fflush();
            end
            else if (i_inst_opcode == `INST_MRET) begin
              state <= STATE_LEAVE_READ_MSTATUS;
            end
            else begin
              state <= STATE_ENTER_WRITE_MEPC;
              exception_cause <= 64'h80000000_00000007;
              // $write("#time-instr\n"); $fflush();
              $write("."); $fflush();
            end
            step <= 0;
          end
        end
        
        STATE_ENTER_WRITE_MEPC: begin
          if (step == 2) begin
            state <= STATE_ENTER_WRITE_MCAUSE;
            step <= 0;
          end
        end
        
        STATE_ENTER_WRITE_MCAUSE: begin
          if (step == 2) begin
            state <= STATE_ENTER_READ_MTVEC;
            step <= 0;
          end
        end
        
        STATE_ENTER_READ_MTVEC: begin
          if (step == 2) begin
            state <= STATE_ENTER_READ_MSTATUS;
            step <= 0;
          end
        end
        
        STATE_ENTER_READ_MSTATUS: begin
          if (step == 2) begin
            state <= STATE_ENTER_WRITE_MSTATUS;
            step <= 0;
          end
        end
        
        STATE_ENTER_WRITE_MSTATUS: begin
          if (step == 2) begin
            state <= STATE_NULL;
            step <= 0;
            req <= 1;
          end
        end
        
        STATE_LEAVE_READ_MSTATUS: begin
          if (step == 2) begin
            state <= STATE_LEAVE_READ_MEPC;
            step <= 0;
          end
        end
        
        STATE_LEAVE_READ_MEPC: begin
          if (step == 2) begin
            state <= STATE_LEAVE_WRITE_MSTATUS;
            step <= 0;
          end
        end
        
        STATE_LEAVE_WRITE_MSTATUS: begin
          if (step == 2) begin
            state <= STATE_NULL;
            step <= 0;
            req <= 1;
          end
        end

        default: ;
      endcase
    end
    else begin
      req <= 0;
    end
    
  end
end

reg [63:0] csr_rdata_save1;
reg [63:0] csr_rdata_save2;

always @(posedge clk) begin
  if (rst) begin
    o_pc_jmp        <= 0;
    o_pc_jmpaddr    <= 0;
    csr_rdata_save1  <= 0;
  end
  else begin
    case (state)
      STATE_NULL: begin
        o_pc_jmp <= 0;
        o_pc_jmpaddr <= 0;  
      end

      STATE_ENTER_WRITE_MEPC: begin
        case (step)
          0:  begin 
            o_csr_addr      <=`CSR_ADR_MEPC; 
            o_csr_wen       <= 1; 
            o_csr_wdata     <= i_pc;
            step            <= 1;
          end
          1:  begin
            o_csr_wen       <= 0;
            step            <= 2;
          end
          default: ;
        endcase
      end

      STATE_ENTER_WRITE_MCAUSE: begin
        case (step)
          0:  begin 
            o_csr_addr      <=`CSR_ADR_MCAUSE; 
            o_csr_wen       <= 1; 
            o_csr_wdata     <= exception_cause;
            step            <= 1;
          end
          1:  begin
            o_csr_wen       <= 0;
            step            <= 2;
          end
          default: ;
        endcase
      end

      STATE_ENTER_READ_MTVEC: begin
        case (step)
          0:  begin 
            o_csr_addr      <=`CSR_ADR_MTVEC; 
            o_csr_ren       <= 1; 
            step            <= 1;
          end
          1:  begin
            o_csr_ren       <= 0;
            step            <= 2;
            csr_rdata_save2 <= i_csr_rdata;
          end
          default: ;
        endcase
      end
      
      STATE_ENTER_READ_MSTATUS: begin
        case (step)
          0:  begin 
            o_csr_addr      <=`CSR_ADR_MSTATUS; 
            o_csr_ren       <= 1; 
            step            <= 1;
          end
          1:  begin
            o_csr_ren       <= 0;
            step            <= 2;
            csr_rdata_save1 <= i_csr_rdata;
          end
          default: ;
        endcase
      end
      
      STATE_ENTER_WRITE_MSTATUS: begin
        case (step)
          0:  begin 
            o_csr_addr      <=`CSR_ADR_MSTATUS; 
            o_csr_wen       <= 1; 
            o_csr_wdata     <= {
              csr_rdata_save1[63:13],
              2'b11,                    // [12:11]: MPP, set to M-mode
              csr_rdata_save1[10:8], 
              csr_rdata_save1[3],       // [7]: MPIE, set with MIE
              csr_rdata_save1[6:4], 
              1'b0,                     // [3]: MIE, set 0
              csr_rdata_save1[2:0]
              };
            step            <= 1;
          end
          1:  begin
            o_csr_wen       <= 0;
            step            <= 2;
            o_pc_jmp        <= 1;
            o_pc_jmpaddr    <= csr_rdata_save2;
          end
          default: ;
        endcase
      end
      
      STATE_LEAVE_READ_MSTATUS: begin
        case (step)
          0:  begin 
            o_csr_addr      <=`CSR_ADR_MSTATUS; 
            o_csr_ren       <= 1; 
            step            <= 1;
          end
          1:  begin
            o_csr_ren       <= 0;
            step            <= 2;
            csr_rdata_save1 <= i_csr_rdata;
          end
          default: ;
        endcase
      end

      STATE_LEAVE_READ_MEPC: begin
        case (step)
          0:  begin 
            o_csr_addr      <=`CSR_ADR_MEPC; 
            o_csr_ren       <= 1; 
            step            <= 1;
          end
          1:  begin
            o_csr_ren       <= 0;
            csr_rdata_save2 <= i_csr_rdata;
            step            <= 2;
          end
          default: ;
        endcase
      end
      
      STATE_LEAVE_WRITE_MSTATUS: begin
        case (step)
          0:  begin 
            o_csr_addr      <=`CSR_ADR_MSTATUS; 
            o_csr_wen       <= 1; 
            o_csr_wdata     <= {
              csr_rdata_save1[63:13],
              2'b00,                    // [12:11]: MPP, set to U-mode
              csr_rdata_save1[10:8], 
              1'b1,                     // [7]: MPIE, set to 1
              csr_rdata_save1[6:4], 
              csr_rdata_save1[7],       // [3]: MIE, set with MPIE
              csr_rdata_save1[2:0]
              };
            step            <= 1;
          end
          1:  begin
            o_csr_wen       <= 0;
            step            <= 2;
            o_pc_jmp        <= 1;
            o_pc_jmpaddr    <= csr_rdata_save2;
          end
          default: ;
        endcase
      end

      default: ;
    endcase
  end
end

wire _unused_ok = &{1'b0,
  csr_rdata_save1[12:11],
  1'b0};

endmodule

// ZhengpuShi

// Memory Interface


module ysyx_210544_mem_stage(
  input   wire                clk,
  input   wire                rst,
  input   reg                 i_mem_executed_req,
  output  reg                 o_mem_executed_ack,
  output  reg                 o_mem_memoryed_req,
  input   reg                 i_mem_memoryed_ack,
  input   wire  [`BUS_64]     i_mem_pc,
  input   wire  [`BUS_32]     i_mem_inst,
  input   wire  [`BUS_RIDX]   i_mem_rd,
  input   wire                i_mem_rd_wen,
  input   wire  [`BUS_64]     i_mem_rd_wdata,
  input   wire                i_mem_nocmt,
  input   wire                i_mem_skipcmt,
  input   wire  [7 : 0]       i_mem_inst_opcode,
  input   wire  [`BUS_64]     i_mem_op1,
  input   wire  [`BUS_64]     i_mem_op2,
  input   wire  [`BUS_64]     i_mem_op3,
  output  wire  [`BUS_RIDX]   o_mem_rd,
  output  wire                o_mem_rd_wen,
  output  wire  [`BUS_64]     o_mem_rd_wdata,
  output  wire  [`BUS_64]     o_mem_pc,
  output  wire  [`BUS_32]     o_mem_inst,
  output  wire                o_mem_nocmt,
  output  wire                o_mem_skipcmt,
  output  wire                o_mem_clint_mtime_overflow,
  input   wire  [`BUS_32]     i_mem_intrNo,
  output  reg   [`BUS_32]     o_mem_intrNo,

  ///////////////////////////////////////////////
  // DCache interface
  output  wire                o_dcache_req,
  output  wire  [63:0]        o_dcache_addr,
  output  wire                o_dcache_op,
  output  wire  [2 :0]        o_dcache_bytes,
  output  wire  [63:0]        o_dcache_wdata,
  input   wire                i_dcache_ack,
  input   wire  [63:0]        i_dcache_rdata
);


assign o_mem_executed_ack = 1'b1;

wire executed_hs = i_mem_executed_req & o_mem_executed_ack;
wire memoryed_hs = i_mem_memoryed_ack & o_mem_memoryed_req;

wire addr_is_mem  = (mem_addr[31:24] == 8'h80) | (mem_addr[31:24] == 8'h10) | (mem_addr[31:24] == 8'h30);
wire addr_is_mmio = (mem_addr[31:24] == 8'h02);// & (64'hFF000000)) == 64'h02000000;

// channel select, only valid in one pulse
wire ch_mem   = addr_is_mem & (mem_ren | mem_wen);
wire ch_mmio  = addr_is_mmio & (mem_ren | mem_wen);
wire ch_none  = (!(addr_is_mem | addr_is_mmio)) | (!(mem_ren | mem_wen));

// memoryed request for different slaves
wire                  memoryed_req_mem;
wire                  memoryed_req_mmio;
wire                  memoryed_req_none;
wire   [`BUS_64]      rdata_mem;      // readed data from mmio
wire   [`BUS_64]      rdata_mmio;     // readed data from main memory
reg    [`BUS_64]      rdata;          // readed data from main memory or mmio

// o_mem_memoryed_req
always @(*) begin
  if (rst) begin
    o_mem_memoryed_req = 0;
  end
  else if (tmp_ch_mem) begin
    o_mem_memoryed_req = memoryed_req_mem;
  end
  else if (tmp_ch_mmio) begin
    o_mem_memoryed_req = memoryed_req_mmio;
  end
  else begin
    o_mem_memoryed_req = memoryed_req_none;
  end
end

// rdata
always @(*) begin
  if (rst) begin
    rdata = 0;
  end
  else if (tmp_ch_mem) begin
    rdata = rdata_mem;
  end
  else if (tmp_ch_mmio) begin
    rdata = rdata_mmio;
  end
  else begin
    rdata = 0;
  end
end

// 保存输入信息
reg   [`BUS_64]               tmp_i_mem_pc;
reg   [`BUS_32]               tmp_i_mem_inst;
reg   [`BUS_RIDX]             tmp_i_mem_rd;
reg                           tmp_i_mem_rd_wen;
reg   [`BUS_64]               tmp_i_mem_rd_wdata;
reg   [7 : 0]                 tmp_i_mem_inst_opcode;
reg                           tmp_i_mem_nocmt;
reg                           tmp_i_mem_skipcmt;
reg                           tmp_ch_mem;
reg                           tmp_ch_mmio;

reg  [63:0] mem_addr;
reg  [2:0]  mem_bytes;
reg         mem_ren;
reg         mem_wen;
wire [63:0] rdata_mem;
reg  [63:0] mem_wdata;



// o_mem_memoryed_req
always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_mem_pc,
      tmp_i_mem_inst,
      tmp_i_mem_rd,
      tmp_i_mem_rd_wen,
      tmp_i_mem_rd_wdata,
      tmp_i_mem_inst_opcode,
      tmp_i_mem_nocmt,
      tmp_i_mem_skipcmt,
      tmp_ch_mem,
      tmp_ch_mmio
    } <= 0;

    o_mem_intrNo <= 0;
  end
  else begin
    if (executed_hs) begin
      tmp_i_mem_pc              <= i_mem_pc;
      tmp_i_mem_inst            <= i_mem_inst;
      tmp_i_mem_inst_opcode     <= i_mem_inst_opcode;
      tmp_i_mem_rd              <= i_mem_rd;
      tmp_i_mem_rd_wen          <= i_mem_rd_wen;
      tmp_i_mem_rd_wdata        <= i_mem_rd_wdata;
      tmp_i_mem_nocmt           <= i_mem_nocmt;
      tmp_i_mem_skipcmt         <= i_mem_skipcmt;
      tmp_ch_mem                <= ch_mem;
      tmp_ch_mmio               <= ch_mmio;

      o_mem_intrNo <= i_mem_intrNo;
    end
    else if (memoryed_hs) begin
      // 该通道号需要消除，不能留到下一个指令
      tmp_ch_mem                <= 0;
      tmp_ch_mmio               <= 0;

      o_mem_intrNo <= 0;

    end
  end
end

assign o_mem_pc           = tmp_i_mem_pc;
assign o_mem_inst         = tmp_i_mem_inst;
assign o_mem_rd           = tmp_i_mem_rd;
assign o_mem_rd_wen       = tmp_i_mem_rd_wen;
assign o_mem_rd_wdata     = tmp_i_mem_rd_wdata;
assign o_mem_nocmt        = tmp_i_mem_nocmt;
assign o_mem_skipcmt      = tmp_i_mem_skipcmt | tmp_ch_mmio;


// ren, only valid at one pulse
always @(*) begin
  if ( rst == 1'b1) begin
    mem_ren = 0;
  end
  else begin
    case (i_mem_inst_opcode)
      `INST_LB  : begin mem_ren = 1; end
      `INST_LBU : begin mem_ren = 1; end
      `INST_LH  : begin mem_ren = 1; end
      `INST_LHU : begin mem_ren = 1; end 
      `INST_LW  : begin mem_ren = 1; end
      `INST_LWU : begin mem_ren = 1; end
      `INST_LD  : begin mem_ren = 1; end
      default   : begin mem_ren = 0; end
    endcase
  end
end

// wen, only valid at one pulse
always @(*) begin
  if ( rst == 1'b1) begin
    mem_wen = 0;
  end
  else begin
    case (i_mem_inst_opcode)
      `INST_SB  : begin mem_wen = 1; end
      `INST_SH  : begin mem_wen = 1; end
      `INST_SW  : begin mem_wen = 1; end
      `INST_SD  : begin mem_wen = 1; end
      default   : begin mem_wen = 0; end
    endcase
  end
end

// addr, only valid at one pulse
assign mem_addr = i_mem_op1 + i_mem_op3;

// bytes, only valid at one pulse
always @(*) begin
  if ( rst == 1'b1) begin
    mem_bytes = 0;
  end
  else begin
    case (i_mem_inst_opcode)
      `INST_LB  : begin mem_bytes = 0; end
      `INST_LBU : begin mem_bytes = 0; end
      `INST_SB  : begin mem_bytes = 0; end
      `INST_LH  : begin mem_bytes = 1; end
      `INST_LHU : begin mem_bytes = 1; end 
      `INST_SH  : begin mem_bytes = 1; end
      `INST_LW  : begin mem_bytes = 3; end
      `INST_SW  : begin mem_bytes = 3; end
      `INST_LWU : begin mem_bytes = 3; end
      `INST_LD  : begin mem_bytes = 7; end
      `INST_SD  : begin mem_bytes = 7; end
      default   : begin mem_bytes = 0; end
    endcase
  end
end

// wdata, only valid at one pulse
always @(*) begin
  if ( rst == 1'b1) begin
    mem_wdata = 0;
  end
  else begin
    case (i_mem_inst_opcode)
      `INST_SB  : begin mem_wdata = {56'd0, i_mem_op2[7:0]}; end
      `INST_SH  : begin mem_wdata = {48'd0, i_mem_op2[15:0]}; end
      `INST_SW  : begin mem_wdata = {32'd0, i_mem_op2[31:0]}; end
      `INST_SD  : begin mem_wdata = i_mem_op2[63:0]; end
      default   : begin mem_wdata = 0; end
    endcase
  end
end

// rdata, valid at several pulses
always @(*) begin
  if ( rst == 1'b1) begin
    o_mem_rd_wdata = 0;
  end
  else begin
    case (tmp_i_mem_inst_opcode)
      `INST_LB  : begin o_mem_rd_wdata = {{57{rdata[7]}}, rdata[6:0]} ; end
      `INST_LBU : begin o_mem_rd_wdata = {56'd0, rdata[7:0]}; end
      `INST_LH  : begin o_mem_rd_wdata = {{49{rdata[15]}}, rdata[14:0]}; end
      `INST_LHU : begin o_mem_rd_wdata = {48'd0, rdata[15:0]}; end
      `INST_LW  : begin o_mem_rd_wdata = {{33{rdata[31]}}, rdata[30:0]}; end
      `INST_LWU : begin o_mem_rd_wdata = {32'd0, rdata[31:0]}; end
      `INST_LD  : begin o_mem_rd_wdata = rdata[63:0]; end
      default   : begin o_mem_rd_wdata = tmp_i_mem_rd_wdata; end
    endcase
  end
end

// 访问主存和外设（过AXI总线）
ysyx_210544_memU MemU(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .start                      (i_mem_executed_req & ch_mem ),
  .ack                        (i_mem_memoryed_ack         ),
  .req                        (memoryed_req_mem           ),
  .i_addr                     (mem_addr                   ),
  .i_bytes                    (mem_bytes                  ),
  .i_ren                      (mem_ren                    ),
  .i_wen                      (mem_wen                    ),
  .i_wdata                    (mem_wdata                  ),
  .o_rdata                    (rdata_mem                  ),

  .o_dcache_req               (o_dcache_req               ),
  .o_dcache_addr              (o_dcache_addr              ),
  .o_dcache_op                (o_dcache_op                ),
  .o_dcache_bytes             (o_dcache_bytes             ),
  .o_dcache_wdata             (o_dcache_wdata             ),
  .i_dcache_ack               (i_dcache_ack               ),
  .i_dcache_rdata             (i_dcache_rdata             )
);

// 访问外设（cpu内部的）
ysyx_210544_mem_mmio Mem_mmio(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .start                      (i_mem_executed_req & ch_mmio),
  .ack                        (i_mem_memoryed_ack         ),
  .req                        (memoryed_req_mmio          ), 
  .ren                        (mem_ren                    ),
  .wen                        (mem_wen                    ),
  .wdata                      (mem_wdata                  ),
  .addr                       (mem_addr                   ),
  .rdata                      (rdata_mmio                 ),
  .o_clint_mtime_overflow     (o_mem_clint_mtime_overflow )
);

// 仅握手
ysyx_210544_mem_nothing Mem_nothing(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .start                      (i_mem_executed_req & ch_none),
  .ack                        (i_mem_memoryed_ack         ),
  .req                        (memoryed_req_none          )
);

endmodule

// ZhengpuShi

// Memory Unit, 组合逻辑电路


module ysyx_210544_memU(
  input   wire                clk,
  input   wire                rst,

  input   wire                start,
  input   wire                ack,
  output  reg                 req,

  input   wire  [`BUS_64]     i_addr,
  input   wire  [2:0]         i_bytes,
  input   wire                i_ren,
  input   wire                i_wen,
  input   wire  [`BUS_64]     i_wdata,
  output  wire  [`BUS_64]     o_rdata,

  ///////////////////////////////////////////////
  // DCache interface
  output  wire                o_dcache_req,
  output  wire  [63:0]        o_dcache_addr,
  output  wire                o_dcache_op,
  output  wire  [2 :0]        o_dcache_bytes,
  output  wire  [63:0]        o_dcache_wdata,
  input   wire                i_dcache_ack,
  input   wire  [63:0]        i_dcache_rdata
);


wire hs_dcache  = o_dcache_req & i_dcache_ack;

reg wait_finish;  // 是否等待访存完毕？

always @(posedge clk) begin
  if (rst) begin
    wait_finish    <= 0;
    req <= 0;
  end
  else begin
    if (start) begin
      if (i_ren) begin
        o_dcache_req      <= 1;
        o_dcache_op       <= `REQ_READ;
        o_dcache_addr     <= i_addr;
        o_dcache_bytes    <= i_bytes;
        wait_finish       <= 1;
      end
      else if (i_wen) begin
        o_dcache_req      <= 1;
        o_dcache_op       <= `REQ_WRITE;
        o_dcache_addr     <= i_addr;
        o_dcache_bytes    <= i_bytes;
        o_dcache_wdata    <= i_wdata;
        wait_finish       <= 1;
      end
    end
    else begin
      // 等待访存完毕
      if (wait_finish) begin
        if (hs_dcache) begin
          wait_finish       <= 0;
          o_dcache_req      <= 0;
          req               <= 1;
          o_rdata           <= i_dcache_rdata;
        end
      end
      // 清除req信号
      else if (ack) begin
        req    <= 0;
      end
    end
  end
end

// assign o_rdata = i_dcache_rdata;


endmodule

// ZhengpuShi


module ysyx_210544_mem_mmio(
  input   wire                clk,
  input   wire                rst,

  input   wire                start,
  input   wire                ack,
  output  reg                 req,
  input   wire                ren,
  input   wire                wen,
  input   wire [`BUS_64]      addr,
  input   reg  [`BUS_64]      wdata,
  output  reg  [`BUS_64]      rdata,
  output  wire                o_clint_mtime_overflow
);

// rtc设备
wire  [`BUS_64]     rtc_rdata;

ysyx_210544_rtc Rtc(
  .clk                (clk              ),
  .rst                (rst              ),
  .ren                (ren & (addr == `DEV_RTC)),
  .rdata              (rtc_rdata        )
);

reg  [`BUS_64]                i_clint_rdata;


// CLINT (Core Local Interrupt Controller)
ysyx_210544_clint Clint(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_clint_addr               (addr                       ),
  .i_clint_ren                (ren                        ),
  .o_clint_rdata              (i_clint_rdata              ),
  .i_clint_wen                (wen                        ),
  .i_clint_wdata              (wdata                      ),
  .o_clint_mtime_overflow     (o_clint_mtime_overflow     )
);

always @(posedge clk) begin
  if (rst) begin
    req <= 0;
    rdata <= 0;
  end
  else begin
    // set request
    if (start) begin
      if (ren) begin
        case (addr)
          `DEV_RTC        : rdata <= rtc_rdata;
          `DEV_MTIME      : rdata <= i_clint_rdata;
          `DEV_MTIMECMP   : rdata <= i_clint_rdata;
          default         : ;
        endcase
        req <= 1;
      end
      else begin
        req <= 1;
      end
    end
    // clear request
    else if (ack) begin
      req <= 0;
      rdata <= 0;
    end
  end
end


endmodule

// ZhengpuShi


module ysyx_210544_mem_nothing(
  input   wire                clk,
  input   wire                rst,

  input   wire                start,
  input   wire                ack,
  output  reg                 req
);

always @(posedge clk) begin
  if (rst) begin
    req <= 0;
  end
  else begin
    // set request
    if (start) begin
      req <= 1;
    end
    // clear request
    else if (ack) begin
      req <= 0;
    end
  end
end


endmodule

// ZhengpuShi

// Writeback Interface


module ysyx_210544_wb_stage(
  input   wire                clk,
  input   wire                rst,
  input   reg                 i_wb_memoryed_req,
  output  reg                 o_wb_memoryed_ack,
  output  reg                 o_wb_writebacked_req,
  input   reg                 i_wb_writebacked_ack,
  input   wire  [`BUS_64]     i_wb_pc,
  input   wire  [`BUS_32]     i_wb_inst,
  input   wire  [`BUS_RIDX]   i_wb_rd,
  input   wire                i_wb_rd_wen,
  input   wire  [`BUS_64]     i_wb_rd_wdata,
  input   wire                i_wb_nocmt,
  input   wire                i_wb_skipcmt,
  output  wire  [`BUS_64]     o_wb_pc,
  output  wire  [`BUS_32]     o_wb_inst,
  output  reg   [`BUS_RIDX]   o_wb_rd,
  output  reg                 o_wb_rd_wen,
  output  wire  [`BUS_64]     o_wb_rd_wdata,
  output  reg                 o_wb_nocmt,
  output  reg                 o_wb_skipcmt,
  input   wire  [`BUS_32]     i_wb_intrNo,
  output  reg   [`BUS_32]     o_wb_intrNo
);


assign o_wb_memoryed_ack = 1'b1;

wire memoryed_hs = i_wb_memoryed_req & o_wb_memoryed_ack;

// 是否使能组合逻辑单元部件
reg                           i_ena;
wire                          i_disable = !i_ena;

// 保存输入信息
reg   [`BUS_64]               tmp_i_wb_pc;
reg   [`BUS_32]               tmp_i_wb_inst;
reg   [4 : 0]                 tmp_i_wb_rd;
reg                           tmp_i_wb_rd_wen;
reg   [`BUS_64]               tmp_i_wb_rd_wdata;
reg                           tmp_i_wb_nocmt;
reg                           tmp_i_wb_skipcmt;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_wb_pc,
      tmp_i_wb_inst,
      tmp_i_wb_rd, 
      tmp_i_wb_rd_wen, 
      tmp_i_wb_rd_wdata,
      tmp_i_wb_nocmt,
      tmp_i_wb_skipcmt
    } <= 0;

    o_wb_writebacked_req  <= 0;
    i_ena                 <= 0;

    o_wb_intrNo <= 0;
  end
  else begin
    if (memoryed_hs) begin
      tmp_i_wb_pc             <= i_wb_pc;
      tmp_i_wb_inst           <= i_wb_inst;
      tmp_i_wb_rd             <= i_wb_rd; 
      tmp_i_wb_rd_wen         <= i_wb_rd_wen;
      tmp_i_wb_rd_wdata       <= i_wb_rd_wdata;
      tmp_i_wb_nocmt          <= i_wb_nocmt;
      tmp_i_wb_skipcmt        <= i_wb_skipcmt;

      o_wb_writebacked_req  <= 1;
      i_ena                 <= 1;

      o_wb_intrNo <= i_wb_intrNo;
    end
    else if (i_wb_writebacked_ack) begin
      o_wb_writebacked_req  <= 0;
      i_ena                 <= 0;
      o_wb_intrNo <= 0;
    end
  end
end

assign o_wb_pc        = i_disable ? 0 : tmp_i_wb_pc;
assign o_wb_inst      = i_disable ? 0 : tmp_i_wb_inst;
assign o_wb_nocmt     = i_disable ? 0 : tmp_i_wb_nocmt;
assign o_wb_skipcmt   = i_disable ? 0 : tmp_i_wb_skipcmt;
assign o_wb_rd        = i_disable ? 0 : tmp_i_wb_rd;
assign o_wb_rd_wen    = i_disable ? 0 : tmp_i_wb_rd_wen;
assign o_wb_rd_wdata  = i_disable ? 0 : tmp_i_wb_rd_wdata;

endmodule

// ZhengpuShi

// Commit Interface (for difftest)


module ysyx_210544_cmt_stage(
  input   wire                clk,
  input   wire                rst,
  input   reg                 i_cmt_writebacked_req,
  output  reg                 o_cmt_writebacked_ack,
  input   wire [4 : 0]        i_cmt_rd,
  input   wire                i_cmt_rd_wen,
  input   wire [`BUS_64]      i_cmt_rd_wdata,
  input   wire [`BUS_64]      i_cmt_pc,
  input   wire [`BUS_32]      i_cmt_inst,
  input   wire                i_cmt_nocmt,
  input   wire                i_cmt_skipcmt,
  input   wire [`BUS_64]      i_cmt_regs[0 : 31],
  input   wire [`BUS_64]      i_cmt_csrs[0 : 15],
  input   wire [`BUS_32]      i_cmt_intrNo
);

assign o_cmt_writebacked_ack = 1'b1;

wire writebacked_hs = i_cmt_writebacked_req & o_cmt_writebacked_ack;

wire i_cmtvalid = writebacked_hs & (!i_cmt_nocmt);

ysyx_210544_cmtU CmtU(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_rd                       (i_cmt_rd                   ),
  .i_rd_wen                   (i_cmt_rd_wen               ),
  .i_rd_wdata                 (i_cmt_rd_wdata             ),
  .i_pc                       (i_cmt_pc                   ),
  .i_inst                     (i_cmt_inst                 ),
  .i_cmtvalid                 (i_cmtvalid                 ),
  .i_skipcmt                  (i_cmt_skipcmt              ),
  .i_regs                     (i_cmt_regs                 ),
  .i_csrs                     (i_cmt_csrs                 ),
  .i_intrNo                   (i_cmt_intrNo               )
);

reg [63:0] cnt;
always @(posedge clk) begin
  if (rst) begin
    cnt <= 1;
  end
  else begin
    
    // 判断停机
    if (i_cmt_inst == 32'h6b) begin
      if (i_cmt_regs[10] == 0) begin
        $display("*****SUCCESS!");
      end
      else begin
        $display("!!!!!FAIL!");
      end
      $finish();
    end

    // 打印执行情况
    // if (i_cmtvalid) begin
    //   cnt <= cnt + 1;
    //   if (cnt[4:0] == 0) begin
    //     $displayh("[cnt:", cnt, ", pc:", i_cmt_pc, "]");
    //   end
    // end


  end
end

wire _unused_ok = &{1'b0,
  cnt,
  1'b0};

endmodule

// ZhengpuShi

// Commit Unit (for difftest)


module ysyx_210544_cmtU(
  input   wire                clk,
  input   wire                rst,
  input   wire [`BUS_RIDX]    i_rd,
  input   wire                i_rd_wen,
  input   wire [`BUS_64]      i_rd_wdata,
  input   wire [`BUS_64]      i_pc,
  input   wire [`BUS_32]      i_inst,
  input   wire [`BUS_64]      i_regs[0 : 31],
  input   wire [`BUS_64]      i_csrs[0 : 15],
  input   wire [`BUS_32]      i_intrNo,
  input   wire                i_cmtvalid,
  input   wire                i_skipcmt
);


// Difftest
reg                           cmt_wen;
reg   [7:0]                   cmt_wdest;
reg   [`BUS_64]               cmt_wdata;
reg   [`BUS_64]               cmt_pc;
reg   [`BUS_32]               cmt_inst;
reg                           cmt_valid;
reg                           cmt_skip;       // control commit skip
reg                           trap;
reg   [2:0]                   trap_code;
reg   [`BUS_64]               cycleCnt;
reg   [`BUS_64]               instrCnt;
reg   [`BUS_64]               regs_diff [0 : 31];

reg   [`BUS_64] instrCnt_inc = i_cmtvalid ? 1 : 0;

wire  [`BUS_64] sstatus = i_csrs[`CSR_IDX_MSTATUS] & 64'h80000003_000DE122;

always @(negedge clk) begin
  if (rst) begin
    {cmt_wen, cmt_wdest, cmt_wdata, cmt_pc, cmt_inst, cmt_valid, cmt_skip, trap, trap_code, cycleCnt, instrCnt} <= 0;
  end
  else if (~trap) begin
    cmt_wen       <= i_rd_wen;
    cmt_wdest     <= {3'd0, i_rd};
    cmt_wdata     <= i_rd_wdata;
    cmt_pc        <= i_pc;
    cmt_inst      <= i_inst;
    cmt_skip      <= i_skipcmt;
    cmt_valid     <= i_cmtvalid & (i_intrNo == 0);
    regs_diff     <= i_regs;
    trap          <= i_inst[6:0] == 7'h6b;
    trap_code     <= i_regs[10][2:0];
    cycleCnt      <= cycleCnt + 1;
    instrCnt      <= instrCnt + instrCnt_inc;
  end
end


`ifndef YSYXSOC

DifftestArchEvent DifftestArchEvent(
  .clock              (clk),		// 时钟
  .coreid             (0),		  // cpu id，单核时固定为0
  .intrNO             (i_intrNo),		  // 中断号，非零有效
  .cause              (0),			// 异常号，非零有效
  .exceptionPC        (i_intrNo > 0 ? i_pc : 0),	// 产生异常或中断时的PC
  .exceptionInst      (0)	  // 产生异常时的指令，未使用
);

DifftestInstrCommit DifftestInstrCommit(
  .clock              (clk),
  .coreid             (0),
  .index              (0),
  .valid              (cmt_valid),
  .pc                 (cmt_pc),
  .instr              (cmt_inst),
  .skip               (cmt_skip),
  .isRVC              (0),
  .scFailed           (0),
  .wen                (cmt_wen),
  .wdest              (cmt_wdest),
  .wdata              (cmt_wdata)
);

DifftestArchIntRegState DifftestArchIntRegState (
  .clock              (clk),
  .coreid             (0),
  .gpr_0              (regs_diff[0]),
  .gpr_1              (regs_diff[1]),
  .gpr_2              (regs_diff[2]),
  .gpr_3              (regs_diff[3]),
  .gpr_4              (regs_diff[4]),
  .gpr_5              (regs_diff[5]),
  .gpr_6              (regs_diff[6]),
  .gpr_7              (regs_diff[7]),
  .gpr_8              (regs_diff[8]),
  .gpr_9              (regs_diff[9]),
  .gpr_10             (regs_diff[10]),
  .gpr_11             (regs_diff[11]),
  .gpr_12             (regs_diff[12]),
  .gpr_13             (regs_diff[13]),
  .gpr_14             (regs_diff[14]),
  .gpr_15             (regs_diff[15]),
  .gpr_16             (regs_diff[16]),
  .gpr_17             (regs_diff[17]),
  .gpr_18             (regs_diff[18]),
  .gpr_19             (regs_diff[19]),
  .gpr_20             (regs_diff[20]),
  .gpr_21             (regs_diff[21]),
  .gpr_22             (regs_diff[22]),
  .gpr_23             (regs_diff[23]),
  .gpr_24             (regs_diff[24]),
  .gpr_25             (regs_diff[25]),
  .gpr_26             (regs_diff[26]),
  .gpr_27             (regs_diff[27]),
  .gpr_28             (regs_diff[28]),
  .gpr_29             (regs_diff[29]),
  .gpr_30             (regs_diff[30]),
  .gpr_31             (regs_diff[31])
);

DifftestTrapEvent DifftestTrapEvent(
  .clock              (clk),
  .coreid             (0),
  .valid              (trap),
  .code               (trap_code),
  .pc                 (cmt_pc),
  .cycleCnt           (cycleCnt),
  .instrCnt           (instrCnt)
);

DifftestCSRState DifftestCSRState(
  .clock              (clk),
  .coreid             (0),
  .priviledgeMode     (`RISCV_PRIV_MODE_M),
  .mstatus            (i_csrs[`CSR_IDX_MSTATUS]),
  .sstatus            (sstatus),
  .mepc               (i_csrs[`CSR_IDX_MEPC]),
  .sepc               (0),
  .mtval              (0),
  .stval              (0),
  .mtvec              (i_csrs[`CSR_IDX_MTVEC]),
  .stvec              (0),
  .mcause             (i_csrs[`CSR_IDX_MCAUSE]),
  .scause             (0),
  .satp               (0),
  .mip                (0),
  .mie                (i_csrs[`CSR_IDX_MIE]),
  .mscratch           (i_csrs[`CSR_IDX_MSCRATCH]),
  .sscratch           (0),
  .mideleg            (0),
  .medeleg            (0)
);

DifftestArchFpRegState DifftestArchFpRegState(
  .clock              (clk),
  .coreid             (0),
  .fpr_0              (0),
  .fpr_1              (0),
  .fpr_2              (0),
  .fpr_3              (0),
  .fpr_4              (0),
  .fpr_5              (0),
  .fpr_6              (0),
  .fpr_7              (0),
  .fpr_8              (0),
  .fpr_9              (0),
  .fpr_10             (0),
  .fpr_11             (0),
  .fpr_12             (0),
  .fpr_13             (0),
  .fpr_14             (0),
  .fpr_15             (0),
  .fpr_16             (0),
  .fpr_17             (0),
  .fpr_18             (0),
  .fpr_19             (0),
  .fpr_20             (0),
  .fpr_21             (0),
  .fpr_22             (0),
  .fpr_23             (0),
  .fpr_24             (0),
  .fpr_25             (0),
  .fpr_26             (0),
  .fpr_27             (0),
  .fpr_28             (0),
  .fpr_29             (0),
  .fpr_30             (0),
  .fpr_31             (0)
);

`else

wire _unused_ok = &{1'b0,
  cmt_wen,
  cmt_wdest,
  cmt_wdata,
  cmt_pc,
  cmt_inst,
  cmt_valid,
  cmt_skip,
  trap_code,
  regs_diff,
  sstatus,
  1'b0};

`endif

endmodule

// ZhengpuShi


module ysyx_210544_cpu(
  input                       clk,
  input                       rst,

  // AXI interface
  input   wire  [511:0]       i_axi_io_rdata,
  input   wire                i_axi_io_ready,
  output  wire                o_axi_io_valid,
  output  wire                o_axi_io_op,
  output  wire  [511:0]       o_axi_io_wdata,
  output  wire  [63:0]        o_axi_io_addr,
  output  wire  [2:0]         o_axi_io_size,
  output  wire  [7:0]         o_axi_io_blks
);


// Special Instruction: putch a0
// wire                          putch_wen;
// wire [7 : 0]                  putch_wdata;
// assign putch_wen              = o_if_inst == 32'h7b;
// assign putch_wdata            = (!putch_wen) ? 0 : (o_reg_regs[10][7:0]); 

// 方式一：缓存一行后再$write打印。
// putch Putch(
//   .clk                (clk              ),
//   .rst                (rst              ),
//   .wen                (putch_wen        ),
//   .wdata              (putch_wdata      ) 
// );

// 方式二：使用$write打印。
always @(posedge clk) begin
  if (o_if_inst == 32'h7b) begin
    $write("%c", o_reg_regs[10][7:0]);
    $fflush();
  end
end

// 方式三：交给上层c++代码来打印
// assign io_uart_out_valid = putch_wen;
// assign io_uart_out_ch = putch_wdata;



// handshake between five stages
wire                          fetched_req;
wire                          decoded_req;
wire                          decoded_ack;
wire                          executed_req;
wire                          executed_ack;
wire                          memoryed_req;
wire                          memoryed_ack;
wire                          writebacked_req;
wire                          writebacked_ack;

// if_stage
// if_stage -> id_stage
wire  [`BUS_64]               o_if_pc;
wire  [`BUS_32]               o_if_inst;
wire                          o_if_nocmt;

// id_stage
// id_stage -> regfile
wire                          o_id_rs1_ren;
wire  [`BUS_RIDX]             o_id_rs1;
wire                          o_id_rs2_ren;
wire  [`BUS_RIDX]             o_id_rs2;
// id_stage -> exe_stage
wire  [`BUS_RIDX]             o_id_rd;
wire                          o_id_rd_wen;
wire  [7 : 0]                 o_id_inst_opcode;
wire  [`BUS_64]               o_id_op1;
wire  [`BUS_64]               o_id_op2;
wire  [`BUS_64]               o_id_op3;
wire                          o_id_nocmt;
wire                          o_id_skipcmt;
wire  [`BUS_64]               o_id_pc;
wire  [`BUS_32]               o_id_inst;

// exe_stage
// exe_stage -> mem_stage
wire  [`BUS_64]               o_ex_pc;
wire  [`BUS_32]               o_ex_inst;
wire                          o_ex_pc_jmp;
wire  [`BUS_64]               o_ex_pc_jmpaddr;
wire  [7 : 0]                 o_ex_inst_opcode;
wire  [`BUS_RIDX]             o_ex_rd;
wire                          o_ex_rd_wen;
wire  [`BUS_64]               o_ex_rd_wdata;
wire  [`BUS_64]               o_ex_op1;
wire  [`BUS_64]               o_ex_op2;
wire  [`BUS_64]               o_ex_op3;
wire                          o_ex_nocmt;
wire                          o_ex_skipcmt;
wire  [`BUS_32]               o_ex_intrNo;

// ex_stage -> csrfile
wire  [11 : 0]                o_ex_csr_addr;
wire                          o_ex_csr_ren;
wire                          o_ex_csr_wen;
wire                          o_ex_csr_wen;
wire  [`BUS_64]               o_ex_csr_wdata;

// mem_stage
// mem_stage -> wb_stage
wire  [`BUS_64]               o_mem_pc;
wire  [`BUS_32]               o_mem_inst;
wire  [`BUS_RIDX]             o_mem_rd;
wire                          o_mem_rd_wen;
wire  [`BUS_64]               o_mem_rd_wdata;
wire                          o_mem_nocmt;
wire                          o_mem_skipcmt;
wire  [`BUS_32]               o_mem_intrNo;

// wb_stage
// wb_stage -> cmt_stage
wire  [`BUS_64]               o_wb_pc;
wire  [`BUS_32]               o_wb_inst;
wire                          o_wb_nocmt;
wire                          o_wb_skipcmt;
wire  [`BUS_32]               o_wb_intrNo;
// wb_stage -> regfile
wire  [`BUS_RIDX]             o_wb_rd;
reg                           o_wb_rd_wen;
wire  [`BUS_64]               o_wb_rd_wdata;

// regfile
// regfile -> id_stage
wire  [`BUS_64]               o_reg_id_rs1_data;
wire  [`BUS_64]               o_reg_id_rs2_data;
// regfile -> difftest
wire  [`BUS_64]               o_reg_regs[0 : 31];

// csrfile
// csrfile -> ex_stage
wire  [`BUS_64]               o_csr_rdata;
// csrfile -> wb_stage
wire  [`BUS_64]               o_csr_csrs[0 :  15];

// clint
wire                          o_clint_mstatus_mie;
wire                          o_clint_mie_mtie;
wire                          o_clint_mtime_overflow;

/////////////////////////////////////////////////

wire                          o_icache_req;
wire  [63:0]                  o_icache_addr;
reg                           i_icache_ack;
reg   [31:0]                  i_icache_rdata;

wire                          o_dcache_req;
wire  [63:0]                  o_dcache_addr;
wire                          o_dcache_op;
wire  [2 :0]                  o_dcache_bytes;
wire  [63:0]                  o_dcache_wdata;
reg                           i_dcache_ack;
reg   [63:0]                  i_dcache_rdata;

ysyx_210544_cache Cache (
  .clk                        (clk                        ),
  .rst                        (rst                        ),

    // ICache
  .i_icache_req               (o_icache_req               ),
  .i_icache_addr              (o_icache_addr              ),
  .o_icache_ack               (i_icache_ack               ),
  .o_icache_rdata             (i_icache_rdata             ),

    // DCache
  .i_dcache_req               (o_dcache_req               ),
  .i_dcache_addr              (o_dcache_addr              ),
  .i_dcache_op                (o_dcache_op                ),
  .i_dcache_bytes             (o_dcache_bytes             ),
  .i_dcache_wdata             (o_dcache_wdata             ),
  .o_dcache_ack               (i_dcache_ack               ),
  .o_dcache_rdata             (i_dcache_rdata             ),

  // AXI
  .i_axi_io_ready             (i_axi_io_ready             ),
  .i_axi_io_rdata             (i_axi_io_rdata             ),
  .o_axi_io_op                (o_axi_io_op                ),
  .o_axi_io_valid             (o_axi_io_valid             ),
  .o_axi_io_wdata             (o_axi_io_wdata             ),
  .o_axi_io_addr              (o_axi_io_addr              ),
  .o_axi_io_size              (o_axi_io_size              ),
  .o_axi_io_blks              (o_axi_io_blks              )
);


/////////////////////////////////////////////////
// Stages
ysyx_210544_if_stage If_stage(
  .rst                        (rst                        ),
  .clk                        (clk                        ),
  .i_if_writebacked_req       (writebacked_req            ),
  .o_if_fetched_req           (fetched_req                ),
  .o_if_bus_req               (o_icache_req               ),
  .i_if_bus_ack               (i_icache_ack               ),
  .i_if_bus_rdata             (i_icache_rdata             ),
  .o_if_bus_addr              (o_icache_addr              ),
  .i_if_pc_jmp                (o_ex_pc_jmp                ),
  .i_if_pc_jmpaddr            (o_ex_pc_jmpaddr            ),
  .o_if_pc                    (o_if_pc                    ),
  .o_if_inst                  (o_if_inst                  ),
  .o_if_nocmt                 (o_if_nocmt                 ) 
);

ysyx_210544_id_stage Id_stage(
  .rst                        (rst                        ),
  .clk                        (clk                        ),
  .i_id_fetched_req           (fetched_req                ),
  .o_id_decoded_req           (decoded_req                ),
  .i_id_decoded_ack           (decoded_ack                ),
  .i_id_pc                    (o_if_pc                    ),
  .i_id_inst                  (o_if_inst                  ),
  .i_id_rs1_data              (o_reg_id_rs1_data          ),
  .i_id_rs2_data              (o_reg_id_rs2_data          ),
  .i_id_nocmt                 (o_if_nocmt                 ),
  .o_id_pc                    (o_id_pc                    ),
  .o_id_inst_opcode           (o_id_inst_opcode           ),
  .o_id_inst                  (o_id_inst                  ),
  .o_id_rs1_ren               (o_id_rs1_ren               ),
  .o_id_rs1                   (o_id_rs1                   ),
  .o_id_rs2_ren               (o_id_rs2_ren               ),
  .o_id_rs2                   (o_id_rs2                   ),
  .o_id_rd                    (o_id_rd                    ),
  .o_id_rd_wen                (o_id_rd_wen                ),
  .o_id_op1                   (o_id_op1                   ),
  .o_id_op2                   (o_id_op2                   ),
  .o_id_op3                   (o_id_op3                   ),
  .o_id_nocmt                 (o_id_nocmt                 ),
  .o_id_skipcmt               (o_id_skipcmt               )
);

ysyx_210544_exe_stage Exe_stage(
  .rst                        (rst                        ),
  .clk                        (clk                        ),
  .i_ex_decoded_req           (decoded_req                ),
  .o_ex_decoded_ack           (decoded_ack                ),
  .o_ex_executed_req          (executed_req               ),
  .i_ex_executed_ack          (executed_ack               ),
  .i_ex_inst_opcode           (o_id_inst_opcode           ),
  .i_ex_pc                    (o_id_pc                    ),
  .i_ex_inst                  (o_id_inst                  ),
  .i_ex_op1                   (o_id_op1                   ),
  .i_ex_op2                   (o_id_op2                   ),
  .i_ex_op3                   (o_id_op3                   ),
  .i_ex_rd                    (o_id_rd                    ),
  .i_ex_rd_wen                (o_id_rd_wen                ),
  .i_ex_nocmt                 (o_id_nocmt                 ),
  .i_ex_skipcmt               (o_id_skipcmt               ),
  .i_ex_clint_mstatus_mie     (o_clint_mstatus_mie        ),
  .i_ex_clint_mie_mtie        (o_clint_mie_mtie           ),
  .i_ex_clint_mtime_overflow  (o_clint_mtime_overflow     ),
  .o_ex_pc                    (o_ex_pc                    ),
  .o_ex_inst                  (o_ex_inst                  ),
  .o_ex_pc_jmp                (o_ex_pc_jmp                ),
  .o_ex_pc_jmpaddr            (o_ex_pc_jmpaddr            ),
  .o_ex_rd                    (o_ex_rd                    ),
  .o_ex_rd_wen                (o_ex_rd_wen                ),
  .o_ex_rd_wdata              (o_ex_rd_wdata              ),
  .o_ex_inst_opcode           (o_ex_inst_opcode           ),
  .o_ex_op1                   (o_ex_op1                   ),
  .o_ex_op2                   (o_ex_op2                   ),
  .o_ex_op3                   (o_ex_op3                   ),
  .o_ex_nocmt                 (o_ex_nocmt                 ),
  .i_ex_csr_rdata             (o_csr_rdata                ),
  .o_ex_csr_addr              (o_ex_csr_addr              ),
  .o_ex_csr_ren               (o_ex_csr_ren               ),
  .o_ex_csr_wen               (o_ex_csr_wen               ),
  .o_ex_csr_wdata             (o_ex_csr_wdata             ),
  .o_ex_skipcmt               (o_ex_skipcmt               ),
  .o_ex_intrNo                (o_ex_intrNo                )
);

ysyx_210544_mem_stage Mem_stage(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_mem_executed_req         (executed_req               ),
  .o_mem_executed_ack         (executed_ack               ),
  .o_mem_memoryed_req         (memoryed_req               ),
  .i_mem_pc                   (o_ex_pc                    ),
  .i_mem_inst                 (o_ex_inst                  ),
  .i_mem_memoryed_ack         (memoryed_ack               ),
  .i_mem_inst_opcode          (o_ex_inst_opcode           ),
  .i_mem_op1                  (o_ex_op1                   ),
  .i_mem_op2                  (o_ex_op2                   ),
  .i_mem_op3                  (o_ex_op3                   ),
  .i_mem_rd                   (o_ex_rd                    ),
  .i_mem_rd_wen               (o_ex_rd_wen                ),
  .i_mem_rd_wdata             (o_ex_rd_wdata              ),
  .i_mem_nocmt                (o_ex_nocmt                 ),
  .i_mem_skipcmt              (o_ex_skipcmt               ),
  .o_mem_rd                   (o_mem_rd                   ),
  .o_mem_rd_wen               (o_mem_rd_wen               ),
  .o_mem_rd_wdata             (o_mem_rd_wdata             ),
  .o_mem_pc                   (o_mem_pc                   ),
  .o_mem_inst                 (o_mem_inst                 ),
  .o_mem_nocmt                (o_mem_nocmt                ),
  .o_mem_skipcmt              (o_mem_skipcmt              ),
  .o_mem_clint_mtime_overflow (o_clint_mtime_overflow     ),
  .i_mem_intrNo               (o_ex_intrNo                ),
  .o_mem_intrNo               (o_mem_intrNo               ),

  .o_dcache_req               (o_dcache_req               ),
  .o_dcache_addr              (o_dcache_addr              ),
  .o_dcache_op                (o_dcache_op                ),
  .o_dcache_bytes             (o_dcache_bytes             ),
  .o_dcache_wdata             (o_dcache_wdata             ),
  .i_dcache_ack               (i_dcache_ack               ),
  .i_dcache_rdata             (i_dcache_rdata             )
);

ysyx_210544_wb_stage Wb_stage(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_wb_memoryed_req          (memoryed_req               ),
  .o_wb_memoryed_ack          (memoryed_ack               ),
  .o_wb_writebacked_req       (writebacked_req            ),
  .i_wb_writebacked_ack       (writebacked_ack            ),
  .i_wb_pc                    (o_mem_pc                   ),
  .i_wb_inst                  (o_mem_inst                 ),
  .i_wb_rd                    (o_mem_rd                   ),
  .i_wb_rd_wen                (o_mem_rd_wen               ),
  .i_wb_rd_wdata              (o_mem_rd_wdata             ),
  .i_wb_nocmt                 (o_mem_nocmt                ),
  .i_wb_skipcmt               (o_mem_skipcmt              ),
  .o_wb_pc                    (o_wb_pc                    ),
  .o_wb_inst                  (o_wb_inst                  ),
  .o_wb_rd                    (o_wb_rd                    ),
  .o_wb_rd_wen                (o_wb_rd_wen                ),
  .o_wb_rd_wdata              (o_wb_rd_wdata              ),
  .o_wb_nocmt                 (o_wb_nocmt                 ),
  .o_wb_skipcmt               (o_wb_skipcmt               ),
  .i_wb_intrNo                (o_mem_intrNo               ),
  .o_wb_intrNo                (o_wb_intrNo                )
);

ysyx_210544_cmt_stage Cmt_stage(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_cmt_writebacked_req      (writebacked_req            ),
  .o_cmt_writebacked_ack      (writebacked_ack            ),
  .i_cmt_rd                   (o_wb_rd                    ),
  .i_cmt_rd_wen               (o_wb_rd_wen                ),
  .i_cmt_rd_wdata             (o_wb_rd_wdata              ),
  .i_cmt_pc                   (o_wb_pc                    ),
  .i_cmt_inst                 (o_wb_inst                  ),
  .i_cmt_nocmt                (o_wb_nocmt                 ),
  .i_cmt_skipcmt              (o_wb_skipcmt               ),
  .i_cmt_regs                 (o_reg_regs                 ),
  .i_cmt_csrs                 (o_csr_csrs                 ),
  .i_cmt_intrNo               (o_wb_intrNo                )
);

ysyx_210544_regfile Regfile(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_rs1                      (o_id_rs1                   ),
  .i_rs1_ren                  (o_id_rs1_ren               ),
  .i_rs2                      (o_id_rs2                   ),
  .i_rs2_ren                  (o_id_rs2_ren               ),
  .i_rd                       (o_wb_rd                    ),
  .i_rd_wen                   (o_wb_rd_wen                ),
  .i_rd_data                  (o_wb_rd_wdata              ),
  .o_rs1_data                 (o_reg_id_rs1_data          ),
  .o_rs2_data                 (o_reg_id_rs2_data          ),
  .o_regs                     (o_reg_regs                 )
);

ysyx_210544_csrfile Csrfile(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_csr_addr                 (o_ex_csr_addr              ),
  .i_csr_ren                  (o_ex_csr_ren               ),
  .i_csr_wen                  (o_ex_csr_wen               ),
  .i_csr_wdata                (o_ex_csr_wdata             ),
  .o_csr_rdata                (o_csr_rdata                ),
  .o_csr_clint_mstatus_mie    (o_clint_mstatus_mie        ),
  .o_csr_clint_mie_mtie       (o_clint_mie_mtie           ),
  .o_csrs                     (o_csr_csrs                 )
);

endmodule

module ysyx_210544(
  input         clock,
  input         reset,
  input         io_interrupt,
  input         io_master_awready,
  output        io_master_awvalid,
  output [31:0] io_master_awaddr,
  output [3:0]  io_master_awid,
  output [7:0]  io_master_awlen,
  output [2:0]  io_master_awsize,
  output [1:0]  io_master_awburst,
  input         io_master_wready,
  output        io_master_wvalid,
  output [63:0] io_master_wdata,
  output [7:0]  io_master_wstrb,
  output        io_master_wlast,
  output        io_master_bready,
  input         io_master_bvalid,
  input  [1:0]  io_master_bresp,
  input  [3:0]  io_master_bid,
  input         io_master_arready,
  output        io_master_arvalid,
  output [31:0] io_master_araddr,
  output [3:0]  io_master_arid,
  output [7:0]  io_master_arlen,
  output [2:0]  io_master_arsize,
  output [1:0]  io_master_arburst,
  output        io_master_rready,
  input         io_master_rvalid,
  input  [1:0]  io_master_rresp,
  input  [63:0] io_master_rdata,
  input         io_master_rlast,
  input  [3:0]  io_master_rid,
  output        io_slave_awready,
  input         io_slave_awvalid,
  input  [31:0] io_slave_awaddr,
  input  [3:0]  io_slave_awid,
  input  [7:0]  io_slave_awlen,
  input  [2:0]  io_slave_awsize,
  input  [1:0]  io_slave_awburst,
  output        io_slave_wready,
  input         io_slave_wvalid,
  input  [63:0] io_slave_wdata,
  input  [7:0]  io_slave_wstrb,
  input         io_slave_wlast,
  input         io_slave_bready,
  output        io_slave_bvalid,
  output [1:0]  io_slave_bresp,
  output [3:0]  io_slave_bid,
  output        io_slave_arready,
  input         io_slave_arvalid,
  input  [31:0] io_slave_araddr,
  input  [3:0]  io_slave_arid,
  input  [7:0]  io_slave_arlen,
  input  [2:0]  io_slave_arsize,
  input  [1:0]  io_slave_arburst,
  input         io_slave_rready,
  output        io_slave_rvalid,
  output [1:0]  io_slave_rresp,
  output [63:0] io_slave_rdata,
  output        io_slave_rlast,
  output [3:0]  io_slave_rid
);

wire [63:0] axi_aw_addr_o;
wire [63:0] axi_ar_addr_o;

assign io_master_awaddr = axi_aw_addr_o[31:0];
assign io_master_araddr = axi_ar_addr_o[31:0];

ysyx_210544_axi_rw u_axi_rw (
    .clock                          (clock),
    .reset                          (reset),

    .user_ready_o                   (i_user_axi_ready),
    .user_rdata_o                   (i_user_axi_rdata),
    .user_req_i                     (o_user_axi_op),
    .user_valid_i                   (o_user_axi_valid),
    .user_wdata_i                   (o_user_axi_wdata),
    .user_addr_i                    (o_user_axi_addr),
    .user_size_i                    (o_user_axi_size),
    .user_blks_i                    (o_user_axi_blks),
    .user_resp_o                    (o_user_axi_resp),

    .axi_aw_ready_i                 (io_master_awready),
    .axi_aw_valid_o                 (io_master_awvalid),
    .axi_aw_addr_o                  (axi_aw_addr_o),
    .axi_aw_id_o                    (io_master_awid),
    .axi_aw_len_o                   (io_master_awlen),
    .axi_aw_size_o                  (io_master_awsize),
    .axi_aw_burst_o                 (io_master_awburst),

    .axi_w_ready_i                  (io_master_wready),
    .axi_w_valid_o                  (io_master_wvalid),
    .axi_w_data_o                   (io_master_wdata),
    .axi_w_strb_o                   (io_master_wstrb),
    .axi_w_last_o                   (io_master_wlast),
    
    .axi_b_ready_o                  (io_master_bready),
    .axi_b_valid_i                  (io_master_bvalid),
    .axi_b_resp_i                   (io_master_bresp),
    .axi_b_id_i                     (io_master_bid),

    .axi_ar_ready_i                 (io_master_arready),
    .axi_ar_valid_o                 (io_master_arvalid),
    .axi_ar_addr_o                  (axi_ar_addr_o),
    .axi_ar_id_o                    (io_master_arid),
    .axi_ar_len_o                   (io_master_arlen),
    .axi_ar_size_o                  (io_master_arsize),
    .axi_ar_burst_o                 (io_master_arburst),
    
    .axi_r_ready_o                  (io_master_rready),
    .axi_r_valid_i                  (io_master_rvalid),
    .axi_r_resp_i                   (io_master_rresp),
    .axi_r_data_i                   (io_master_rdata),
    .axi_r_last_i                   (io_master_rlast),
    .axi_r_id_i                     (io_master_rid)
);


/////////////////////////////////////////////////
// axi_rw 接口
wire                          i_user_axi_ready;
wire [511:0]                  i_user_axi_rdata;
wire                          o_user_axi_op;
wire                          o_user_axi_valid;
wire [511:0]                  o_user_axi_wdata;
wire [63:0]                   o_user_axi_addr;
wire [2:0]                    o_user_axi_size;
wire [7:0]                    o_user_axi_blks;

wire [1:0]                    o_user_axi_resp;


// 使用Verilator快速编译的测试，尝试修改这里的内容，看看soc编译需要多久
reg tmp;
always @(posedge clock) begin
  if (reset) begin
    tmp <= 0;
  end
  else begin
    if (!tmp) begin
      tmp <= 1;
      $display("TEST by Steven. 2021.09.25 12:17\n");
    end
  end
end

/////////////////////////////////////////////////
// CPU核
ysyx_210544_cpu u_cpu(
  .clk                        (clock                      ),
  .rst                        (reset                      ),
  .i_axi_io_ready             (i_user_axi_ready           ),
  .i_axi_io_rdata             (i_user_axi_rdata           ),
  .o_axi_io_op                (o_user_axi_op              ),
  .o_axi_io_valid             (o_user_axi_valid           ),
  .o_axi_io_wdata             (o_user_axi_wdata           ),
  .o_axi_io_addr              (o_user_axi_addr            ),
  .o_axi_io_size              (o_user_axi_size            ),
  .o_axi_io_blks              (o_user_axi_blks            )
);


// io_slave 处理

assign io_slave_awready = 0;
assign io_slave_wready = 0;
assign io_slave_bvalid = 0;
assign io_slave_bresp = 0;
assign io_slave_bid = 0;
assign io_slave_arready = 0;
assign io_slave_rvalid = 0;
assign io_slave_rresp = 0;
assign io_slave_rdata = 0;
assign io_slave_rlast = 0;
assign io_slave_rid = 0;

wire _unused_ok = &{1'b0,
  io_interrupt,
  io_slave_awaddr,
  io_slave_awid,
  io_slave_awlen,
  io_slave_awsize,
  io_slave_awburst,
  io_slave_awvalid,
  io_slave_wvalid,
  io_slave_wdata,
  io_slave_wstrb,
  io_slave_wlast,
  io_slave_bready,
  io_slave_arvalid,
  io_slave_araddr,
  io_slave_arid,
  io_slave_arlen,
  io_slave_arsize,
  io_slave_arburst,
  io_slave_rready,
  axi_aw_addr_o[63:32],
  axi_ar_addr_o[63:32],
  o_user_axi_resp,
  1'b0};

endmodule
