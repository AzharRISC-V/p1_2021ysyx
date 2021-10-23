/* verilator lint_off DECLFILENAME */

// ZhengpuShi

// Definitions


`define YSYX210544_ZERO_WORD           64'h00000000_00000000

`ifdef YSYX210544_DIFFTEST_FLAG
`define YSYX210544_PC_START            64'h00000000_80000000
`else
`define YSYX210544_PC_START            64'h00000000_30000000
`endif

`define YSYX210544_SIZE_B              3'b000
`define YSYX210544_SIZE_H              3'b001
`define YSYX210544_SIZE_W              3'b010
`define YSYX210544_SIZE_D              3'b011

`define YSYX210544_REQ_READ            1'b0
`define YSYX210544_REQ_WRITE           1'b1

`define YSYX210544_RW_DATA_WIDTH       512

`define YSYX210544_RISCV_PRIV_MODE_U   0
`define YSYX210544_RISCV_PRIV_MODE_S   1
`define YSYX210544_RISCV_PRIV_MODE_M   3


`define YSYX210544_CLOCKS_PER_SECOND   64'd240_0000        // 每秒的clock数，约240万

`define YSYX210544_BUS_8               7:0
`define YSYX210544_BUS_16              15:0
`define YSYX210544_BUS_32              31:0
`define YSYX210544_BUS_64              63:0
`define YSYX210544_BUS_RIDX            4:0                 // 寄存器索引的总线

// CSR

// CSR addr
`define YSYX210544_CSR_ADR_MCYCLE      12'hB00
`define YSYX210544_CSR_ADR_MSTATUS     12'h300         // machine status register
`define YSYX210544_CSR_ADR_MIE         12'h304         // machine interrupt-enable register
`define YSYX210544_CSR_ADR_MTVEC       12'h305         // machine trap-handler base address
`define YSYX210544_CSR_ADR_MSCRATCH    12'h340         // scratch register for machine trap handlers.
`define YSYX210544_CSR_ADR_MEPC        12'h341         // machine exception program counter
`define YSYX210544_CSR_ADR_MCAUSE      12'h342         // machine trap cause
`define YSYX210544_CSR_ADR_MIP         12'h344         // machine interrupt pending

// 已编码的指令
`define YSYX210544_INST_NOP            32'h0000_0013   // addi x0,x0,0

// 自定义的指令码
`define YSYX210544_INST_LUI            8'b0000_0001    // d1
`define YSYX210544_INST_AUIPC          8'b0000_0010    //
`define YSYX210544_INST_JAL            8'b0000_0011    //
`define YSYX210544_INST_JALR           8'b0000_0100    //
`define YSYX210544_INST_BEQ            8'b0000_0101    //
`define YSYX210544_INST_BNE            8'b0000_0110    //
`define YSYX210544_INST_BLT            8'b0000_0111    //
`define YSYX210544_INST_BGE            8'b0000_1000    //
`define YSYX210544_INST_BLTU           8'b0000_1001    //
`define YSYX210544_INST_BGEU           8'b0000_1010    //
`define YSYX210544_INST_LB             8'b0000_1011    //
`define YSYX210544_INST_LH             8'b0000_1100    //
`define YSYX210544_INST_LW             8'b0000_1101    //
`define YSYX210544_INST_LBU            8'b0000_1110    //
`define YSYX210544_INST_LHU            8'b0000_1111    //
`define YSYX210544_INST_SB             8'b0001_0000    //
`define YSYX210544_INST_SH             8'b0001_0001    //
`define YSYX210544_INST_SW             8'b0001_0010    //
`define YSYX210544_INST_ADDI           8'b0001_0011    //
`define YSYX210544_INST_SLTI           8'b0001_0100    //
`define YSYX210544_INST_SLTIU          8'b0001_0101    //
`define YSYX210544_INST_XORI           8'b0001_0110    //
`define YSYX210544_INST_ORI            8'b0001_0111    //
`define YSYX210544_INST_ANDI           8'b0001_1000    //
`define YSYX210544_INST_SLLI           8'b0001_1001    //
`define YSYX210544_INST_SRLI           8'b0001_1010    //
`define YSYX210544_INST_SRAI           8'b0001_1011    //
`define YSYX210544_INST_ADD            8'b0001_1100    //
`define YSYX210544_INST_SUB            8'b0001_1101    //
`define YSYX210544_INST_SLL            8'b0001_1110    //
`define YSYX210544_INST_SLT            8'b0001_1111    //
`define YSYX210544_INST_SLTU           8'b0010_0000    //
`define YSYX210544_INST_XOR            8'b0010_0001    //
`define YSYX210544_INST_SRL            8'b0010_0010    //
`define YSYX210544_INST_SRA            8'b0010_0011    //
`define YSYX210544_INST_OR             8'b0010_0100    //
`define YSYX210544_INST_AND            8'b0010_0101    //
`define YSYX210544_INST_FENCE          8'b0010_0110    //
`define YSYX210544_INST_FENCEI         8'b0010_0111    //
`define YSYX210544_INST_ECALL          8'b0010_1000    //
`define YSYX210544_INST_EBREAK         8'b0010_1001    //
`define YSYX210544_INST_CSRRW          8'b0010_1010    //
`define YSYX210544_INST_CSRRS          8'b0010_1011    //
`define YSYX210544_INST_CSRRC          8'b0010_1100    //
`define YSYX210544_INST_CSRRWI         8'b0010_1101    //
`define YSYX210544_INST_CSRRSI         8'b0010_1110    //
`define YSYX210544_INST_CSRRCI         8'b0010_1111    // d47 = h2F

`define YSYX210544_INST_LWU            8'b0011_0000    //
`define YSYX210544_INST_LD             8'b0011_0001    //
`define YSYX210544_INST_SD             8'b0011_0010    //
`define YSYX210544_INST_ADDIW          8'b0011_0011    //
`define YSYX210544_INST_SLLIW          8'b0011_0100    //
`define YSYX210544_INST_SRLIW          8'b0011_0101    //
`define YSYX210544_INST_SRAIW          8'b0011_0110    //
`define YSYX210544_INST_ADDW           8'b0011_0111    //
`define YSYX210544_INST_SUBW           8'b0011_1000    //
`define YSYX210544_INST_SLLW           8'b0011_1001    //
`define YSYX210544_INST_SRLW           8'b0011_1010    //
`define YSYX210544_INST_SRAW           8'b0011_1011    //
`define YSYX210544_INST_MRET           8'b0011_1100    //

// ==  = Devices

`define YSYX210544_DEV_BASEADDR        64'h0200_0000

// RTC
`define YSYX210544_DEV_RTC_OFFSET      64'h0100
`define YSYX210544_DEV_RTC             (`YSYX210544_DEV_BASEADDR + `YSYX210544_DEV_RTC_OFFSET)

// Machine time register，以恒定频率增加，廉价的RTC软件方案
// mcycle与mtime的区别：
// 1. mcycle可随外接时钟而变化
// 2. mtime必须以恒定的频率增加（估计是因指令执行耗费的clock数不同而引起，这里需要封装差异吗）
`define YSYX210544_DEV_MTIME_OFFSET    64'hbff8
`define YSYX210544_DEV_MTIME           (`YSYX210544_DEV_BASEADDR + `YSYX210544_DEV_MTIME_OFFSET)
// Machien time compare register
// 当 mtime > = mtimecmp 时，产生计时器中断
// mip的MTIP位置1。
`define YSYX210544_DEV_MTIMECMP_OFFSET 64'h4000
`define YSYX210544_DEV_MTIMECMP        (`YSYX210544_DEV_BASEADDR + `YSYX210544_DEV_MTIMECMP_OFFSET)

// Custom MMIO area
`define YSYX210544_DEV_CUSTOM_OFFSET   64'h8000
`define YSYX210544_DEV_CUSTOM_MASK     64'hFFFF_8000
`define YSYX210544_DEV_CUSTOM          (`YSYX210544_DEV_BASEADDR + `YSYX210544_DEV_CUSTOM_OFFSET)


// AXI Read & Write Unit


// Burst types
// `define AXI_BURST_TYPE_FIXED                                2'b00
// `define AXI_BURST_TYPE_INCR                                 2'b01
// `define AXI_BURST_TYPE_WRAP                                 2'b10
// Access permissions
// `define AXI_PROT_UNPRIVILEGED_ACCESS                        3'b000
// `define AXI_PROT_PRIVILEGED_ACCESS                          3'b001
// `define AXI_PROT_SECURE_ACCESS                              3'b000
// `define AXI_PROT_NON_SECURE_ACCESS                          3'b010
// `define AXI_PROT_DATA_ACCESS                                3'b000
// `define AXI_PROT_INSTRUCTION_ACCESS                         3'b100
// Memory types (AR)
// `define AXI_ARCACHE_DEVICE_NON_BUFFERABLE                   4'b0000
// `define AXI_ARCACHE_DEVICE_BUFFERABLE                       4'b0001
// `define AXI_ARCACHE_NORMAL_NON_CACHEABLE_NON_BUFFERABLE     4'b0010
// `define AXI_ARCACHE_NORMAL_NON_CACHEABLE_BUFFERABLE         4'b0011
// `define AXI_ARCACHE_WRITE_THROUGH_NO_ALLOCATE               4'b1010
// `define AXI_ARCACHE_WRITE_THROUGH_READ_ALLOCATE             4'b1110
// `define AXI_ARCACHE_WRITE_THROUGH_WRITE_ALLOCATE            4'b1010
// `define AXI_ARCACHE_WRITE_THROUGH_READ_AND_WRITE_ALLOCATE   4'b1110
// `define AXI_ARCACHE_WRITE_BACK_NO_ALLOCATE                  4'b1011
// `define AXI_ARCACHE_WRITE_BACK_READ_ALLOCATE                4'b1111
// `define AXI_ARCACHE_WRITE_BACK_WRITE_ALLOCATE               4'b1011
// `define AXI_ARCACHE_WRITE_BACK_READ_AND_WRITE_ALLOCATE      4'b1111
// Memory types (AW)
// `define AXI_AWCACHE_DEVICE_NON_BUFFERABLE                   4'b0000
// `define AXI_AWCACHE_DEVICE_BUFFERABLE                       4'b0001
// `define AXI_AWCACHE_NORMAL_NON_CACHEABLE_NON_BUFFERABLE     4'b0010
// `define AXI_AWCACHE_NORMAL_NON_CACHEABLE_BUFFERABLE         4'b0011
// `define AXI_AWCACHE_WRITE_THROUGH_NO_ALLOCATE               4'b0110
// `define AXI_AWCACHE_WRITE_THROUGH_READ_ALLOCATE             4'b0110
// `define AXI_AWCACHE_WRITE_THROUGH_WRITE_ALLOCATE            4'b1110
// `define AXI_AWCACHE_WRITE_THROUGH_READ_AND_WRITE_ALLOCATE   4'b1110
// `define AXI_AWCACHE_WRITE_BACK_NO_ALLOCATE                  4'b0111
// `define AXI_AWCACHE_WRITE_BACK_READ_ALLOCATE                4'b0111
// `define AXI_AWCACHE_WRITE_BACK_WRITE_ALLOCATE               4'b1111
// `define AXI_AWCACHE_WRITE_BACK_READ_AND_WRITE_ALLOCATE      4'b1111

// `define AXI_SIZE_BYTES_1                                    3'b000
// `define AXI_SIZE_BYTES_2                                    3'b001
// `define AXI_SIZE_BYTES_4                                    3'b010
// `define AXI_SIZE_BYTES_8                                    3'b011
// `define AXI_SIZE_BYTES_16                                   3'b100
// `define AXI_SIZE_BYTES_32                                   3'b101
// `define AXI_SIZE_BYTES_64                                   3'b110
// `define AXI_SIZE_BYTES_128                                  3'b111

module ysyx_210544_axi_rw (
    input                               clock,
    input                               reset,

    input                               user_valid_i,
    output                              user_ready_o,
    input                               user_req_i,         // read or write
    input  [7:0]                        user_blks_i,          // blocks: 0 ~ 7， means 1~8 (后端硬件资源限制为8)
    output reg [`YSYX210544_RW_DATA_WIDTH-1:0]     user_rdata_o,
    input  [`YSYX210544_RW_DATA_WIDTH-1:0]         user_wdata_i,
    input  [63:0]                       user_addr_i,
    input  [2:0]                        user_size_i,
    output [1:0]                        user_resp_o,

    // Advanced eXtensible Interface
    input                               axi_aw_ready_i,
    output                              axi_aw_valid_o,
    output [63:0]                       axi_aw_addr_o,
    output [3:0]                        axi_aw_id_o,
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
    input  [3:0]                        axi_b_id_i,

    input                               axi_ar_ready_i,
    output                              axi_ar_valid_o,
    output [63:0]                       axi_ar_addr_o,
    output [3:0]                        axi_ar_id_o,
    output [7:0]                        axi_ar_len_o,
    output [2:0]                        axi_ar_size_o,
    output [1:0]                        axi_ar_burst_o,
    
    output                              axi_r_ready_o,
    input                               axi_r_valid_i,
    input  [1:0]                        axi_r_resp_i,
    input  [63:0]                       axi_r_data_i,
    input                               axi_r_last_i,
    input  [3:0]                        axi_r_id_i
);

parameter [1:0] W_STATE_IDLE = 2'b00, W_STATE_ADDR = 2'b01, W_STATE_WRITE = 2'b10, W_STATE_RESP = 2'b11;
parameter [1:0] R_STATE_IDLE = 2'b00, R_STATE_ADDR = 2'b01, R_STATE_READ  = 2'b10;

reg rw_ready;
wire w_trans;
wire r_trans;
wire w_valid;
wire r_valid;
wire aw_hs;
wire w_hs;
wire b_hs;
wire ar_hs;
wire r_hs;
wire w_done;
wire r_done;
wire trans_done;
reg [1:0] w_state;
reg [1:0] r_state;
wire w_state_idle;
wire w_state_addr;
wire w_state_write;
wire w_state_resp;
wire r_state_idle;
wire r_state_addr;
wire r_state_read;
reg [7:0] len;
wire [7:0] axi_len;
wire len_reset;
wire len_incr_en;
wire [2:0] axi_size;
wire [63:0] axi_addr;
wire [3:0] axi_id;
wire rw_ready_nxt;
wire rw_ready_en;
reg [1:0] rw_resp;
wire [1:0] rw_resp_nxt;
wire resp_en;
wire [2:0] axi_addr_offset_bytes;       // 输入地址的 字节偏移量(0~7)
wire [5:0] axi_addr_offset_bits;        // 输入地址的   位偏移量(0~56)
reg  [7:0] axi_w_strb_orig;

wire YSYX210544_SIZE_B;
wire YSYX210544_SIZE_H;
wire YSYX210544_SIZE_W;
wire YSYX210544_SIZE_D;
reg  [63:0] mask_rdata;
wire [5:0] aligned_offset;                      // 移位的bit数。0~7 转换为 0~56
wire [63:0] axi_r_data_masked_unaligned;        // 已掩码，已移位后的数据



assign w_trans    = user_req_i == `YSYX210544_REQ_WRITE;
assign r_trans    = user_req_i == `YSYX210544_REQ_READ;
assign w_valid    = user_valid_i & w_trans & (!rw_ready);
assign r_valid    = user_valid_i & r_trans & (!rw_ready);

// handshake
assign aw_hs      = axi_aw_ready_i & axi_aw_valid_o;
assign w_hs       = axi_w_ready_i  & axi_w_valid_o;
assign b_hs       = axi_b_ready_o  & axi_b_valid_i;
assign ar_hs      = axi_ar_ready_i & axi_ar_valid_o;
assign r_hs       = axi_r_ready_o  & axi_r_valid_i;

assign w_done     = w_hs & axi_w_last_o;
assign r_done     = r_hs & axi_r_last_i;
assign trans_done = w_trans ? b_hs : r_done;

// ------------------State Machine------------------
assign w_state_idle = w_state == W_STATE_IDLE;
assign w_state_addr = w_state == W_STATE_ADDR;
assign w_state_write = w_state == W_STATE_WRITE;
assign w_state_resp = w_state == W_STATE_RESP;
assign r_state_idle = r_state == R_STATE_IDLE;
assign r_state_addr = r_state == R_STATE_ADDR;
assign r_state_read  = r_state == R_STATE_READ;

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
                default: ;
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
assign len_reset      = reset | (w_trans & w_state_idle) | (r_trans & r_state_idle);
assign len_incr_en    = (len != axi_len) & (w_hs | r_hs);
always @(posedge clock) begin
    if (len_reset) begin
        len <= 0;
    end
    else if (len_incr_en) begin
        len <= len + 8'd1;
    end
end

// ------------------Process Data------------------
assign axi_len          = user_blks_i;
assign axi_size         = user_size_i;
assign axi_addr         = user_addr_i;
assign axi_id           = 4'd0;// {`AXI_ID_WIDTH{1'b0}};

assign rw_ready_nxt = trans_done;
assign rw_ready_en      = trans_done | rw_ready;
always @(posedge clock) begin
    if (reset) begin
        rw_ready <= 1'b0;
    end
    else if (rw_ready_en) begin
        rw_ready <= rw_ready_nxt;
    end
end

assign user_ready_o     = rw_ready;

assign rw_resp_nxt = w_trans ? axi_b_resp_i : axi_r_resp_i;
assign resp_en = trans_done;
always @(posedge clock) begin
    if (reset) begin
        rw_resp <= 2'b0;
    end
    else if (resp_en) begin
        rw_resp <= rw_resp_nxt;
    end
end
assign user_resp_o      = rw_resp;


// ------------------Write Transaction------------------

// Read address channel signals
assign axi_aw_valid_o   = w_state_addr & user_valid_i;
assign axi_aw_addr_o    = w_valid ? axi_addr : 64'd0;
assign axi_aw_id_o      = w_valid ? axi_id : 4'd0;
assign axi_aw_len_o     = w_valid ? axi_len: 8'd0;
assign axi_aw_size_o    = w_valid ? axi_size: 3'd0;
assign axi_aw_burst_o   = 2'b01;// `AXI_BURST_TYPE_INCR;

// Write data channel signals
assign axi_w_valid_o = reset ? 1'b0 : w_state_write;

assign axi_w_last_o     = w_hs & (len == axi_len);

// 仅根据size生成的wstrb，需要移位后使用，是吗？？

always @(*) begin
    if (reset) begin
        axi_w_strb_orig = 8'd0;
    end
    else begin
    case (user_size_i)
        `YSYX210544_SIZE_B: axi_w_strb_orig = 8'b0000_0001;
        `YSYX210544_SIZE_H: axi_w_strb_orig = 8'b0000_0011;
        `YSYX210544_SIZE_W: axi_w_strb_orig = 8'b0000_1111;
        `YSYX210544_SIZE_D: axi_w_strb_orig = 8'b1111_1111;
        default: axi_w_strb_orig = 8'b0000_0000; // 不支持
    endcase 
    end
end

assign axi_addr_offset_bytes  = user_addr_i[2:0];
assign axi_addr_offset_bits   = {3'b0, axi_addr_offset_bytes} << 2'd3;

// 移位生成最终的 w_strb。wdata 和 wstrb 都需要移位
// assign axi_w_strb_o     = 8'b1111_1111;     // 每个bit代表一个字节是否要写入
assign axi_w_strb_o = w_valid ? (axi_w_strb_orig << axi_addr_offset_bytes) : 8'd0;

// Wreite response channel signals
assign axi_b_ready_o    = w_state_resp;

assign axi_w_data_o = (reset || (!w_state_write)) ? 0 : (user_wdata_i[64*len +:64] << axi_addr_offset_bits);


// ------------------Read Transaction------------------

// Read address channel signals
assign axi_ar_valid_o   = r_state_addr & user_valid_i;
assign axi_ar_addr_o    = r_trans ? axi_addr : 64'd0;
assign axi_ar_id_o      = r_trans ? axi_id : 4'd0;
assign axi_ar_len_o     = r_trans ? axi_len : 8'd0;
assign axi_ar_size_o    = r_trans ? axi_size : 3'd0;
assign axi_ar_burst_o   = 2'b01;// `AXI_BURST_TYPE_INCR;

// Read data channel signals
assign axi_r_ready_o    = r_state_read;

// User Data Size
assign YSYX210544_SIZE_B             = user_size_i == `YSYX210544_SIZE_B;
assign YSYX210544_SIZE_H             = user_size_i == `YSYX210544_SIZE_H;
assign YSYX210544_SIZE_W             = user_size_i == `YSYX210544_SIZE_W;
assign YSYX210544_SIZE_D             = user_size_i == `YSYX210544_SIZE_D;

// Read data mask
// assign mask_rdata   = (({64{YSYX210544_SIZE_B}} & {{64- 8{1'b0}},  8'hff}) 
//                      | ({64{YSYX210544_SIZE_H}} & {{64-16{1'b0}}, 16'hffff})
//                      | ({64{YSYX210544_SIZE_W}} & {{64-32{1'b0}}, 32'hffffffff})
//                      | ({64{YSYX210544_SIZE_D}} & {{64-64{1'b0}}, 64'hffffffff_ffffffff})
//                       );
always @(*) begin
    if (YSYX210544_SIZE_D)         mask_rdata = 64'hffffffff_ffffffff;
    else if (YSYX210544_SIZE_W)    mask_rdata = 64'h00000000_ffffffff;
    else if (YSYX210544_SIZE_H)    mask_rdata = 64'h00000000_0000ffff;
    else if (YSYX210544_SIZE_B)    mask_rdata = 64'h00000000_000000ff;
    else                mask_rdata = 64'd0;
end


assign aligned_offset = {3'b0, user_addr_i[2:0]} << 2'd3;

assign axi_r_data_masked_unaligned = (axi_r_data_i >> aligned_offset) & mask_rdata;

always @(posedge clock) begin
    if (reset) begin
        user_rdata_o <= 512'd0;
    end
    else if (r_hs) begin
        case (len)
            8'd0: user_rdata_o[0*64+:64] <= axi_r_data_masked_unaligned;
            8'd1: user_rdata_o[1*64+:64] <= axi_r_data_masked_unaligned;
            8'd2: user_rdata_o[2*64+:64] <= axi_r_data_masked_unaligned;
            8'd3: user_rdata_o[3*64+:64] <= axi_r_data_masked_unaligned;
            8'd4: user_rdata_o[4*64+:64] <= axi_r_data_masked_unaligned;
            8'd5: user_rdata_o[5*64+:64] <= axi_r_data_masked_unaligned;
            8'd6: user_rdata_o[6*64+:64] <= axi_r_data_masked_unaligned;
            8'd7: user_rdata_o[7*64+:64] <= axi_r_data_masked_unaligned;
            default: ;
        endcase
    end
 end


//wire _unused_ok = &{1'b0,
// axi_b_id_i,
// axi_r_id_i,
// 1'b0};

endmodule

// ZhengpuShi

// Cache AXI Unit
// Cache的AXI通信模块。
// 通过AXI更新Cache数据的，根据Cache的设计而定制的AXI访问控制
// 对外接口：访问64字节（ = 512bit），包括读、写
// 内部需要转换为AXI访问的多次读写。
// 1. AXI数据宽度最多64bit，已确认。
// 2. AXI burst len最多是8，这样一次最多传输64字节。


module ysyx_210544_cache_axi(
  input   wire                      clk,
  input   wire                      rst,
  input                             i_cache_axi_req,        // 请求读写
  input   wire  [63 : 0]            i_cache_axi_addr,       // 存储器地址（字节为单位），128字节对齐，低7位为0。
  input   wire                      i_cache_axi_op,         // 操作类型：0读取，1写入
  input   wire  [511 : 0]           i_cache_axi_wdata,      // 写入的数据
  output  reg   [511 : 0]           o_cache_axi_rdata,      // 读出的数据
  output  reg                       o_cache_axi_ack,        // 读写完成应答

  ///////////////////////////////////////////////
  // AXI interface
  output                            o_axi_io_op,            // 0:read, 1:write
  input                             i_axi_io_ready,
  input         [511 : 0]           i_axi_io_rdata,
  output reg                        o_axi_io_valid,
  output reg    [63 : 0]            o_axi_io_addr,
  output reg    [511 : 0]           o_axi_io_wdata,
  output        [2 : 0]             o_axi_io_size,
  output        [7 : 0]             o_axi_io_blks
);
    
    wire        is_flash;    // 是否为Flash外设，此时只能4字节传输，且不能使用burst模式，所以64字节需要16次传输
    wire        hs_ok;       // axi一次传输完成
    reg         cache_req_his0;   // 跟踪req信号，连续两个周期的 req 才认为是开始信号，防止一结束就又开始了新的阶段
    wire        axi_start;    // axi请求开始
    
    reg [3:0]   trans_cnt;          // 传输次数
    reg [3:0]   trans_cnt_write;    // 传输次数（写入）
    wire [8:0]  offset_bits;        // 偏移位数
    wire [8:0]  offset_bits_write;  // 偏移位数（写入）
    
    
    
    assign is_flash = i_cache_axi_addr[31:28] == 4'h3;
    assign hs_ok    = o_axi_io_valid & i_axi_io_ready;
    
    // axi每次传输的大小：64bit
    assign o_axi_io_size = is_flash ? `YSYX210544_SIZE_W : `YSYX210544_SIZE_D;
    
    // 块数：0~7表示1~8块
    assign o_axi_io_blks = is_flash ? 8'd0 : 8'd7;
    
    // 操作类型：0:read, 1:write
    assign o_axi_io_op = i_cache_axi_op;
    
    assign axi_start = i_cache_axi_req & !cache_req_his0;
    
    // 传输起始地址，64字节对齐。加入soc后，有UART的1字节对齐，Flash的4字节对齐，故这一个规则弃用
    // assign o_axi_io_addr = i_cache_axi_addr & (~64'h3F);
    
    // 控制传输次数，
    // 如果是主存，  需要 1次AXI传输得512bit；
    // 如果是Flash，需要16次AXI传输得到512bit，每次传输32bit（64bit是否支持？？）；
    assign offset_bits       = {5'd0, trans_cnt} << 3'd5;
    assign offset_bits_write = {5'd0, trans_cnt_write} << 3'd5;
    
    // 控制传输
    always @(posedge clk) begin
        if (rst) begin
            cache_req_his0    <= 1'd0;
            o_cache_axi_ack   <= 1'd0;
            o_axi_io_valid    <= 1'd0;
            o_axi_io_addr     <= 64'd0;
            o_axi_io_wdata    <= 512'd0;
            o_cache_axi_rdata <= 512'd0;
            trans_cnt         <= 4'd0;
            trans_cnt_write   <= 4'd0;
        end
        else begin
            // 追踪开始信号
            cache_req_his0 <= i_cache_axi_req;
            
            // 收到数据：保存数据、增加计数、握手反馈
            if (hs_ok) begin
                if (is_flash) begin
                    // flash传输，需要分批读取数据，分批写入数据。
                    o_cache_axi_rdata[offset_bits +:32] <= i_axi_io_rdata[0+:32]; // 保存数据
                    if (trans_cnt < 4'd15) begin
                        o_axi_io_addr   <= o_axi_io_addr + 64'd4;     // 地址递增
                        o_axi_io_wdata  <= {480'd0, i_cache_axi_wdata[offset_bits_write +:32]}; // 准备数据
                        trans_cnt       <= trans_cnt + 4'd1;             // 次数递增
                        trans_cnt_write <= trans_cnt_write + 4'd1;
                    end
                    else begin
                        o_cache_axi_ack <= 1'd1;    // 完成
                        o_axi_io_valid  <= 1'd0;    // 关闭axi请求
                        trans_cnt       <= 4'd0;    // 清零计数，准备下次继续
                        trans_cnt_write <= 4'd1;    // 初始为1，方便计算偏移量
                    end
                end
                else begin
                    o_cache_axi_rdata <= i_axi_io_rdata;    // 保存数据
                    o_cache_axi_ack   <= 1'd1;   // 完成
                    o_axi_io_valid    <= 1'd0;   // 关闭axi请求
                end
            end
            else begin
                // 触发采样
                if (axi_start) begin
                    // 第一次进入时更新地址、写入数据
                    if (!o_axi_io_valid) begin
                        if (is_flash) begin
                            o_axi_io_addr  <= i_cache_axi_addr & (~64'h3);   // 传输起始地址，4字节对齐
                        end
                        else begin
                            o_axi_io_addr  <= i_cache_axi_addr & (~64'h3F);  // 传输起始地址，64字节对齐
                        end
                        // 准备数据
                        o_axi_io_wdata <= i_cache_axi_wdata;
                    end
                    o_axi_io_valid <= 1'd1;
                end
                // 清除信号
                o_cache_axi_ack <= 1'd0;
            end
        end
    end
    
    // assign o_cache_axi_rdata = i_axi_io_rdata;
    // assign o_axi_io_wdata    = i_cache_axi_wdata;
    
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
    [*] cache data bytes = 4 * 16 * 64B = 4KB   -- 由路数、块数、块大小决定
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
        每行26bit，从高位到低位，2bit顺序，1bit脏位，1bit有效位，22bit主存标记
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

  // 常规通道
  input   wire  [`YSYX210544_BUS_64]     i_cache_basic_addr,         // 地址。保证与操作数大小相加后不能跨界。
  input   wire  [`YSYX210544_BUS_64]     i_cache_basic_wdata,        // 写入的数据
  input   wire  [2 : 0]       i_cache_basic_bytes,        // 操作的字节数: 0~7表示1~8字节
  input   wire                i_cache_basic_op,           // 操作: 0:read, 1:write
  input   wire                i_cache_basic_req,          // 请求
  output  reg   [`YSYX210544_BUS_64]     o_cache_basic_rdata,        // 读出的数据
  output  reg                 o_cache_basic_ack,          // 应答

  // 同步通道
  input   wire                i_cache_basic_sync_rreq,      // 读请求，需要一直保持，收到应答后撤销。
  output  wire                o_cache_basic_sync_rack,      // 读应答，操作完毕后应答
  output  wire                o_cache_basic_sync_rpackreq,  // 读包请求，DCache发出请求
  input   wire                i_cache_basic_sync_rpackack,  // 读包应答，DCache收到应答
  output  wire  [  1: 0]      o_cache_basic_sync_rwayid,    // 读取到的路id: 0~3
  output  wire  [  3: 0]      o_cache_basic_sync_rblkid,    // 读取到的块id: 0~15
  output  wire  [ 25: 0]      o_cache_basic_sync_rinfo,     // 读取到的cache_info
  output  wire  [511: 0]      o_cache_basic_sync_rdata,     // 读取到的cache_data
  input   wire                i_cache_basic_sync_wreq,      // 写请求，ICache收到请求
  output  wire                o_cache_basic_sync_wack,      // 写应答，ICache发出应答
  input   wire  [  1: 0]      i_cache_basic_sync_wwayid,    // 要写入的路id: 0~3
  input   wire  [  3: 0]      i_cache_basic_sync_wblkid,    // 要写入的块id: 0~15
  input   wire  [ 25: 0]      i_cache_basic_sync_winfo,     // 要写入的cache_info
  input   wire  [511: 0]      i_cache_basic_sync_wdata,     // 要写入的cache_data

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

// 根据实际硬件模型设置有效电平
parameter CHIP_DATA_CEN = 1'b0;        // cen有效的电平
parameter CHIP_DATA_WEN = 1'b0;        // wen有效的电平
parameter CHIP_DATA_WMASK_EN = 1'b0;   // 写掩码有效的电平

// =============== 状态机 ===============
//  英文名称          中文名称               含义
//  IDLE              空闲                 无活动。有用户请求则进入 READY / STORE_FROM_RAM / LOAD_FROM_BUS 这三种情况
//  READY             就绪                  命中，则直接读写。读写完毕回到IDLE。
//  STORE_FROM_RAM    存储(从RAM读取数据)    不命中并选择脏的数据块，则需要写回。先以128bit为单位分4次从RAM读入数据，读取完毕跳转到 StoreToBUS
//  STORE_TO_BUS      存储(写入总线)         不命中并选择脏的数据块，则需要写回。再将512bit数据写入总线，写入完毕跳转到 LoadFromBUS
//  LOAD_FROM_BUS     加载(从总线读取数据)    不命中并选择不脏的数据块，则需要读入新数据。先从总线读取512bit数据，读取完毕跳转到 LoadToRAM
//  LOAD_TO_RAM       加载(写入RAM)         不命中并选择不脏的数据块，则需要读入新数据。再以128bit为单位分4次写入RAM，写入完毕跳转到READY
//  FENCE_RD          同步读               有fence请求，读取vlaid的数据，送出
//  FENCE_WR          同步写               有fence请求，收到数据包，写入。
parameter [2:0] STATE_IDLE              = 3'd0;
parameter [2:0] STATE_READY             = 3'd1;
parameter [2:0] STATE_STORE_FROM_RAM    = 3'd2;
parameter [2:0] STATE_STORE_TO_BUS      = 3'd3;
parameter [2:0] STATE_LOAD_FROM_BUS     = 3'd4;
parameter [2:0] STATE_LOAD_TO_RAM       = 3'd5;
parameter [2:0] STATE_FENCE_RD          = 3'd6;
parameter [2:0] STATE_FENCE_WR          = 3'd7;

`define YSYX210544_WAYS                  4             // 路数
`define YSYX210544_BLKS                  16            // 块数
`define YSYX210544_BUS_WAYS              0:3           // 各路的总线。4路

`define YSYX210544_C_TAG_BUS             21:0          // cache的tag所在的总线 
`define YSYX210544_C_TAG_MSG_BUS         21            // cache的tag最高位所在的总线，若为1则是主存地址，即：8000_0000 ~ 4GB-1 
`define YSYX210544_C_V_BUS               22            // cache的v所在的总线 
`define YSYX210544_C_D_BUS               23            // cache的d所在的总线 
`define YSYX210544_C_S_BUS               25:24         // cache的s所在的总线


reg                           o_cache_axi_req;            // 请求
reg   [63 : 0]                o_cache_axi_addr;           // 存储器地址（字节为单位），64字节对齐，低6位为0。
reg                           o_cache_axi_op;             // 操作类型：0读取，1写入
reg   [511 : 0]               o_cache_axi_wdata;          // 要写入的数据
wire  [511 : 0]               i_cache_axi_rdata;          // 已读出的数据
wire                          i_cache_axi_ack;            // 应答

// =============== 同步 ===============
wire                          sync_rreq;                  // 同步操作读请求
reg                           sync_rack;                  // 同步操作读应答
reg                           sync_rpackreq;              // 同步操作读包请求
wire                          sync_rpackack;              // 同步操作读包应答
wire                          sync_wreq;                  // 同步操作写包请求
reg                           sync_wack;                  // 同步操作写包应答

reg   [1  : 0]                sync_rwayid;                // 读取到的路id: 0~3
reg   [3  : 0]                sync_rblkid;                // 读取到的块id: 0~15
wire  [25 : 0]                sync_rinfo;                 // 读到到的cache_info
reg   [511: 0]                sync_rdata;                 // 读到到的cache_data
wire                          sync_rlast;                 // 读取达到最后一个单元
wire                          sync_r_need;                // 是否需要读取的条件：cache行有效，且地址是主存的地址

wire  [1  : 0]                sync_wwayid;                // 要写入的路id: 0~3
wire  [3  : 0]                sync_wblkid;                // 要写入的块id: 0~15
wire  [25 : 0]                sync_winfo;                 // 要写入的cache_info
wire  [511: 0]                sync_wdata;                 // 要写入的cache_data

// =============== 物理地址解码 ===============
wire  [63: 0]                 user_blk_aligned_bytes;     // 用户地址的按块对齐地址(按字节)（64字节对齐，低6位为0）
reg   [63: 0]                 user_wmask;                 // 用户数据的写入掩码，由bytes决定，高电平有效
wire  [3 : 0]                 mem_blkno;                  // mem块号，0~15
//wire  [5 : 0]                 mem_offset_bytes;           // mem块内偏移(按字节)，0~63
wire  [8 : 0]                 mem_offset_bits;            // mem块内偏移(按位)，0~511
wire  [21: 0]                 mem_tag;                    // mem标记

// =============== Cache Info 缓存信息 ===============
reg   [25 : 0]                cache_info[`YSYX210544_BUS_WAYS][0:`YSYX210544_BLKS-1];   // cache信息块
wire  [5 : 0]                 c_data_lineno;                      // cache数据行号(0~63)
//wire  [3 : 0]                 c_offset_bytes;                     // cache行内偏移(按字节)(0~15)
wire  [6 : 0]                 c_offset_bits;                      // cache行内偏移(按位)(0~127)
wire  [127:0]                 c_wdata;                            // cache行要写入的数据
wire  [127:0]                 c_wmask;                            // cache行要写入的掩码

wire                          c_v[`YSYX210544_BUS_WAYS];                     // cache valid bit 有效位，1位有效
wire                          c_d[`YSYX210544_BUS_WAYS];                     // cache dirty bit 脏位，1为脏
wire  [1 : 0]                 c_s[`YSYX210544_BUS_WAYS];                     // cache seqence bit 顺序位，越大越需要先被替换走
wire  [21: 0]                 c_tag[`YSYX210544_BUS_WAYS];                   // cache标记

// =============== cache选中 ===============
wire                          hit[`YSYX210544_BUS_WAYS];     // 各路是否命中
wire                          hit_any;            // 是否有任意一路命中？
wire [1:0]                    wayID_smin;         // s最小的是哪一路？
wire [1:0]                    wayID_hit;          // 已命中的是哪一路（至多有一路命中） 
wire [1:0]                    wayID_select;       // 选择了哪一路？方法：若命中则就是命中的那一路；否则选择smax所在的那一路

// =============== Cache Data 缓存数据 ===============

reg                           chip_data_cen[`YSYX210544_BUS_WAYS];               // RAM 使能，低电平有效
reg                           chip_data_wen[`YSYX210544_BUS_WAYS];               // RAM 写使能，低电平有效
reg   [5  : 0]                chip_data_addr[`YSYX210544_BUS_WAYS];              // RAM 地址
reg   [127: 0]                chip_data_wdata[`YSYX210544_BUS_WAYS];             // RAM 写入数据
reg   [127: 0]                chip_data_wmask[`YSYX210544_BUS_WAYS];             // RAM 写入掩码
wire  [127: 0]                chip_data_rdata[`YSYX210544_BUS_WAYS];             // RAM 读出数据


reg [2:0] state;
reg   [1  : 0]                sync_step;                  // sync操作的不同阶段

// =============== 处理用户请求 ===============
reg   [2:0]         ram_op_cnt;                 // RAM操作计数器(0~3表示1~4次，剩余的位数用于大于4的计数)
wire  [8:0]         ram_op_offset_128;          // RAM操作的128位偏移量（延迟2个时钟周期后输出）
wire                hs_cache;                   // cache操作 握手
wire                hs_sync_rd;                 // sync读操作 握手
wire                hs_sync_rpack;              // sync读包操作 握手
wire                hs_sync_wr;                 // sync写操作 握手
wire                hs_cache_axi;               // cache_axi操作 握手
wire                hs_ramwrite;                // ram操作 握手（完成4行写入）
wire                hs_ramread;                 // ram操作 握手（完成4行读取）
wire                hs_ramline;                 // ram操作 握手（完成指定1行读写）
wire  [127: 0]      rdata_line;                 // 读取一行数据
wire  [63: 0]       rdata_out;                  // 输出的数据



assign sync_rreq                    = i_cache_basic_sync_rreq;
assign o_cache_basic_sync_rack      = sync_rack;
assign o_cache_basic_sync_rpackreq  = sync_rpackreq;
assign sync_rpackack                = i_cache_basic_sync_rpackack;
assign sync_wreq                    = i_cache_basic_sync_wreq;
assign o_cache_basic_sync_wack      = sync_wack;

assign sync_rinfo                   = cache_info[sync_rwayid][sync_rblkid];
assign o_cache_basic_sync_rwayid    = sync_rwayid;
assign o_cache_basic_sync_rblkid    = sync_rblkid;
assign o_cache_basic_sync_rinfo     = sync_rinfo;
assign o_cache_basic_sync_rdata     = sync_rdata;

assign sync_rlast                   = !sync_rreq ? 1'd0 : (sync_rwayid == 2'd3) && (sync_rblkid == 4'd15);
assign sync_r_need                  = sync_rinfo[`YSYX210544_C_V_BUS] & sync_rinfo[`YSYX210544_C_TAG_MSG_BUS];

assign sync_wwayid                  = i_cache_basic_sync_wwayid;
assign sync_wblkid                  = i_cache_basic_sync_wblkid;
assign sync_winfo                   = i_cache_basic_sync_winfo;
assign sync_wdata                   = i_cache_basic_sync_wdata;

// assign sync_rblkid                  = !sync_rreq ? 0 : {sync_rlineid >> 2}[3:0];
// assign sync_rtag                    = !sync_rreq ? 0 : c_tag[sync_rwayid];
// assign o_cache_basic_sync_retag     = {sync_rtag, sync_rlineid};
// assign sync_rdata                   = !sync_rreq ? 0 : rdata_line;

// assign sync_wetag                   = !sync_wreq ? 0 : i_cache_basic_sync_wetag;
// assign sync_wtag                    = !sync_wreq ? 0 : sync_wetag[27:6];
// assign sync_wlineid                 = !sync_wreq ? 0 : sync_wetag[5:0];
// assign sync_wblkid                  = !sync_wreq ? 0 : {sync_wlineid >> 2}[3:0];
// assign sync_wdata                   = !sync_wreq ? 0 : i_cache_basic_sync_wdata;

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

//assign mem_offset_bytes   = i_cache_basic_addr[5:0];
assign mem_offset_bits    = {3'b0, i_cache_basic_addr[5:0]} << 2'd3;
assign mem_blkno          = i_cache_basic_addr[9:6];
assign mem_tag            = i_cache_basic_addr[31:10];

assign c_data_lineno    = i_cache_basic_addr[9:4];
//assign c_offset_bytes   = mem_offset_bits[6:3]; 
assign c_offset_bits    = mem_offset_bits[6:0];
assign c_wmask          = {64'd0, user_wmask} << c_offset_bits;
assign c_wdata          = {64'd0, i_cache_basic_wdata} << c_offset_bits;

// c_tag, c_v, c_d, c_s
assign c_tag[0]   = cache_info[0][mem_blkno][`YSYX210544_C_TAG_BUS];
assign c_tag[1]   = cache_info[1][mem_blkno][`YSYX210544_C_TAG_BUS];
assign c_tag[2]   = cache_info[2][mem_blkno][`YSYX210544_C_TAG_BUS];
assign c_tag[3]   = cache_info[3][mem_blkno][`YSYX210544_C_TAG_BUS];

assign c_v[0]     = cache_info[0][mem_blkno][`YSYX210544_C_V_BUS];
assign c_v[1]     = cache_info[1][mem_blkno][`YSYX210544_C_V_BUS];
assign c_v[2]     = cache_info[2][mem_blkno][`YSYX210544_C_V_BUS];
assign c_v[3]     = cache_info[3][mem_blkno][`YSYX210544_C_V_BUS];

assign c_d[0]     = cache_info[0][mem_blkno][`YSYX210544_C_D_BUS];
assign c_d[1]     = cache_info[1][mem_blkno][`YSYX210544_C_D_BUS];
assign c_d[2]     = cache_info[2][mem_blkno][`YSYX210544_C_D_BUS];
assign c_d[3]     = cache_info[3][mem_blkno][`YSYX210544_C_D_BUS];

assign c_s[0]     = cache_info[0][mem_blkno][`YSYX210544_C_S_BUS];
assign c_s[1]     = cache_info[1][mem_blkno][`YSYX210544_C_S_BUS];
assign c_s[2]     = cache_info[2][mem_blkno][`YSYX210544_C_S_BUS];
assign c_s[3]     = cache_info[3][mem_blkno][`YSYX210544_C_S_BUS];

// hit
assign hit[0] = c_v[0] && (c_tag[0] == mem_tag);
assign hit[1] = c_v[1] && (c_tag[1] == mem_tag);
assign hit[2] = c_v[2] && (c_tag[2] == mem_tag);
assign hit[3] = c_v[3] && (c_tag[3] == mem_tag);

assign hit_any = hit[0] | hit[1] | hit[2] | hit[3];
assign wayID_hit = (hit[1] ? 2'd1 : 2'd0) | (hit[2] ? 2'd2 : 2'd0) | (hit[3] ? 2'd3 : 2'd0);
assign wayID_smin = (c_s[1] == 0 ? 2'd1 : 2'd0) | (c_s[2] == 0 ? 2'd2 : 2'd0) | (c_s[3] == 0 ? 2'd3 : 2'd0);
assign wayID_select = hit_any ? wayID_hit : wayID_smin;

// RAM instantiate
genvar way;
generate
  for (way = 0; way < `YSYX210544_WAYS; way = way + 1) 
  begin: CACHE_DATA_GEN
    S011HD1P_X32Y2D128_BW  chip_data(
      .CLK                        (clk                  ),
      .CEN                        (chip_data_cen[way]     ),
      .WEN                        (chip_data_wen[way]     ),
      .A                          (chip_data_addr[way]    ),
      .D                          (chip_data_wdata[way]   ),
      .BWEN                       (chip_data_wmask[way]   ),
      .Q                          (chip_data_rdata[way]   )
    );
  end
endgenerate

// wire state_idle             = state == STATE_IDLE;
// wire state_ready            = state == STATE_READY;
// wire state_store_from_ram   = state == STATE_STORE_FROM_RAM;
// wire state_store_to_bus     = state == STATE_STORE_TO_BUS;
// wire state_load_from_bus    = state == STATE_LOAD_FROM_BUS;
// wire state_load_to_ram      = state == STATE_LOAD_TO_RAM;

assign ram_op_offset_128 = ({6'd0, ram_op_cnt} - 9'd2) << 3'd7;
assign hs_cache = i_cache_basic_req & o_cache_basic_ack;
assign hs_sync_rd = sync_rreq & sync_rack;
assign hs_sync_rpack = sync_rpackack & sync_rpackreq;
assign hs_sync_wr = sync_wreq & sync_wack;
assign hs_cache_axi = o_cache_axi_req & i_cache_axi_ack;
assign hs_ramwrite = ram_op_cnt == 3'd4;
assign hs_ramread = ram_op_cnt == 3'd6;
assign hs_ramline = ram_op_cnt == 3'd3;
assign rdata_line = chip_data_rdata[wayID_select];
assign rdata_out = rdata_line[c_offset_bits +:64] & user_wmask;

always @(posedge clk) begin
    if (rst) begin
        state <= STATE_IDLE;
    end
    else begin
      case (state)
          STATE_IDLE:   begin
            if (sync_rreq) begin
              state <= STATE_FENCE_RD;
            end
            else if (sync_wreq) begin
              state <= STATE_FENCE_WR;
            end
            else if (i_cache_basic_req) begin
              if (hit_any) begin
                state <= STATE_READY;
              end
              else begin
                if (c_d[wayID_select]) begin
                  state <= STATE_STORE_FROM_RAM;
                end
                else begin
                  state <= STATE_LOAD_FROM_BUS;
                end
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

          STATE_FENCE_RD: begin
            if (hs_sync_rd) begin
              state <= STATE_IDLE;
            end
          end

          STATE_FENCE_WR: begin
            if (hs_sync_wr) begin
              state <= STATE_IDLE;
            end
          end

          default: ;
      endcase
    end
end

always @(posedge clk) begin
  if (rst) begin
    cache_info[0][ 0] <= {2'd0, 1'b0, 1'b0, 22'b0};
    cache_info[0][ 1] <= {2'd0, 1'b0, 1'b0, 22'b0};
    cache_info[0][ 2] <= {2'd0, 1'b0, 1'b0, 22'b0};
    cache_info[0][ 3] <= {2'd0, 1'b0, 1'b0, 22'b0};
    cache_info[0][ 4] <= {2'd0, 1'b0, 1'b0, 22'b0};
    cache_info[0][ 5] <= {2'd0, 1'b0, 1'b0, 22'b0};
    cache_info[0][ 6] <= {2'd0, 1'b0, 1'b0, 22'b0};
    cache_info[0][ 7] <= {2'd0, 1'b0, 1'b0, 22'b0};
    cache_info[0][ 8] <= {2'd0, 1'b0, 1'b0, 22'b0};
    cache_info[0][ 9] <= {2'd0, 1'b0, 1'b0, 22'b0};
    cache_info[0][10] <= {2'd0, 1'b0, 1'b0, 22'b0};
    cache_info[0][11] <= {2'd0, 1'b0, 1'b0, 22'b0};
    cache_info[0][12] <= {2'd0, 1'b0, 1'b0, 22'b0};
    cache_info[0][13] <= {2'd0, 1'b0, 1'b0, 22'b0};
    cache_info[0][14] <= {2'd0, 1'b0, 1'b0, 22'b0};
    cache_info[0][15] <= {2'd0, 1'b0, 1'b0, 22'b0};
    cache_info[1][ 0] <= {2'd1, 1'b0, 1'b0, 22'b0};
    cache_info[1][ 1] <= {2'd1, 1'b0, 1'b0, 22'b0};
    cache_info[1][ 2] <= {2'd1, 1'b0, 1'b0, 22'b0};
    cache_info[1][ 3] <= {2'd1, 1'b0, 1'b0, 22'b0};
    cache_info[1][ 4] <= {2'd1, 1'b0, 1'b0, 22'b0};
    cache_info[1][ 5] <= {2'd1, 1'b0, 1'b0, 22'b0};
    cache_info[1][ 6] <= {2'd1, 1'b0, 1'b0, 22'b0};
    cache_info[1][ 7] <= {2'd1, 1'b0, 1'b0, 22'b0};
    cache_info[1][ 8] <= {2'd1, 1'b0, 1'b0, 22'b0};
    cache_info[1][ 9] <= {2'd1, 1'b0, 1'b0, 22'b0};
    cache_info[1][10] <= {2'd1, 1'b0, 1'b0, 22'b0};
    cache_info[1][11] <= {2'd1, 1'b0, 1'b0, 22'b0};
    cache_info[1][12] <= {2'd1, 1'b0, 1'b0, 22'b0};
    cache_info[1][13] <= {2'd1, 1'b0, 1'b0, 22'b0};
    cache_info[1][14] <= {2'd1, 1'b0, 1'b0, 22'b0};
    cache_info[1][15] <= {2'd1, 1'b0, 1'b0, 22'b0};
    cache_info[2][ 0] <= {2'd2, 1'b0, 1'b0, 22'b0};
    cache_info[2][ 1] <= {2'd2, 1'b0, 1'b0, 22'b0};
    cache_info[2][ 2] <= {2'd2, 1'b0, 1'b0, 22'b0};
    cache_info[2][ 3] <= {2'd2, 1'b0, 1'b0, 22'b0};
    cache_info[2][ 4] <= {2'd2, 1'b0, 1'b0, 22'b0};
    cache_info[2][ 5] <= {2'd2, 1'b0, 1'b0, 22'b0};
    cache_info[2][ 6] <= {2'd2, 1'b0, 1'b0, 22'b0};
    cache_info[2][ 7] <= {2'd2, 1'b0, 1'b0, 22'b0};
    cache_info[2][ 8] <= {2'd2, 1'b0, 1'b0, 22'b0};
    cache_info[2][ 9] <= {2'd2, 1'b0, 1'b0, 22'b0};
    cache_info[2][10] <= {2'd2, 1'b0, 1'b0, 22'b0};
    cache_info[2][11] <= {2'd2, 1'b0, 1'b0, 22'b0};
    cache_info[2][12] <= {2'd2, 1'b0, 1'b0, 22'b0};
    cache_info[2][13] <= {2'd2, 1'b0, 1'b0, 22'b0};
    cache_info[2][14] <= {2'd2, 1'b0, 1'b0, 22'b0};
    cache_info[2][15] <= {2'd2, 1'b0, 1'b0, 22'b0};
    cache_info[3][ 0] <= {2'd3, 1'b0, 1'b0, 22'b0};
    cache_info[3][ 1] <= {2'd3, 1'b0, 1'b0, 22'b0};
    cache_info[3][ 2] <= {2'd3, 1'b0, 1'b0, 22'b0};
    cache_info[3][ 3] <= {2'd3, 1'b0, 1'b0, 22'b0};
    cache_info[3][ 4] <= {2'd3, 1'b0, 1'b0, 22'b0};
    cache_info[3][ 5] <= {2'd3, 1'b0, 1'b0, 22'b0};
    cache_info[3][ 6] <= {2'd3, 1'b0, 1'b0, 22'b0};
    cache_info[3][ 7] <= {2'd3, 1'b0, 1'b0, 22'b0};
    cache_info[3][ 8] <= {2'd3, 1'b0, 1'b0, 22'b0};
    cache_info[3][ 9] <= {2'd3, 1'b0, 1'b0, 22'b0};
    cache_info[3][10] <= {2'd3, 1'b0, 1'b0, 22'b0};
    cache_info[3][11] <= {2'd3, 1'b0, 1'b0, 22'b0};
    cache_info[3][12] <= {2'd3, 1'b0, 1'b0, 22'b0};
    cache_info[3][13] <= {2'd3, 1'b0, 1'b0, 22'b0};
    cache_info[3][14] <= {2'd3, 1'b0, 1'b0, 22'b0};
    cache_info[3][15] <= {2'd3, 1'b0, 1'b0, 22'b0};

    chip_data_cen[0] <= !CHIP_DATA_CEN;
    chip_data_cen[1] <= !CHIP_DATA_CEN;
    chip_data_cen[2] <= !CHIP_DATA_CEN;
    chip_data_cen[3] <= !CHIP_DATA_CEN;
    chip_data_wen[0] <= !CHIP_DATA_WEN;
    chip_data_wen[1] <= !CHIP_DATA_WEN;
    chip_data_wen[2] <= !CHIP_DATA_WEN;
    chip_data_wen[3] <= !CHIP_DATA_WEN;
    chip_data_addr[0] <= 6'd0;
    chip_data_addr[1] <= 6'd0;
    chip_data_addr[2] <= 6'd0;
    chip_data_addr[3] <= 6'd0;
    chip_data_wdata[0] <= 128'd0;
    chip_data_wdata[1] <= 128'd0;
    chip_data_wdata[2] <= 128'd0;
    chip_data_wdata[3] <= 128'd0;
    chip_data_wmask[0] <= 0;
    chip_data_wmask[1] <= 0;
    chip_data_wmask[2] <= 0;
    chip_data_wmask[3] <= 0;

    o_cache_basic_rdata <= 0;
    o_cache_basic_ack   <= 1'd0;

    sync_rpackreq <= 1'd0;
    sync_rack   <= 1'd0;
    sync_wack   <= 1'd0;
    sync_rwayid <= 2'd0;
    sync_rblkid <= 4'd0;
    sync_rdata  <= 512'd0;
    sync_step   <= 2'd0;

    ram_op_cnt          <= 3'd0;

    o_cache_axi_req     <= 0;
    o_cache_axi_addr    <= 64'd0;
    o_cache_axi_op      <= 0;
    o_cache_axi_wdata   <= 0;
  end
  else begin
    case (state)
      STATE_IDLE: begin;
        o_cache_basic_ack <= 1'd0;
        sync_rack <= 1'd0;
        sync_rpackreq <= 1'd0;
        sync_wack <= 1'd0;
      end

      STATE_READY: begin
        if (!hs_cache) begin
          if (i_cache_basic_op == `YSYX210544_REQ_READ) begin
            // 读取RAM一个单元
            if (!hs_ramline) begin
              chip_data_cen[wayID_select] <= CHIP_DATA_CEN;
              chip_data_addr[wayID_select] <= c_data_lineno;
              ram_op_cnt <= ram_op_cnt + 3'd1;
            end
            else begin
              chip_data_cen[wayID_select] <= !CHIP_DATA_CEN;
              o_cache_basic_rdata <= rdata_out; // ToDo: 在跳转指令时，这一步可以用组合电路实现，更早得到新的数据
              o_cache_basic_ack <= 1'd1;
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
              ram_op_cnt <= ram_op_cnt + 3'd1;
            end
            else begin
              chip_data_cen[wayID_select] <= !CHIP_DATA_CEN;
              chip_data_wen[wayID_select] <= !CHIP_DATA_WEN;
              o_cache_basic_ack <= 1'd1;
              // cache更新记录
              cache_info[wayID_select][mem_blkno][`YSYX210544_C_D_BUS]  <= 1'd1;
            end
          end
        end
        else begin
          ram_op_cnt <= 3'd0;
        end
      end

      STATE_LOAD_FROM_BUS: begin
        // 读取主存一个块
        if (!hs_cache_axi) begin
            o_cache_axi_req <= 1'd1;
            o_cache_axi_addr <= user_blk_aligned_bytes;
            o_cache_axi_op <= `YSYX210544_REQ_READ;
        end
        else begin
          o_cache_axi_req <= 1'd0;
        end
      end

      STATE_LOAD_TO_RAM: begin
        // 写入RAM一个块
        if (!hs_ramwrite) begin
          ram_op_cnt <= ram_op_cnt + 3'd1;
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
          cache_info[wayID_select][mem_blkno][`YSYX210544_C_TAG_BUS]      <= mem_tag; // c_tag
          cache_info[wayID_select][mem_blkno][`YSYX210544_C_V_BUS]        <= 1'd1;       // 有效位
          cache_info[wayID_select][mem_blkno][`YSYX210544_C_D_BUS]        <= 1'd0;       // 脏位
          // 更新cache记录四行的 s 位，循环移动
          cache_info[3][mem_blkno][`YSYX210544_C_S_BUS] <= cache_info[2][mem_blkno][`YSYX210544_C_S_BUS];
          cache_info[2][mem_blkno][`YSYX210544_C_S_BUS] <= cache_info[1][mem_blkno][`YSYX210544_C_S_BUS];
          cache_info[1][mem_blkno][`YSYX210544_C_S_BUS] <= cache_info[0][mem_blkno][`YSYX210544_C_S_BUS];
          cache_info[0][mem_blkno][`YSYX210544_C_S_BUS] <= cache_info[3][mem_blkno][`YSYX210544_C_S_BUS];
        end
      end

      STATE_STORE_FROM_RAM: begin
        // 读取RAM一个块
        if (!hs_ramread) begin
          ram_op_cnt <= ram_op_cnt + 3'd1;
          // RAM控制信号在前4个周期有效
          if (ram_op_cnt <= 3'd3) begin
            chip_data_cen[wayID_select] <= CHIP_DATA_CEN;
            chip_data_addr[wayID_select] <= {{2'd0, mem_blkno} << 2} | {4'd0, ram_op_cnt[1:0]};
          end
          // 延迟2个周期后保存RAM读出的数据
          if (ram_op_cnt >= 3'd2) begin
            o_cache_axi_wdata[ram_op_offset_128+:128] <= chip_data_rdata[wayID_select];   // 128的倍数
          end
        end
        else begin
          ram_op_cnt <= 3'd0;
          chip_data_cen[wayID_select] <= !CHIP_DATA_CEN;
          // 更新cache记录一行的 d 位。
          cache_info[wayID_select][mem_blkno][`YSYX210544_C_D_BUS]        <= 1'd0;       // 脏位
        end
      end

      STATE_STORE_TO_BUS: begin
        // 写入主存一个块
        if (!hs_cache_axi) begin
            o_cache_axi_req <= 1'd1;
            o_cache_axi_addr <= {32'd0, c_tag[wayID_select], mem_blkno, 6'd0 };
            o_cache_axi_op <= `YSYX210544_REQ_WRITE;
        end
        else begin
          o_cache_axi_wdata <= 512'd0;
          o_cache_axi_req <= 1'd0;
        end
      end

      STATE_FENCE_RD: begin
        if (!hs_sync_rd) begin
          // step0: 找到一个空位置
          if (sync_step == 2'd0) begin
            // 若是主存地址，且存在，则开始搬运数据
            if (sync_r_need) begin
              sync_step <= 2'd1;
            end
            // 若不命中则移动指针，或者完成任务
            else begin
              if (!sync_rlast) begin
                sync_rblkid <= sync_rblkid + 4'd1;
                if (sync_rblkid == 4'd15) begin
                  sync_rblkid <= 4'd0;
                  sync_rwayid <= sync_rwayid + 2'd1;
                end
              end
              else begin
                sync_step <= 2'd3;
              end
            end
          end
          // step1: 读取数据
          else if (sync_step == 2'd1) begin
            // 读取RAM一个块
            if (!hs_ramread) begin
              ram_op_cnt <= ram_op_cnt + 3'd1;
              // RAM控制信号在前4个周期有效
              if (ram_op_cnt <= 3'd3) begin
                chip_data_cen[sync_rwayid]  <= CHIP_DATA_CEN;
                chip_data_addr[sync_rwayid] <= {{2'd0, sync_rblkid} << 2} | {4'd0, ram_op_cnt[1:0]};
              end
              // 延迟2个周期后保存RAM读出的数据
              if (ram_op_cnt >= 3'd2) begin
                sync_rdata[ram_op_offset_128+:128] <= chip_data_rdata[sync_rwayid];   // 128的倍数
              end
            end
            else begin
              ram_op_cnt <= 3'd0;
              chip_data_cen[sync_rwayid] <= !CHIP_DATA_CEN;
              sync_rpackreq <= 1;
              sync_step <= 2'd2;
            end
          end
          // step2: 等待数据包应答
          else if (sync_step == 2'd2) begin
            if (hs_sync_rpack) begin
              sync_rpackreq <= 1'd0; // 撤销请求
              // 若不是最后一包，则移动指针继续工作，否则完成任务
              if (!sync_rlast) begin
                sync_rblkid <= sync_rblkid + 4'd1;
                if (sync_rblkid == 4'd15) begin
                  sync_rblkid <= 4'd0;
                  sync_rwayid <= sync_rwayid + 2'd1;
                end
                sync_step <= 2'd0;
              end
              else begin
                sync_step <= 2'd3;
              end
            end
          end
          // step3: 完成任务
          else if (sync_step == 2'd3) begin
            if (!hs_sync_rd) begin
              sync_rack <= 1'd1;
            end
            else begin
              // 清零所有信号
              sync_step <= 2'd0;
              sync_rack <= 1'd0;
              sync_rwayid <= 2'd0;
              sync_rblkid <= 4'd0;
            end
          end
        end
      end

      STATE_FENCE_WR: begin
        if (!hs_sync_wr) begin

          // 写入RAM一个块
          if (!hs_ramwrite) begin
            ram_op_cnt <= ram_op_cnt + 3'd1;
            // 写入cache数据一行
            chip_data_cen[sync_wwayid] <= CHIP_DATA_CEN;
            chip_data_wen[sync_wwayid] <= CHIP_DATA_WEN;
            chip_data_addr[sync_wwayid] <= {{2'd0, sync_wblkid} << 2} | {4'd0, ram_op_cnt[1:0]};
            chip_data_wdata[sync_wwayid] <= sync_wdata[{{7'd0,ram_op_cnt[1:0]} << 7}+:128];   // 128的倍数
            chip_data_wmask[sync_wwayid] <= {128{CHIP_DATA_WMASK_EN}};
          end
          else begin
            ram_op_cnt <= 3'd0;
            chip_data_cen[sync_wwayid] <= !CHIP_DATA_CEN;
            chip_data_wen[sync_wwayid] <= !CHIP_DATA_WEN;
            // 更新cache记录一行，并强行置位dirty位，保证在调换时能被写入主存
            // 这里cache s位是否需要考虑？如果是DCache全部搬运，则不需要考虑。如果是搬运v=1的块，则要考虑吧
            cache_info[sync_wwayid][sync_wblkid] <= sync_winfo | (26'd1 << `YSYX210544_C_D_BUS);

            sync_wack <= 1'd1;
          end
        end
      end

      default:;
    endcase
  end
end

// =============== cache_axi 从机端，请求传输数据 ===============

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

//wire _unused_ok = &{1'b0,
//  i_cache_basic_addr[63:32],
//  mem_offset_bytes,
//  mem_offset_bits[8:7],
//  c_offset_bytes,
//  1'b0};

endmodule

// ZhengpuShi

// Cache Core Unit
// 支持不对齐访问的Cache核心模块
// 封装了 cache_basic，将不对齐的访问转换为1~2次cache访问。


module ysyx_210544_cache_core (
  input   wire                clk,
  input   wire                rst,
  input   wire  [`YSYX210544_BUS_64]     i_cache_core_addr,          // 地址。地址与操作数相加后可以跨界。
  input   wire  [`YSYX210544_BUS_64]     i_cache_core_wdata,         // 写入的数据
  input   wire  [2 : 0]       i_cache_core_bytes,         // 操作的字节数: 0~7表示1~8字节
  input   wire                i_cache_core_op,            // 操作: 0:read, 1:write
  input   wire                i_cache_core_req,           // 请求
  output  reg   [`YSYX210544_BUS_64]     o_cache_core_rdata,         // 读出的数据
  output  reg                 o_cache_core_ack,           // 应答

  // 同步通道
  input   wire                i_cache_core_sync_rreq,     // 读请求
  output  wire                o_cache_core_sync_rack,     // 读应答
  input   wire                i_cache_core_sync_rpackack, // 读包请求
  output  wire                o_cache_core_sync_rpackreq, // 读包应答
  output  wire  [  1: 0]      o_cache_core_sync_rwayid,   // read way_id
  output  wire  [  3: 0]      o_cache_core_sync_rblkid,   // read blk_id
  output  wire  [ 25: 0]      o_cache_core_sync_rinfo,    // read cache_info
  output  wire  [511: 0]      o_cache_core_sync_rdata,    // read cache_data
  input   wire                i_cache_core_sync_wreq,     // 写请求
  output  wire                o_cache_core_sync_wack,     // 写应答
  input   wire  [  1: 0]      i_cache_core_sync_wwayid,   // write way_id
  input   wire  [  3: 0]      i_cache_core_sync_wblkid,   // write blk_id
  input   wire  [ 25: 0]      i_cache_core_sync_winfo,    // write cache_info
  input   wire  [511: 0]      i_cache_core_sync_wdata,    // write cache_data

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
wire  [63 : 0]                o_cache_basic_addr;         // 存储器地址（字节为单位），64字节对齐，低6位为0。
wire  [63 : 0]                o_cache_basic_wdata;        // 要写入的数据
wire  [2  : 0]                o_cache_basic_bytes;        // 字节数
wire                          o_cache_basic_op;           // 操作类型：0读取，1写入
reg                           o_cache_basic_req;          // 请求
wire  [63 : 0]                i_cache_basic_rdata;        // 已读出的数据
wire                          i_cache_basic_ack;          // 应答

// =============== 处理跨行问题 ===============
wire  [59:0]                  i_addr_high;                // 输入地址的高60位
wire  [3:0]                   i_addr_4;                   // 输入地址的低4位 (0~15)
wire  [3:0]                   i_addr_4_rev;               // 输入地址的低4位取反 (0~15)
wire  [3:0]                   i_addr_4_add;               // 输入地址的低4位add (0~15)
wire  [3:0]                   i_bytes_4;                  // 输入字节数扩展为4位

wire                          en_second;                  // 第二次操作使能
wire  [2 : 0]                 bytes[0:1];                 // 字节数
wire  [63: 0]                 addr[0:1];                  // 地址
wire  [63: 0]                 wdata[0:1];                 // 写数据
reg   [63: 0]                 rdata0;                     // 读数据

reg                           index;      // 操作的序号：0,1表示两个阶段
wire                          hs_cache;



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

  .i_cache_basic_sync_rreq    (i_cache_core_sync_rreq     ),
  .o_cache_basic_sync_rack    (o_cache_core_sync_rack     ),
  .o_cache_basic_sync_rpackreq(o_cache_core_sync_rpackreq ),
  .i_cache_basic_sync_rpackack(i_cache_core_sync_rpackack ),
  .i_cache_basic_sync_wreq    (i_cache_core_sync_wreq     ),
  .o_cache_basic_sync_wack    (o_cache_core_sync_wack     ),
  .o_cache_basic_sync_rwayid  (o_cache_core_sync_rwayid   ),
  .o_cache_basic_sync_rblkid  (o_cache_core_sync_rblkid   ),
  .o_cache_basic_sync_rinfo   (o_cache_core_sync_rinfo    ),
  .o_cache_basic_sync_rdata   (o_cache_core_sync_rdata    ),
  .i_cache_basic_sync_wwayid  (i_cache_core_sync_wwayid   ),
  .i_cache_basic_sync_wblkid  (i_cache_core_sync_wblkid   ),
  .i_cache_basic_sync_winfo   (i_cache_core_sync_winfo    ),
  .i_cache_basic_sync_wdata   (i_cache_core_sync_wdata    ),

  .i_axi_io_ready             (i_axi_io_ready             ),
  .i_axi_io_rdata             (i_axi_io_rdata             ),
  .o_axi_io_op                (o_axi_io_op                ),
  .o_axi_io_valid             (o_axi_io_valid             ),
  .o_axi_io_wdata             (o_axi_io_wdata             ),
  .o_axi_io_addr              (o_axi_io_addr              ),
  .o_axi_io_size              (o_axi_io_size              ),
  .o_axi_io_blks              (o_axi_io_blks              )
);

assign i_addr_high = i_cache_core_addr[63:4];
assign i_addr_4 = i_cache_core_addr[3:0];
assign i_bytes_4 = {1'd0, i_cache_core_bytes};
assign i_addr_4_rev = 4'd15 - i_addr_4;
assign i_addr_4_add = i_addr_4 + i_bytes_4;

assign en_second = i_addr_4 + i_bytes_4 < i_addr_4;
assign bytes[0] = en_second ? i_addr_4_rev[2:0] : i_cache_core_bytes;
assign bytes[1] = en_second ? i_addr_4_add[2:0] : 3'd0;
assign addr[0] = i_cache_core_addr;
assign addr[1] = {i_addr_high + 60'd1, 4'd0};
assign wdata[0] = i_cache_core_wdata;
assign wdata[1] = i_cache_core_wdata >> (({3'd0,bytes[0]} + 1) << 3);

assign hs_cache = i_cache_basic_ack & o_cache_basic_req;

assign o_cache_basic_addr = (index == 0) ? addr[0] : addr[1];
assign o_cache_basic_bytes = (index == 0) ? bytes[0] : bytes[1];
assign o_cache_basic_wdata = (index == 0) ? wdata[0] : wdata[1];

always @(posedge clk) begin
  if (rst) begin
    index <= 1'd0;
    o_cache_basic_req <= 1'd0;
    o_cache_core_rdata <= 0;
    o_cache_core_ack <= 0;
    rdata0 <= 0;
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
          rdata0 <= i_cache_basic_rdata;
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
        //   rdata[1] <= i_cache_basic_rdata;
          o_cache_core_rdata <= rdata0 + (i_cache_basic_rdata << ((bytes[0] + 1) << 3));
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

//wire _unused_ok = &{1'b0,
//  i_addr_4_rev[3],
//  i_addr_4_add[3],
//  1'b0};

endmodule

// ZhengpuShi

// No Cache Unit
// 没有Cache的AXI总线访问，比如UART。其实Flash也可以用。


module ysyx_210544_cache_nocache (
  input   wire                clk,
  input   wire                rst,
  input   wire  [`YSYX210544_BUS_64]     i_cache_nocache_addr,          // 地址
  input   wire  [`YSYX210544_BUS_64]     i_cache_nocache_wdata,         // 写入的数据
  input   wire  [2 : 0]       i_cache_nocache_bytes,         // 操作的字大小: 0~7表示1~8字节
  input   wire                i_cache_nocache_op,            // 操作: 0:read, 1:write
  input   wire                i_cache_nocache_req,           // 请求
  output  reg   [`YSYX210544_BUS_64]     o_cache_nocache_rdata,         // 读出的数据
  output  reg                 o_cache_nocache_ack,           // 应答

  // AXI interface
  input   wire  [511:0]       i_axi_io_rdata,
  input   wire                i_axi_io_ready,
  output  reg                 o_axi_io_valid,
  output  reg                 o_axi_io_op,
  output  reg   [511:0]       o_axi_io_wdata,
  output  reg   [63:0]        o_axi_io_addr,
  output  reg   [2:0]         o_axi_io_size,
  output  reg   [7:0]         o_axi_io_blks
);

wire hs_axi_io;
reg [2:0] nocache_size;



assign hs_axi_io = o_axi_io_valid & i_axi_io_ready;

always @(*) begin
  case (i_cache_nocache_bytes)
    3'b000: nocache_size = `YSYX210544_SIZE_B;
    3'b001: nocache_size = `YSYX210544_SIZE_H;
    3'b011: nocache_size = `YSYX210544_SIZE_W;
    3'b111: nocache_size = `YSYX210544_SIZE_D;
    default: nocache_size = `YSYX210544_SIZE_B;  // 这种情况应该是不支持的。
  endcase
end

always @(posedge clk) begin
  if (rst) begin
    o_axi_io_addr <= 0;
    o_axi_io_blks <= 0;
    o_axi_io_op <= 0;
    o_axi_io_size <= 0;
    o_axi_io_wdata <= 0;
    o_axi_io_valid <= 0;
    o_cache_nocache_rdata <= 0;
    o_cache_nocache_ack <= 0;
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

//wire _unused_ok = &{1'b0,
//  i_axi_io_rdata[511:64],
//  1'b0};

endmodule

// ZhengpuShi

// Cache Synchronous，处理DCache到ICache的一致性

// 典型应用：DCache存储了程序，将PC指针指向此地址时，默认只会从ICache取指，娶不到这些数据。
// 方法，fence.i 指令。作用：请求将DCache中的数据同步到ICache中，以便能够取到指令。
// 由于在Flash中执行程序时，会将Memory地址看做是数据，所有搬运完的数据除非装填不下，否则都会在DCache中，
// 此时需要将DCache中的数据处理掉，两种方法：
// 1. 最笨的方法，让DCache中的脏数据全部写回到Memory。
// 2. 聪明的方法，将DCache中的脏数据全部同步到ICache中，虽然可能会使ICache中的有些指令会冲掉，但影响有限。
// 采用方法2，具体做法（这里不检测是否为脏数据，先做一个全部同步的版本）
// 1. 收到fence请求，
// 2. 模拟一套8字节为大小的搬运请求
//   a. 时钟继续运行
//   b. dcache读取一包数据
//   c. icache写入一包数据
//   d. 循环b/c操作，直到完成任务。


module ysyx_210544_cache_sync(
  input                       clk,
  input                       rst,
  
  // fence.i
  input   wire                i_fencei_req,
  output  reg                 o_fencei_ack,
  
  // DCache
  output  reg                 o_sync_dcache_rreq,     // 读请求
  input   wire                i_sync_dcache_rack,     // 读应答
  input   wire                i_sync_dcache_rpackreq, // 读包请求
  output  reg                 o_sync_dcache_rpackack, // 读包应答
  input   wire  [  1: 0]      i_sync_dcache_rwayid,   // read way_id
  input   wire  [  3: 0]      i_sync_dcache_rblkid,   // read blk_id
  input   wire  [ 25: 0]      i_sync_dcache_rinfo,    // read cache_info
  input   wire  [511: 0]      i_sync_dcache_rdata,    // read cache_data

  // ICache
  output  reg                 o_sync_icache_wreq,     // 写请求
  input   wire                i_sync_icache_wack,     // 写应答
  output  reg   [  1: 0]      o_sync_icache_wwayid,   // write way_id
  output  reg   [  3: 0]      o_sync_icache_wblkid,   // write blk_id
  output  reg   [ 25: 0]      o_sync_icache_winfo,    // write cache_info
  output  reg   [511: 0]      o_sync_icache_wdata     // write cache_data
);

// =============== 状态机 ===============
//  英文名称          中文名称    含义
//  IDLE            空闲        无活动。有fencei请求进入 SYNC_READ
//  SYNC_READ       读          读DCache。读到一包数据，进入 SYNC_WRITE；读取完成，进入 IDLE
//  SYNC_WRITE      写          写ICache。写入ICache完成，进入 SYNC_RPACK_ACK
//  SYNC_RPACK_ACK  读包应答     读包应答的写入和清除。清除后，进入 SYNC_READ
parameter [1:0] STATE_IDLE              = 2'd0;
parameter [1:0] STATE_SYNC_READ         = 2'd1;
parameter [1:0] STATE_SYNC_WRITE        = 2'd2;
parameter [1:0] STATE_SYNC_RPACK_ACK    = 2'd3;

reg [1:0] state;
wire hs_rd;
wire hs_wr;



assign hs_rd          = o_sync_dcache_rreq & i_sync_dcache_rack;
// wire hs_rd_pack     = o_sync_dcache_rpackack & i_sync_dcache_rpackreq;
assign hs_wr          = o_sync_icache_wreq & i_sync_icache_wack;

always @(posedge clk) begin
  if (rst) begin
    state <= STATE_IDLE;
  end
  else begin
    case (state)
      STATE_IDLE:   begin
        if (i_fencei_req & (!o_fencei_ack)) begin
          state <= STATE_SYNC_READ;
        end
      end
      
      STATE_SYNC_READ:  begin
        if (i_sync_dcache_rpackreq) begin
          state <= STATE_SYNC_WRITE;
        end
        else if (hs_rd) begin
          state <= STATE_IDLE;
        end
      end

      STATE_SYNC_WRITE:     begin
        if (hs_wr) begin
          state <= STATE_SYNC_RPACK_ACK;
        end
      end

      STATE_SYNC_RPACK_ACK:     begin
        // 等待 rapckreq 信号撤销
        if (!i_sync_dcache_rpackreq) begin
          state <= STATE_SYNC_READ;
        end
      end

      default: ;
    endcase
  end
end

always @(posedge clk) begin
  if (rst) begin
    o_fencei_ack <= 0;
    o_sync_dcache_rreq <= 0;
    o_sync_icache_wwayid <= 0;
    o_sync_icache_wblkid <= 0;
    o_sync_icache_winfo <= 0;
    o_sync_icache_wdata <= 0;
    o_sync_icache_wreq <= 0;
    o_sync_dcache_rpackack <= 0;
  end
  else begin
    case (state)
      STATE_IDLE: begin;
        o_fencei_ack <= 0;
      end

      STATE_SYNC_READ: begin
        if (!hs_rd) begin
          o_sync_dcache_rreq <= 1;
        end
        else begin
          o_fencei_ack <= 1;
          o_sync_dcache_rreq <= 0;
        end

        if (i_sync_dcache_rpackreq) begin
          o_sync_icache_wwayid  <= i_sync_dcache_rwayid;
          o_sync_icache_wblkid  <= i_sync_dcache_rblkid;
          o_sync_icache_winfo   <= i_sync_dcache_rinfo;
          o_sync_icache_wdata   <= i_sync_dcache_rdata;
        end
      end

      STATE_SYNC_WRITE: begin
        if (!hs_wr) begin
          o_sync_icache_wreq <= 1;
        end
        else begin
          o_sync_icache_wreq <= 0;
          o_sync_dcache_rpackack <= 1;
        end
      end

      STATE_SYNC_RPACK_ACK: begin
        // rapckack只保持一个周期，自动清除
        o_sync_dcache_rpackack <= 0; 
      end

      default:;
    endcase
  end
end

endmodule

// ZhengpuShi

// Cache Interface
// 对ICache和DCache的统一


module ysyx_210544_cache(
    input                     clk,
    input                     rst,
    
    // fence.i。同步通道，在Exe_stage执行
    input   wire              i_fencei_req,
    output  wire              o_fencei_ack,
    
    // ICache。取指通道
    input   wire              i_icache_req,
    input   wire  [63:0]      i_icache_addr,
    output  wire              o_icache_ack,
    output  wire  [31:0]      o_icache_rdata,

    // DCache。访存通道
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
wire              iaddr_FLASH;
wire              iaddr_MEM;
wire              daddr_PERI;
wire              daddr_FLASH;
wire              daddr_MEM;
wire              ch_icache;
wire              ch_dcache;
wire              ch_nocache;

// Instruction Cache
wire  [63:0]      icache_rdata;
wire              icache_ack;
wire              icache_axi_io_valid;
wire              icache_axi_io_op;
wire  [511:0]     icache_axi_io_wdata;
wire  [63:0]      icache_axi_io_addr;
wire  [2:0]       icache_axi_io_size;
wire  [7:0]       icache_axi_io_blks;

// Data Cache
wire [63:0]       dcache_rdata;
wire              dcache_ack;
wire              dcache_axi_io_valid;
wire              dcache_axi_io_op;
wire  [511:0]     dcache_axi_io_wdata;
wire  [63:0]      dcache_axi_io_addr;
wire  [2:0]       dcache_axi_io_size;
wire  [7:0]       dcache_axi_io_blks;

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

// Cache_sync, ICache and DCache auto exchange data
wire              sync_dcache_rreq;
wire              sync_dcache_rack;
wire              sync_dcache_rpackreq;
wire              sync_dcache_rpackack;
wire              sync_dcache_wack;
wire  [  1: 0]    sync_dcache_rwayid;
wire  [  3: 0]    sync_dcache_rblkid;
wire  [ 25:0]     sync_dcache_rinfo;
wire  [511:0]     sync_dcache_rdata;

wire              sync_icache_rack;
wire              sync_icache_rpackreq;
wire              sync_icache_wreq;
wire              sync_icache_wack;
wire  [  1: 0]    sync_icache_rwayid;
wire  [  3: 0]    sync_icache_rblkid;
wire  [ 25:0]     sync_icache_rinfo;
wire  [511:0]     sync_icache_rdata;
wire  [  1: 0]    sync_icache_wwayid;
wire  [  3: 0]    sync_icache_wblkid;
wire  [ 25:0]     sync_icache_winfo;
wire  [511:0]     sync_icache_wdata;



// 0x1000_0000 ~ 0x2FFF_FFFF, 是UART/SPI等外设
// 0x3000_0000 ~ 0x3FFF_FFFF, 是Flash
// 0x8000_0000 ~ 0xFFFF_FFFF, 是主存
assign iaddr_FLASH  = i_icache_req && (i_icache_addr[31:28] == 4'h3);
assign iaddr_MEM    = i_icache_req && (i_icache_addr[31] == 1'b1);

assign daddr_PERI   = i_dcache_req && ((i_dcache_addr[31:28] == 4'h1) || (i_dcache_addr[31:28] == 4'h2));
assign daddr_FLASH  = i_dcache_req && (i_dcache_addr[31:28] == 4'h3);
assign daddr_MEM    = i_dcache_req && (i_dcache_addr[31] == 1'b1);

// 注意： FLASH可选的使用Cache或不使用Cache，Cache已做适配。
assign ch_icache    = iaddr_MEM | iaddr_FLASH;
assign ch_dcache    = daddr_MEM | daddr_FLASH;
assign ch_nocache   = daddr_PERI | daddr_PERI;// | iaddr_FLASH | daddr_FLASH;

ysyx_210544_cache_core ICache(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_cache_core_addr          (i_icache_addr              ),
  .i_cache_core_wdata         (64'd0                      ),
  .i_cache_core_bytes         (3'd3                       ),
  .i_cache_core_op            (`YSYX210544_REQ_READ                  ),
  .i_cache_core_req           (ch_icache ? i_icache_req : 1'b0),
  .o_cache_core_rdata         (icache_rdata               ),
  .o_cache_core_ack           (icache_ack                 ),


  .i_cache_core_sync_rreq     (1'b0                       ),
  .o_cache_core_sync_rack     (sync_icache_rack           ),
  .i_cache_core_sync_rpackack (1'b0                       ),
  .o_cache_core_sync_rpackreq (sync_icache_rpackreq       ),
  .i_cache_core_sync_wreq     (sync_icache_wreq           ),
  .o_cache_core_sync_wack     (sync_icache_wack           ),
  .o_cache_core_sync_rwayid   (sync_icache_rwayid         ),
  .o_cache_core_sync_rblkid   (sync_icache_rblkid         ),
  .o_cache_core_sync_rinfo    (sync_icache_rinfo          ),
  .o_cache_core_sync_rdata    (sync_icache_rdata          ),
  .i_cache_core_sync_wwayid   (sync_icache_wwayid         ),
  .i_cache_core_sync_wblkid   (sync_icache_wblkid         ),
  .i_cache_core_sync_winfo    (sync_icache_winfo          ),
  .i_cache_core_sync_wdata    (sync_icache_wdata          ),

  .i_axi_io_ready             (ch_icache ? i_axi_io_ready : 1'b0 ),
  .i_axi_io_rdata             (ch_icache ? i_axi_io_rdata : 512'd0 ),
  .o_axi_io_op                (icache_axi_io_op           ),
  .o_axi_io_valid             (icache_axi_io_valid        ),
  .o_axi_io_wdata             (icache_axi_io_wdata        ),
  .o_axi_io_addr              (icache_axi_io_addr         ),
  .o_axi_io_size              (icache_axi_io_size         ),
  .o_axi_io_blks              (icache_axi_io_blks         )
);

ysyx_210544_cache_core DCache(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_cache_core_addr          (i_dcache_addr              ),
  .i_cache_core_wdata         (i_dcache_wdata             ),
  .i_cache_core_bytes         (i_dcache_bytes             ),
  .i_cache_core_op            (i_dcache_op                ),
  .i_cache_core_req           (ch_dcache ? i_dcache_req : 1'b0),
  .o_cache_core_rdata         (dcache_rdata               ),
  .o_cache_core_ack           (dcache_ack                 ),

  .i_cache_core_sync_rreq     (sync_dcache_rreq           ),
  .o_cache_core_sync_rack     (sync_dcache_rack           ),
  .i_cache_core_sync_rpackack (sync_dcache_rpackack       ),
  .o_cache_core_sync_rpackreq (sync_dcache_rpackreq       ),
  .i_cache_core_sync_wreq     (1'b0                       ),
  .o_cache_core_sync_wack     (sync_dcache_wack           ),
  .o_cache_core_sync_rwayid   (sync_dcache_rwayid         ),
  .o_cache_core_sync_rblkid   (sync_dcache_rblkid         ),
  .o_cache_core_sync_rinfo    (sync_dcache_rinfo          ),
  .o_cache_core_sync_rdata    (sync_dcache_rdata          ),
  .i_cache_core_sync_wwayid   (2'd0                       ),
  .i_cache_core_sync_wblkid   (4'd0                       ),
  .i_cache_core_sync_winfo    (26'd0                      ),
  .i_cache_core_sync_wdata    (512'd0                     ),

  .i_axi_io_ready             (ch_dcache ? i_axi_io_ready : 1'b0),
  .i_axi_io_rdata             (ch_dcache ? i_axi_io_rdata : 512'd0),
  .o_axi_io_op                (dcache_axi_io_op           ),
  .o_axi_io_valid             (dcache_axi_io_valid        ),
  .o_axi_io_wdata             (dcache_axi_io_wdata        ),
  .o_axi_io_addr              (dcache_axi_io_addr         ),
  .o_axi_io_size              (dcache_axi_io_size         ),
  .o_axi_io_blks              (dcache_axi_io_blks         )
);

ysyx_210544_cache_nocache NoCache(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_cache_nocache_addr       (nocache_addr               ),
  .i_cache_nocache_wdata      (nocache_wdata              ),
  .i_cache_nocache_bytes      (nocache_bytes              ),
  .i_cache_nocache_op         (nocache_op                 ),
  .i_cache_nocache_req        (ch_nocache ? nocache_req : 1'b0),
  .o_cache_nocache_rdata      (nocache_rdata              ),
  .o_cache_nocache_ack        (nocache_ack                ),

  .i_axi_io_ready             (ch_nocache ? i_axi_io_ready : 1'b0        ),
  .i_axi_io_rdata             (ch_nocache ? i_axi_io_rdata : 512'd0      ),
  .o_axi_io_op                (nocache_axi_io_op          ),
  .o_axi_io_valid             (nocache_axi_io_valid       ),
  .o_axi_io_wdata             (nocache_axi_io_wdata       ),
  .o_axi_io_addr              (nocache_axi_io_addr        ),
  .o_axi_io_size              (nocache_axi_io_size        ),
  .o_axi_io_blks              (nocache_axi_io_blks        )
);

ysyx_210544_cache_sync Cache_sync(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .i_fencei_req               (i_fencei_req               ),
  .o_fencei_ack               (o_fencei_ack               ),
  .o_sync_dcache_rreq         (sync_dcache_rreq           ),
  .i_sync_dcache_rack         (sync_dcache_rack           ),
  .o_sync_dcache_rpackack     (sync_dcache_rpackack       ),
  .i_sync_dcache_rpackreq     (sync_dcache_rpackreq       ),
  .i_sync_dcache_rwayid       (sync_dcache_rwayid         ),
  .i_sync_dcache_rblkid       (sync_dcache_rblkid         ),
  .i_sync_dcache_rinfo        (sync_dcache_rinfo          ),
  .i_sync_dcache_rdata        (sync_dcache_rdata          ),
  .o_sync_icache_wreq         (sync_icache_wreq           ),
  .i_sync_icache_wack         (sync_icache_wack           ),
  .o_sync_icache_wwayid       (sync_icache_wwayid         ),
  .o_sync_icache_wblkid       (sync_icache_wblkid         ),
  .o_sync_icache_winfo        (sync_icache_winfo          ),
  .o_sync_icache_wdata        (sync_icache_wdata          )
);


/////////////////////////////////////////////////
// 信号互联

assign nocache_req      = ch_nocache ? (i_icache_req | i_dcache_req                     ) : 1'b0;
assign nocache_addr     = ch_nocache ? (i_icache_req ? i_icache_addr  : i_dcache_addr   ) : 64'd0;
assign nocache_wdata    = ch_nocache ? (i_icache_req ? 64'd0          : i_dcache_wdata  ) : 64'd0;
assign nocache_bytes    = ch_nocache ? (i_icache_req ? 3'd3           : i_dcache_bytes  ) : 3'd0;
assign nocache_op       = ch_nocache ? (i_icache_req ? `YSYX210544_REQ_READ      : i_dcache_op     ) : `YSYX210544_REQ_READ;

assign o_axi_io_valid   =                   ch_icache ? icache_axi_io_valid   : (ch_dcache ? dcache_axi_io_valid  : nocache_axi_io_valid);
assign o_axi_io_op      = o_axi_io_valid ? (ch_icache ? icache_axi_io_op      : (ch_dcache ? dcache_axi_io_op     : nocache_axi_io_op   )) : 0;
assign o_axi_io_wdata   = o_axi_io_valid ? (ch_icache ? icache_axi_io_wdata   : (ch_dcache ? dcache_axi_io_wdata  : nocache_axi_io_wdata)) : 0;
assign o_axi_io_addr    = o_axi_io_valid ? (ch_icache ? icache_axi_io_addr    : (ch_dcache ? dcache_axi_io_addr   : nocache_axi_io_addr )) : 0;
assign o_axi_io_size    = o_axi_io_valid ? (ch_icache ? icache_axi_io_size    : (ch_dcache ? dcache_axi_io_size   : nocache_axi_io_size )) : 0;
assign o_axi_io_blks    = o_axi_io_valid ? (ch_icache ? icache_axi_io_blks    : (ch_dcache ? dcache_axi_io_blks   : nocache_axi_io_blks )) : 0;

assign o_icache_rdata   = ch_icache ? icache_rdata[31:0] : nocache_rdata[31:0];
assign o_icache_ack     = ch_icache ? icache_ack         : nocache_ack        ;

assign o_dcache_rdata   = ch_dcache ? dcache_rdata       : nocache_rdata      ;
assign o_dcache_ack     = ch_dcache ? dcache_ack         : nocache_ack        ;


//wire _unused_ok = &{1'b0,
//  icache_rdata[63:32],
//  sync_dcache_wack,
//  sync_icache_rack,
//  sync_icache_rwayid,
//  sync_icache_rblkid,
//  sync_icache_rinfo,
//  sync_icache_rdata,
//  sync_icache_rpackreq,
//  1'b0};

endmodule

// ZhengpuShi

// Simple RTC module


module ysyx_210544_rtc(
  input   wire              clk,
  input   wire              rst,

  input   wire              ren,
  output  [`YSYX210544_BUS_64]         rdata
);

reg   [`YSYX210544_BUS_64] clk_cnt     ;   // 内部计时器，用于控制秒的变化
reg   [15: 0]   year        ;   // year: 0000 ~ 9999    2^16-1=65535
reg   [3 : 0]   month       ;   // 2^4-1=15
reg   [4 : 0]   day         ;   // 2^5-1=31
reg   [5 : 0]   hour        ;   // 2^6-1=63
reg   [5 : 0]   minute      ;   // 2^6-1=63
reg   [5 : 0]   second      ;   // 2^6-1=63

wire  [`YSYX210544_BUS_64] rtc_val;


assign rtc_val = {21'b0, year, month, day, hour, minute, second};

// rtc simulate
always @(posedge clk) begin
  if (rst) begin
    clk_cnt  <= 0;
    year    <= 16'd2021;
    month   <= 4'd1;
    day     <= 5'd2;
    hour    <= 6'd3;
    minute  <= 6'd4;
    second  <= 6'd5;
  end
  else begin
    clk_cnt <= clk_cnt + 1;
    if (clk_cnt == `YSYX210544_CLOCKS_PER_SECOND) begin
      clk_cnt <= 0;
      second <= second + 6'd1;
      if (second == 60) begin
        second <= 6'd0;

        minute <= minute + 6'd1;
        if (minute == 60) begin
          minute <= 6'd0;

          hour <= hour + 6'd1;
          if (hour == 24) begin
            hour <= 6'd0;

            day <= day + 5'd1;
            if (day == 30) begin
              day <= 5'd0;

              month <= month + 4'd1;
              if (month == 12) begin
                month <= 4'd0;

                year <= year + 16'd1;
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

  input   wire [`YSYX210544_BUS_64]      i_clint_addr,
  input   wire                i_clint_ren,
  output  wire [`YSYX210544_BUS_64]      o_clint_rdata,
  input   wire                i_clint_wen,
  input   wire [`YSYX210544_BUS_64]      i_clint_wdata,
  output  wire                o_clint_mtime_overflow
);

// reg   [7:0]       reg_mtime_cnt;
reg   [`YSYX210544_BUS_64]   reg_mtime;
reg   [`YSYX210544_BUS_64]   reg_mtimecmp;
wire addr_mtime;
wire addr_mtimecmp;



assign addr_mtime = i_clint_addr == `YSYX210544_DEV_MTIME;
assign addr_mtimecmp = i_clint_addr == `YSYX210544_DEV_MTIMECMP;

always @(posedge clk) begin
  if (rst) begin
    reg_mtime <= 0;
    reg_mtimecmp <= 5000;
  end
  else begin
    // if (reg_mtime_cnt < 1) begin
    //   reg_mtime_cnt <= reg_mtime_cnt + 1;
    // end
    // else begin
    //   reg_mtime_cnt <= 0;
    //   reg_mtime <= reg_mtime + 500;
    // end
    reg_mtime <= reg_mtime + 1;
    
    if (i_clint_wen & addr_mtimecmp) begin
      // $display("reg_mtimecmp, old: ", reg_mtimecmp, ", new: ", i_clint_wdata, ". reg_mtime: ", reg_mtime);
      // $write("^");
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

  input   wire  [`YSYX210544_BUS_RIDX]     i_rs1,
  input   wire                  i_rs1_ren,
  input   wire  [`YSYX210544_BUS_RIDX]     i_rs2,
  input   wire                  i_rs2_ren,
  input   wire  [`YSYX210544_BUS_RIDX]     i_rd,
  input   wire                  i_rd_wen,
  input   wire  [`YSYX210544_BUS_64]       i_rd_data,
  output  reg   [`YSYX210544_BUS_64]       o_rs1_data,
  output  reg   [`YSYX210544_BUS_64]       o_rs2_data

`ifdef YSYX210544_DIFFTEST_FLAG
    ,
  output  wire  [`YSYX210544_BUS_64]       o_regs[0:31]
`endif
);

reg [`YSYX210544_BUS_64] regs[0:31];

`ifdef YSYX210544_DIFFTEST_FLAG

// difftest regs接口
genvar i;
generate
    for (i = 0; i < 32; i = i + 1) 
    begin: O_REGS_GEN
        assign o_regs[i] = ((i_rd_wen) && (i_rd == i) && (i != 0)) ? i_rd_data : regs[i];
    end
endgenerate

// register alias name
wire  [`YSYX210544_BUS_64]   x00_zero;
wire  [`YSYX210544_BUS_64]   x01_ra;
wire  [`YSYX210544_BUS_64]   x02_sp;
wire  [`YSYX210544_BUS_64]   x03_gp;
wire  [`YSYX210544_BUS_64]   x04_tp;
wire  [`YSYX210544_BUS_64]   x05_t0;
wire  [`YSYX210544_BUS_64]   x06_t1;
wire  [`YSYX210544_BUS_64]   x07_t2;
wire  [`YSYX210544_BUS_64]   x08_s0;
wire  [`YSYX210544_BUS_64]   x09_s1;
wire  [`YSYX210544_BUS_64]   x10_a0;
wire  [`YSYX210544_BUS_64]   x11_a1;
wire  [`YSYX210544_BUS_64]   x12_a2;
wire  [`YSYX210544_BUS_64]   x13_a3;
wire  [`YSYX210544_BUS_64]   x14_a4;
wire  [`YSYX210544_BUS_64]   x15_a5;
wire  [`YSYX210544_BUS_64]   x16_a6;
wire  [`YSYX210544_BUS_64]   x17_a7;
wire  [`YSYX210544_BUS_64]   x18_s2;
wire  [`YSYX210544_BUS_64]   x19_s3;
wire  [`YSYX210544_BUS_64]   x20_s4;
wire  [`YSYX210544_BUS_64]   x21_s5;
wire  [`YSYX210544_BUS_64]   x22_s6;
wire  [`YSYX210544_BUS_64]   x23_s7;
wire  [`YSYX210544_BUS_64]   x24_s8;
wire  [`YSYX210544_BUS_64]   x25_s9;
wire  [`YSYX210544_BUS_64]   x26_s10;
wire  [`YSYX210544_BUS_64]   x27_s11;
wire  [`YSYX210544_BUS_64]   x28_t3;
wire  [`YSYX210544_BUS_64]   x29_t4;
wire  [`YSYX210544_BUS_64]   x30_t5;
wire  [`YSYX210544_BUS_64]   x31_t6;

assign x00_zero = regs[00];
assign x01_ra   = regs[01];
assign x02_sp   = regs[02];
assign x03_gp   = regs[03];
assign x04_tp   = regs[04];
assign x05_t0   = regs[05];
assign x06_t1   = regs[06];
assign x07_t2   = regs[07];
assign x08_s0   = regs[08];
assign x09_s1   = regs[09];
assign x10_a0   = regs[10];
assign x11_a1   = regs[11];
assign x12_a2   = regs[12];
assign x13_a3   = regs[13];
assign x14_a4   = regs[14];
assign x15_a5   = regs[15];
assign x16_a6   = regs[16];
assign x17_a7   = regs[17];
assign x18_s2   = regs[18];
assign x19_s3   = regs[19];
assign x20_s4   = regs[20];
assign x21_s5   = regs[21];
assign x22_s6   = regs[22];
assign x23_s7   = regs[23];
assign x24_s8   = regs[24];
assign x25_s9   = regs[25];
assign x26_s10  = regs[26];
assign x27_s11  = regs[27];
assign x28_t3   = regs[28];
assign x29_t4   = regs[29];
assign x30_t5   = regs[30];
assign x31_t6   = regs[31];

`endif

// i_rd 写入
always @(posedge clk) begin
  if (rst) begin
    regs[ 0] <= `YSYX210544_ZERO_WORD;
    regs[ 1] <= `YSYX210544_ZERO_WORD;
    regs[ 2] <= `YSYX210544_ZERO_WORD;
    regs[ 3] <= `YSYX210544_ZERO_WORD;
    regs[ 4] <= `YSYX210544_ZERO_WORD;
    regs[ 5] <= `YSYX210544_ZERO_WORD;
    regs[ 6] <= `YSYX210544_ZERO_WORD;
    regs[ 7] <= `YSYX210544_ZERO_WORD;
    regs[ 8] <= `YSYX210544_ZERO_WORD;
    regs[ 9] <= `YSYX210544_ZERO_WORD;
    regs[10] <= `YSYX210544_ZERO_WORD;
    regs[11] <= `YSYX210544_ZERO_WORD;
    regs[12] <= `YSYX210544_ZERO_WORD;
    regs[13] <= `YSYX210544_ZERO_WORD;
    regs[14] <= `YSYX210544_ZERO_WORD;
    regs[15] <= `YSYX210544_ZERO_WORD;
    regs[16] <= `YSYX210544_ZERO_WORD;
    regs[17] <= `YSYX210544_ZERO_WORD;
    regs[18] <= `YSYX210544_ZERO_WORD;
    regs[19] <= `YSYX210544_ZERO_WORD;
    regs[20] <= `YSYX210544_ZERO_WORD;
    regs[21] <= `YSYX210544_ZERO_WORD;
    regs[22] <= `YSYX210544_ZERO_WORD;
    regs[23] <= `YSYX210544_ZERO_WORD;
    regs[24] <= `YSYX210544_ZERO_WORD;
    regs[25] <= `YSYX210544_ZERO_WORD;
    regs[26] <= `YSYX210544_ZERO_WORD;
    regs[27] <= `YSYX210544_ZERO_WORD;
    regs[28] <= `YSYX210544_ZERO_WORD;
    regs[29] <= `YSYX210544_ZERO_WORD;
    regs[30] <= `YSYX210544_ZERO_WORD;
    regs[31] <= `YSYX210544_ZERO_WORD;
  end
  else begin
    // if ((w_ena) && (w_addr != 5'h00))    
    //     regs[w_addr] <= w_data;
      
    if (i_rd_wen && (i_rd != 5'h00))
      regs[i_rd] <= i_rd_data;
  end
end

// i_rs1 读取
always @(*) begin
  if (rst)
    o_rs1_data = `YSYX210544_ZERO_WORD;
  else if (i_rs1_ren)
    o_rs1_data = regs[i_rs1];
  else
    o_rs1_data = `YSYX210544_ZERO_WORD;
end

// i_rs2 读取
always @(*) begin
  if (rst)
    o_rs2_data = `YSYX210544_ZERO_WORD;
  else if (i_rs2_ren)
    o_rs2_data = regs[i_rs2];
  else
    o_rs2_data = `YSYX210544_ZERO_WORD;
end

//wire _unused_ok = &{1'b0,
//  x00_zero,
//  x01_ra,
//  x02_sp,
//  x03_gp,
//  x04_tp,
//  x05_t0,
//  x06_t1,
//  x07_t2,
//  x08_s0,
//  x09_s1,
//  x10_a0,
//  x11_a1,
//  x12_a2,
//  x13_a3,
//  x14_a4,
//  x15_a5,
//  x16_a6,
//  x17_a7,
//  x18_s2,
//  x19_s3,
//  x20_s4,
//  x21_s5,
//  x22_s6,
//  x23_s7,
//  x24_s8,
//  x25_s9,
//  x26_s10,
//  x27_s11,
//  x28_t3,
//  x29_t4,
//  x30_t5,
//  x31_t6,
//  1'b0};

endmodule

// ZhengpuShi


module ysyx_210544_csrfile(
  input   wire              clk,
  input   wire              rst,

  // 读写CSR
  input                     i_csr_ren,
  input   wire  [11 : 0]    i_csr_addr,
  input                     i_csr_wen,
  input   wire  [`YSYX210544_BUS_64]   i_csr_wdata,
  output  reg   [`YSYX210544_BUS_64]   o_csr_rdata,

  // 中断信号，直接控制csr
  output                    o_csr_clint_mstatus_mie,
  output                    o_csr_clint_mie_mtie,

  output  reg   [`YSYX210544_BUS_64]   o_csrs_mcycle,
  output  reg   [`YSYX210544_BUS_64]   o_csrs_mstatus,
  output  reg   [`YSYX210544_BUS_64]   o_csrs_mie,
  output  reg   [`YSYX210544_BUS_64]   o_csrs_mtvec,
  output  reg   [`YSYX210544_BUS_64]   o_csrs_mscratch,
  output  reg   [`YSYX210544_BUS_64]   o_csrs_mepc,
  output  reg   [`YSYX210544_BUS_64]   o_csrs_mcause,
  output  reg   [`YSYX210544_BUS_64]   o_csrs_mip
);

wire              mstatus_sd;


// CSR
assign o_csr_clint_mstatus_mie = o_csrs_mstatus[3];
assign o_csr_clint_mie_mtie = o_csrs_mie[7];

// csr读取
always @(*) begin
  if (rst) begin
    o_csr_rdata   = 0;
  end
  else if (i_csr_ren) begin
    case (i_csr_addr)
        `YSYX210544_CSR_ADR_MCYCLE:    o_csr_rdata = o_csrs_mcycle;
        `YSYX210544_CSR_ADR_MSTATUS:   o_csr_rdata = o_csrs_mstatus;
        `YSYX210544_CSR_ADR_MIE:       o_csr_rdata = o_csrs_mie;
        `YSYX210544_CSR_ADR_MTVEC:     o_csr_rdata = o_csrs_mtvec;
        `YSYX210544_CSR_ADR_MSCRATCH:  o_csr_rdata = o_csrs_mscratch;
        `YSYX210544_CSR_ADR_MEPC:      o_csr_rdata = o_csrs_mepc;
        `YSYX210544_CSR_ADR_MCAUSE:    o_csr_rdata = o_csrs_mcause;
        `YSYX210544_CSR_ADR_MIP:       o_csr_rdata = o_csrs_mip;
        default:            o_csr_rdata = 0;
    endcase
  end
  else begin
    o_csr_rdata = 0;
  end
end

assign mstatus_sd = (i_csr_wdata[14:13] == 2'b11) | (i_csr_wdata[16:15] == 2'b11);

// csr写入
always @(posedge clk) begin
    if (rst) begin
        o_csrs_mcycle    <= 0;
        o_csrs_mstatus   <= 64'h1800;// 64'h1808;
        o_csrs_mie       <= 0;// 64'h80;
        o_csrs_mtvec     <= 0;
        o_csrs_mscratch  <= 0;
        o_csrs_mepc      <= 0;
        o_csrs_mcause    <= 0;// 64'h80000000_00000007;
        o_csrs_mip       <= 0;// 64'h80;
    end
    else begin
        o_csrs_mcycle <= o_csrs_mcycle + 1;
        if (i_csr_wen) begin
            case (i_csr_addr)
                // `YSYX210544_CSR_ADR_MCYCLE:    o_csrs_mcycle <= i_csr_wdata;
                `YSYX210544_CSR_ADR_MSTATUS:   o_csrs_mstatus <= {mstatus_sd, i_csr_wdata[62:0]};
                `YSYX210544_CSR_ADR_MIE:       o_csrs_mie <= i_csr_wdata;
                `YSYX210544_CSR_ADR_MTVEC:     o_csrs_mtvec <= i_csr_wdata;
                `YSYX210544_CSR_ADR_MSCRATCH:  o_csrs_mscratch <= i_csr_wdata;
                `YSYX210544_CSR_ADR_MEPC:      o_csrs_mepc <= i_csr_wdata;
                `YSYX210544_CSR_ADR_MCAUSE:    o_csrs_mcause <= i_csr_wdata;
                `YSYX210544_CSR_ADR_MIP:       o_csrs_mip <= i_csr_wdata;
                default: ;
            endcase
        end
    end
end

endmodule

// ZhengpuShi

// Fetch Interface


module ysyx_210544_if_stage(
  input   wire                clk,
  input   wire                rst,
  input                       i_if_writebacked_req,
  output  wire                o_if_fetched_req,

  ///////////////////////////////////////////////
  // AXI interface for Fetch
  input                       i_if_bus_ack,
  input         [`YSYX210544_BUS_32]     i_if_bus_rdata,
  output                      o_if_bus_req,
  output        [`YSYX210544_BUS_64]     o_if_bus_addr,
  
  ///////////////////////////////////////////////
  input   wire                i_if_pc_jmp,
  input   wire  [`YSYX210544_BUS_64]     i_if_pc_jmpaddr,
  output  wire  [`YSYX210544_BUS_64]     o_if_pc,
  output  wire  [`YSYX210544_BUS_32]     o_if_inst
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
  .o_fetched                  (o_if_fetched_req           )
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
  input         [`YSYX210544_BUS_32]     i_bus_rdata,
  output reg                  o_bus_req,
  output reg    [`YSYX210544_BUS_64]     o_bus_addr,
  
  /////////////////////////////////////////////////////////
  input                       i_writebacked_req,    // 是否写回阶段完成
  input   wire                i_pc_jmp,
  input   wire  [`YSYX210544_BUS_64]     i_pc_jmpaddr,
  output  reg   [`YSYX210544_BUS_64]     o_pc,
  output  reg   [`YSYX210544_BUS_32]     o_inst,
  output  reg                 o_fetched             // 取到指令的通知
);

wire              handshake_done;
reg [`YSYX210544_BUS_64]     saved_pc_jmpaddr;     // 记忆的pc跳转指令
reg               fetch_again;          // 再次取指
reg [`YSYX210544_BUS_64]     pc_pred;              // 预测的下一个PC



// o_bus_req
always @(posedge clk) begin
  if (rst) begin
    o_bus_req <= 1;
  end
  else begin
    // 停止信号
    if (handshake_done) begin
		// if fetch_again, won't stop
      if (!fetch_again) begin
        o_bus_req <= 0;
      end
    end
    // 启动信号
    else if (i_writebacked_req) begin
      o_bus_req <= 1;
    end
  end
end

assign handshake_done = o_bus_req & i_bus_ack;


// fetch an instruction
always @( posedge clk ) begin
  if (rst) begin
    fetch_again             <= 0;
    saved_pc_jmpaddr        <= 0;
    o_bus_addr              <= `YSYX210544_PC_START;
    o_pc                    <= 0;
    o_inst                  <= 0;
    o_fetched               <= 0;
    pc_pred                 <= 0;
  end
  else begin
    // if jmp, fetch again once
    if (i_pc_jmp & (i_pc_jmpaddr != pc_pred)) begin
      fetch_again 			<= 1;
      saved_pc_jmpaddr 		<= i_pc_jmpaddr;
    end
    // 收到总线数据，处理数据
    else if (handshake_done) begin
      if (fetch_again) begin
        fetch_again             <= 0;
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
    // 空闲时，输出空数据
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
  input   wire                i_id_fetched_req,
  input   wire                i_id_decoded_ack,
  output  reg                 o_id_decoded_req,
  input   wire  [`YSYX210544_BUS_64]     i_id_pc,
  input   wire  [`YSYX210544_BUS_32]     i_id_inst,
  input   wire  [`YSYX210544_BUS_64]     i_id_rs1_data,
  input   wire  [`YSYX210544_BUS_64]     i_id_rs2_data,
  output  wire  [`YSYX210544_BUS_64]     o_id_pc,
  output  wire  [`YSYX210544_BUS_32]     o_id_inst,
  output  wire                o_id_rs1_ren,
  output  wire  [`YSYX210544_BUS_RIDX]   o_id_rs1,
  output  wire                o_id_rs2_ren,
  output  wire  [`YSYX210544_BUS_RIDX]   o_id_rs2,
  output  wire  [`YSYX210544_BUS_RIDX]   o_id_rd,
  output  wire                o_id_rd_wen,
  output  wire  [7 : 0]       o_id_inst_opcode,
  output  wire  [`YSYX210544_BUS_64]     o_id_op1,
  output  wire  [`YSYX210544_BUS_64]     o_id_op2,
  output  wire  [`YSYX210544_BUS_64]     o_id_op3,
  output  wire                o_id_skipcmt
);

reg                           i_ena;    // 是否使能组合逻辑单元部件
wire                          i_disable;
// 保存输入信息
reg   [`YSYX210544_BUS_64]               tmp_i_id_pc;
reg   [`YSYX210544_BUS_32]               tmp_i_id_inst;

wire fetched_hs;
wire decoded_hs;



assign fetched_hs = i_id_fetched_req;
assign decoded_hs = i_id_decoded_ack & o_id_decoded_req;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_id_pc,
      tmp_i_id_inst
    } <= 0;

    o_id_decoded_req      <= 0;
    i_ena                 <= 0;
  end
  else begin
    if (fetched_hs) begin
      tmp_i_id_pc         <= i_id_pc;
      tmp_i_id_inst       <= i_id_inst;

      o_id_decoded_req    <= 1;
      i_ena               <= 1;
    end
    else if (decoded_hs) begin
      o_id_decoded_req    <= 0;
      i_ena               <= 0;
    end
  end
end

assign i_disable = !i_ena;

assign o_id_pc      = i_disable ? 0 : tmp_i_id_pc;
assign o_id_inst    = i_disable ? 0 : tmp_i_id_inst;

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
  input   wire  [`YSYX210544_BUS_32]     i_inst,
  input   wire  [`YSYX210544_BUS_64]     i_rs1_data,
  input   wire  [`YSYX210544_BUS_64]     i_rs2_data,
  input   wire  [`YSYX210544_BUS_64]     i_pc,
  output  wire                o_rs1_ren,
  output  wire  [`YSYX210544_BUS_RIDX]   o_rs1,
  output  wire                o_rs2_ren,
  output  wire  [`YSYX210544_BUS_RIDX]   o_rs2,
  output  wire  [`YSYX210544_BUS_RIDX]   o_rd,
  output  wire                o_rd_wen,
  output  wire  [7 : 0]       o_inst_opcode,
  output  reg   [`YSYX210544_BUS_64]     o_op1,
  output  reg   [`YSYX210544_BUS_64]     o_op2,
  output  reg   [`YSYX210544_BUS_64]     o_op3,
  output  wire                o_skipcmt
);

wire [7  : 0] inst_opcode;

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
wire inst_lui;     
wire inst_auipc;   
wire inst_jal;     
wire inst_jalr;    
wire inst_beq;     
wire inst_bne;     
wire inst_blt;     
wire inst_bge;     
wire inst_bltu;    
wire inst_bgeu;    
wire inst_lb;      
wire inst_lh;      
wire inst_lw;      
wire inst_lbu;     
wire inst_lhu;     
wire inst_sb;      
wire inst_sh;      
wire inst_sw;      
wire inst_addi;    
wire inst_slti;    
wire inst_sltiu;   
wire inst_xori;    
wire inst_ori;     
wire inst_andi;    
wire inst_slli;    
wire inst_srli;    
wire inst_srai;    
wire inst_add;     
wire inst_sub;     
wire inst_sll;     
wire inst_slt;     
wire inst_sltu;    
wire inst_xor;     
wire inst_srl;     
wire inst_sra;     
wire inst_or;      
wire inst_and;     
wire inst_fence;   
wire inst_fencei;  
wire inst_ecall;   
wire inst_ebreak;  
wire inst_csrrw;   
wire inst_csrrs;   
wire inst_csrrc;   
wire inst_csrrwi;  
wire inst_csrrsi;  
wire inst_csrrci;  
wire inst_lwu;     
wire inst_ld;      
wire inst_sd;      
wire inst_addiw;   
wire inst_slliw;   
wire inst_srliw;   
wire inst_sraiw;   
wire inst_addw;    
wire inst_subw;    
wire inst_sllw;    
wire inst_srlw;    
wire inst_sraw;    
wire inst_mret;    
wire inst_load;    
wire inst_store;   

wire inst_type_R;
wire inst_type_I;
wire inst_type_S;
wire inst_type_B;
wire inst_type_U;
wire inst_type_J;
wire inst_type_CSRI;  // csr immediate



assign o_inst_opcode = inst_opcode;
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

assign inst_lui     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] &  opcode[2];
assign inst_auipc   = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] &  opcode[2];
assign inst_jal     =  opcode[6] &  opcode[5] & ~opcode[4] &  opcode[3] &  opcode[2];
assign inst_jalr    =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] &  opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
assign inst_beq     =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
assign inst_bne     =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
assign inst_blt     =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] & ~func3[0];
assign inst_bge     =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0];
assign inst_bltu    =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
assign inst_bgeu    =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] &  func3[0];
assign inst_lb      = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
assign inst_lh      = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
assign inst_lw      = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];
assign inst_lbu     = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] & ~func3[0];
assign inst_lhu     = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0];
assign inst_sb      = ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
assign inst_sh      = ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
assign inst_sw      = ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];
assign inst_addi    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
assign inst_slti    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];
assign inst_sltiu   = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
assign inst_xori    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] & ~func3[0];
assign inst_ori     = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
assign inst_andi    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] &  func3[0];
assign inst_slli    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
assign inst_srli    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] & ~func7[5];
assign inst_srai    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] &  func7[5];
assign inst_add     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] & ~func7[5];
assign inst_sub     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] &  func7[5];
assign inst_sll     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
assign inst_slt     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];
assign inst_sltu    = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
assign inst_xor     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] & ~func3[0];
assign inst_srl     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] & ~func7[5];
assign inst_sra     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] &  func7[5];
assign inst_or      = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
assign inst_and     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] &  func3[0];
assign inst_fence   = ~opcode[6] & ~opcode[5] & ~opcode[4] &  opcode[3] &  opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
assign inst_fencei  = ~opcode[6] & ~opcode[5] & ~opcode[4] &  opcode[3] &  opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
assign inst_ecall   =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] & ~func7[4] & ~func7[3] & ~func7[0] & ~rs2[1];
assign inst_ebreak  =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] & ~func7[4] & ~func7[3] &  func7[0] & ~rs2[1];
assign inst_csrrw   =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
assign inst_csrrs   =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];
assign inst_csrrc   =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
assign inst_csrrwi  =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0];
assign inst_csrrsi  =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
assign inst_csrrci  =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] &  func3[0];
assign inst_lwu     = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
assign inst_ld      = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
assign inst_sd      = ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
assign inst_addiw   = ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
assign inst_slliw   = ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
assign inst_srliw   = ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] & ~func7[5];
assign inst_sraiw   = ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] &  func7[5];
assign inst_addw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] & ~func7[5];
assign inst_subw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] &  func7[5];
assign inst_sllw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
assign inst_srlw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] & ~func7[5];
assign inst_sraw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] &  func7[5];
assign inst_mret    =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] &  func7[4] &  func7[3] & ~func7[0] & rs2[1];
assign inst_load    = inst_lb | inst_lbu | inst_lh | inst_lhu | inst_lw | inst_lwu | inst_ld;
assign inst_store   = inst_sb | inst_sh | inst_sw | inst_sd;

// arith inst: 10000; logic: 01000;
// load-store: 00100; j: 00010;  sys: 000001
// === I don't use the logic above!
assign inst_opcode[7] = rst ? 1'd0 : 1'd0;
assign inst_opcode[6] = rst ? 1'd0 : 1'd0;
assign inst_opcode[5] = rst ? 1'd0 : 
  ( inst_sltu   | inst_xor    | inst_srl    | inst_sra    | 
    inst_or     | inst_and    | inst_fence  | inst_fencei | 
    inst_ecall  | inst_ebreak | inst_csrrw  | inst_csrrs  | 
    inst_csrrc  | inst_csrrwi | inst_csrrsi | inst_csrrci |
    inst_lwu    | inst_ld     | inst_sd     | inst_addiw  |
    inst_slliw  | inst_srliw  | inst_sraiw  | inst_addw   | 
    inst_subw   | inst_sllw   | inst_srlw   | inst_sraw   |
    inst_mret   );
assign inst_opcode[4] = rst ? 1'd0 : 
  ( inst_sb     | inst_sh     | inst_sw     | inst_addi   | 
    inst_slti   | inst_sltiu  | inst_xori   | inst_ori    | 
    inst_andi   | inst_slli   | inst_srli   | inst_srai   | 
    inst_add    | inst_sub    | inst_sll    | inst_slt    |
    inst_lwu    | inst_ld     | inst_sd     | inst_addiw  |
    inst_slliw  | inst_srliw  | inst_sraiw  | inst_addw   | 
    inst_subw   | inst_sllw   | inst_srlw   | inst_sraw   |
    inst_mret   );
assign inst_opcode[3] = rst ? 1'd0 : 
  ( inst_bge    | inst_bltu   | inst_bgeu   | inst_lb     | 
    inst_lh     | inst_lw     | inst_lbu    | inst_lhu    | 
    inst_andi   | inst_slli   | inst_srli   | inst_srai   | 
    inst_add    | inst_sub    | inst_sll    | inst_slt    | 
    inst_ecall  | inst_ebreak | inst_csrrw  | inst_csrrs  | 
    inst_csrrc  | inst_csrrwi | inst_csrrsi | inst_csrrci |
    inst_sllw   | inst_srlw   | inst_sraw   | inst_subw   |
    inst_mret   );
assign inst_opcode[2] = rst ? 1'd0 : 
  ( inst_jalr   | inst_beq    | inst_bne    | inst_blt    | 
    inst_lh     | inst_lw     | inst_lbu    | inst_lhu    | 
    inst_slti   | inst_sltiu  | inst_xori   | inst_ori    | 
    inst_add    | inst_sub    | inst_sll    | inst_slt    | 
    inst_or     | inst_and    | inst_fence  | inst_fencei | 
    inst_csrrc  | inst_csrrwi | inst_csrrsi | inst_csrrci |
    inst_slliw  | inst_srliw  | inst_sraiw  | inst_mret   );
assign inst_opcode[1] = rst ? 1'd0 : 
  ( inst_auipc  | inst_jal    | inst_bne    | inst_blt    | 
    inst_bgeu   | inst_lb     | inst_lbu    | inst_lhu    | 
    inst_sw     | inst_addi   | inst_xori   | inst_ori    | 
    inst_srli   | inst_srai   | inst_sll    | inst_slt    | 
    inst_srl    | inst_sra    | inst_fence  | inst_fencei | 
    inst_csrrw  | inst_csrrs  | inst_csrrsi | inst_csrrci |
    inst_sd     | inst_addiw  | inst_sraiw  | inst_addw   | 
    inst_srlw   | inst_sraw   );
assign inst_opcode[0] = rst ? 1'd0 : 
  ( inst_lui    | inst_jal    | inst_beq    | inst_blt    | 
    inst_bltu   | inst_lb     | inst_lw     | inst_lhu    | 
    inst_sh     | inst_addi   | inst_sltiu  | inst_ori    | 
    inst_slli   | inst_srai   | inst_sub    | inst_slt    | 
    inst_xor    | inst_sra    | inst_and    | inst_fencei | 
    inst_ebreak | inst_csrrs  | inst_csrrwi | inst_csrrci |
    inst_ld     | inst_addiw  | inst_srliw  | inst_addw   | 
    inst_sllw   | inst_sraw   ); 

assign inst_type_R    = rst ? 1'd0 : 
  ( inst_add    | inst_sub    | inst_sll    | inst_slt    | 
    inst_sltu   | inst_xor    | inst_srl    | inst_sra    | 
    inst_or     | inst_and    | inst_addw   | inst_subw   | 
    inst_sllw   | inst_srlw   | inst_sraw   );
assign inst_type_I    = rst ? 1'd0 : 
  ( inst_jalr   | inst_lb     | inst_lh     | inst_lw     | 
    inst_ld     | inst_lbu    | inst_lhu    | inst_lwu    | 
    inst_addi   | inst_slti   | inst_sltiu  | inst_xori   | 
    inst_ori    | inst_andi   | inst_slli   | inst_srli   | 
    inst_srai   | inst_csrrw  | inst_csrrs  | inst_csrrc  |
    inst_lwu    | inst_ld     | inst_addiw  | inst_slliw  | 
    inst_srliw  | inst_sraiw  | inst_csrrwi | inst_csrrsi | 
    inst_csrrci );
assign inst_type_S    = rst ? 1'd0 : 
  ( inst_sb     | inst_sh     | inst_sw     | inst_sd     );
assign inst_type_B    = rst ? 1'd0 : 
  ( inst_beq    | inst_bne    | inst_blt    | inst_bge   | 
    inst_bltu   | inst_bgeu   );
assign inst_type_U    = rst ? 1'd0 : 
  ( inst_lui    | inst_auipc  );
assign inst_type_J    = rst ? 1'd0 : 
  ( inst_jal    );
assign inst_type_CSRI = rst ? 1'd0 : 
  ( inst_csrrwi | inst_csrrsi | inst_csrrci );

assign o_rs1_ren  = rst ? 1'd0 : ( inst_type_R | inst_type_I | inst_type_S | inst_type_B);
assign o_rs1      = rst ? 5'd0 : ((inst_type_R | inst_type_I | inst_type_S | inst_type_B) ? rs1 : 5'd0 );
assign o_rs2_ren  = rst ? 1'd0 : ( inst_type_R | inst_type_S | inst_type_B);
assign o_rs2      = rst ? 5'd0 : ((inst_type_R | inst_type_S | inst_type_B) ? rs2 : 5'd0 );

assign o_rd_wen   = rst ? 1'd0 : ( inst_type_R | inst_type_I | inst_type_U | inst_type_J | inst_type_CSRI);
assign o_rd       = rst ? 5'd0 : ((inst_type_R | inst_type_I | inst_type_U | inst_type_J | inst_type_CSRI) ? rd  : 5'd0 );

always @(*) begin
  if (rst) begin
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
  if (rst) begin
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
  if (rst) begin
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

//wire _unused_ok = &{1'b0,
//  opcode[1:0],
//  func7[6],
//  func7[2:1],
//  1'b0};

endmodule

// ZhengpuShi

// Execute Interface


module ysyx_210544_exe_stage(
  input   wire                rst,
  input   wire                clk,
  input   wire                i_ex_decoded_req,
  output  wire                o_ex_decoded_ack,
  output  reg                 o_ex_executed_req,
  input   wire                i_ex_executed_ack,
  input   wire  [7 : 0]       i_ex_inst_opcode,
  input   wire  [`YSYX210544_BUS_64]     i_ex_pc,
  input   wire  [`YSYX210544_BUS_32]     i_ex_inst,
  input   wire  [`YSYX210544_BUS_64]     i_ex_op1,
  input   wire  [`YSYX210544_BUS_64]     i_ex_op2,
  input   wire  [`YSYX210544_BUS_64]     i_ex_op3,
  input   wire  [`YSYX210544_BUS_RIDX]   i_ex_rd,
  input   wire                i_ex_rd_wen,
  input   wire                i_ex_clint_mstatus_mie,
  input   wire                i_ex_clint_mie_mtie,
  input   wire                i_ex_clint_mtime_overflow,
  input   wire                i_ex_skipcmt,
  input   wire  [`YSYX210544_BUS_64]     i_ex_csr_rdata,
  output  wire  [11 : 0]      o_ex_csr_addr,
  output  wire                o_ex_csr_ren,
  output  wire                o_ex_csr_wen,
  output  wire  [`YSYX210544_BUS_64]     o_ex_csr_wdata,
  output  wire  [`YSYX210544_BUS_64]     o_ex_pc,
  output  wire  [`YSYX210544_BUS_32]     o_ex_inst,
  output  wire                o_ex_pc_jmp,
  output  wire  [`YSYX210544_BUS_64]     o_ex_pc_jmpaddr,
  output  wire  [`YSYX210544_BUS_RIDX]   o_ex_rd,
  output  wire                o_ex_rd_wen,
  output  wire  [`YSYX210544_BUS_64]     o_ex_rd_wdata,
  output  wire  [7 : 0]       o_ex_inst_opcode,
  output  wire  [`YSYX210544_BUS_64]     o_ex_op1,
  output  wire  [`YSYX210544_BUS_64]     o_ex_op2,
  output  wire  [`YSYX210544_BUS_64]     o_ex_op3,
  output  wire                o_ex_skipcmt,
  output  reg   [`YSYX210544_BUS_32]     o_ex_intrNo
);

wire                          i_disable;

wire                          decoded_hs;
wire                          executed_hs;
wire                          exeU_skip_cmt;

wire                          is_inst_exceptionU;    // 是否为异常指令：ecall, mret
wire                          is_time_int_req;       // 是否产生了时钟中断？

// 通道选择
reg                           o_ena_exeU;
reg                           o_ena_exceptionU;

wire                          exeU_pc_jmp;
wire [`YSYX210544_BUS_64]                exeU_pc_jmpaddr;
wire   [11 : 0]               exeU_csr_addr;
wire                          exeU_csr_ren;
wire                          exeU_csr_wen;
wire   [`YSYX210544_BUS_64]              exeU_csr_wdata;

wire                          exceptionU_req;
wire                          exceptionU_pc_jmp;
wire [`YSYX210544_BUS_64]                exceptionU_pc_jmpaddr;
wire   [11 : 0]               exceptionU_csr_addr;
wire                          exceptionU_csr_ren;
wire                          exceptionU_csr_wen;
wire   [`YSYX210544_BUS_64]              exceptionU_csr_wdata;

// 保存输入信息
reg   [7 : 0]                 tmp_i_ex_inst_opcode;
reg   [`YSYX210544_BUS_64]               tmp_i_ex_pc;
reg   [`YSYX210544_BUS_32]               tmp_i_ex_inst;
reg   [`YSYX210544_BUS_64]               tmp_i_ex_op1;
reg   [`YSYX210544_BUS_64]               tmp_i_ex_op2;
reg   [`YSYX210544_BUS_64]               tmp_i_ex_op3;
reg   [4 : 0]                 tmp_i_ex_rd;
reg                           tmp_i_ex_rd_wen;
reg                           tmp_i_ex_skipcmt;



assign i_disable = rst | (!executed_hs);

assign o_ex_decoded_ack = 1'b1;

assign decoded_hs = i_ex_decoded_req & o_ex_decoded_ack;
assign executed_hs = i_ex_executed_ack & o_ex_executed_req;

assign is_inst_exceptionU = (i_ex_inst_opcode == `YSYX210544_INST_ECALL) | (i_ex_inst_opcode == `YSYX210544_INST_MRET);
assign is_time_int_req = i_ex_clint_mstatus_mie & i_ex_clint_mie_mtie & i_ex_clint_mtime_overflow;

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
      tmp_i_ex_skipcmt
    } <= 0;

    o_ena_exeU          <= 0;
    o_ena_exceptionU    <= 0;
    o_ex_executed_req   <= 0;
    o_ex_intrNo         <= 0;
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
    // exceptionU结束，请求信号置位
    else if (exceptionU_req) begin
      o_ex_executed_req <= 1;
    end
    // exeU或exceptionU收到应答，请求信号撤销
    else if (executed_hs) begin
      o_ena_exeU        <= 0;
      o_ena_exceptionU  <= 0;
      o_ex_executed_req <= 0;
      o_ex_intrNo       <= 0;
    end
  end
end

assign o_ex_pc            = i_disable ? 64'd0 : tmp_i_ex_pc;
assign o_ex_inst          = i_disable ? 32'd0 : tmp_i_ex_inst;
assign o_ex_op1           = i_disable ? 64'd0 : tmp_i_ex_op1;
assign o_ex_op2           = i_disable ? 64'd0 : tmp_i_ex_op2;
assign o_ex_op3           = i_disable ? 64'd0 : tmp_i_ex_op3;
assign o_ex_inst_opcode   = i_disable ?  8'd0 : tmp_i_ex_inst_opcode;
assign o_ex_rd            = i_disable ?  5'd0 : (!o_ena_exeU ? 5'd0 : tmp_i_ex_rd);
assign o_ex_rd_wen        = i_disable ?  1'd0 : (!o_ena_exeU ? 1'd0 : tmp_i_ex_rd_wen);
assign o_ex_skipcmt       = i_disable ?  1'd0 : (tmp_i_ex_skipcmt | exeU_skip_cmt);

assign o_ex_pc_jmp      = rst ?  1'd0 : (o_ena_exeU ? exeU_pc_jmp     : exceptionU_pc_jmp);
assign o_ex_pc_jmpaddr  = rst ? 64'd0 : (o_ena_exeU ? exeU_pc_jmpaddr : exceptionU_pc_jmpaddr);
assign o_ex_csr_addr    = rst ? 12'd0 : (o_ena_exeU ? exeU_csr_addr   : exceptionU_csr_addr);
assign o_ex_csr_ren     = rst ?  1'd0 : (o_ena_exeU ? exeU_csr_ren    : exceptionU_csr_ren);
assign o_ex_csr_wen     = rst ?  1'd0 : (o_ena_exeU ? exeU_csr_wen    : exceptionU_csr_wen);
assign o_ex_csr_wdata   = rst ? 64'd0 : (o_ena_exeU ? exeU_csr_wdata  : exceptionU_csr_wdata);

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
  input   wire  [`YSYX210544_BUS_64]     i_op1,
  input   wire  [`YSYX210544_BUS_64]     i_op2,
  input   wire  [`YSYX210544_BUS_64]     i_op3,
  input   wire  [`YSYX210544_BUS_64]     i_csr_rdata,
  output  wire  [11 : 0]      o_csr_addr,
  output  wire                o_csr_ren,
  output  wire                o_csr_wen,
  output  reg   [`YSYX210544_BUS_64]     o_csr_wdata,
  output  reg                 o_pc_jmp,
  output  reg   [`YSYX210544_BUS_64]     o_pc_jmpaddr,
  output  reg   [`YSYX210544_BUS_64]     o_rd_wdata,
  output  wire                o_exeU_skip_cmt    // 这里也会发现需要跳过提交的指令，比如 csr mcycle
);

wire i_disable;
wire [63:0] reg64_t1;
wire [63:0] reg64_t2;
wire [63:0] reg64_t3;
wire [63:0] reg64_t4;
wire [31:0] reg32_t1;
wire inst_csr;



assign i_disable = !ena;
assign reg64_t1 = i_op1 + i_op2;
assign reg64_t2 = i_op1 << i_op2[5:0];
assign reg64_t3 = i_op1 - $signed(i_op2);
assign reg64_t4 = i_op1 << i_op2[4:0];
assign reg32_t1 = i_op1[31:0] >> i_op2[4:0];

always @(*) begin
  if( i_disable ) begin
    o_rd_wdata = `YSYX210544_ZERO_WORD;
  end
  else begin
    case( i_inst_opcode )
      `YSYX210544_INST_ADDI    : begin o_rd_wdata = i_op1 + i_op2;  end
      `YSYX210544_INST_ADD     : begin o_rd_wdata = i_op1 + i_op2;  end
      `YSYX210544_INST_SUB     : begin o_rd_wdata = i_op1 - i_op2;  end
      `YSYX210544_INST_SUBW    : begin o_rd_wdata = {{33{reg64_t3[31]}}, reg64_t3[30:0]}; end
      `YSYX210544_INST_ADDIW   : begin o_rd_wdata = {{33{reg64_t1[31]}}, reg64_t1[30:0]}; end
      `YSYX210544_INST_AND     : begin o_rd_wdata = i_op1 & i_op2;  end
      `YSYX210544_INST_ANDI    : begin o_rd_wdata = i_op1 & i_op2;  end
      `YSYX210544_INST_OR      : begin o_rd_wdata = i_op1 | i_op2;  end
      `YSYX210544_INST_ORI     : begin o_rd_wdata = i_op1 | i_op2;  end
      `YSYX210544_INST_XOR     : begin o_rd_wdata = i_op1 ^ i_op2;  end
      `YSYX210544_INST_XORI    : begin o_rd_wdata = i_op1 ^ i_op2;  end
      `YSYX210544_INST_SLL     : begin o_rd_wdata = i_op1 << i_op2[5:0]; end
      `YSYX210544_INST_SLLI    : begin o_rd_wdata = i_op1 << i_op2[5:0]; end
      `YSYX210544_INST_SLLIW   : begin o_rd_wdata = {{33{reg64_t2[31]}}, reg64_t2[30:0]}; end
      `YSYX210544_INST_SLLW    : begin o_rd_wdata = {{33{reg64_t4[31]}}, reg64_t4[30:0]}; end
      `YSYX210544_INST_SLT     : begin o_rd_wdata = ($signed(i_op1) < $signed(i_op2)) ? 1 : 0; end
      `YSYX210544_INST_SLTI    : begin o_rd_wdata = ($signed(i_op1) < $signed(i_op2)) ? 1 : 0; end
      `YSYX210544_INST_SLTIU   : begin o_rd_wdata = i_op1 < i_op2 ? 1 : 0; end
      `YSYX210544_INST_SLTU    : begin o_rd_wdata = (i_op1 < i_op2) ? 1 : 0; end
      `YSYX210544_INST_SRA     : begin o_rd_wdata = $signed(i_op1) >>> i_op2[5:0]; end
      `YSYX210544_INST_SRAW    : begin o_rd_wdata = $signed({{33{i_op1[31]}}, i_op1[30:0]}) >>> i_op2[4:0]; end
      `YSYX210544_INST_SRAI    : begin o_rd_wdata = $signed(i_op1) >>> i_op2[5:0]; end
      `YSYX210544_INST_SRAIW   : begin o_rd_wdata = $signed({{33{i_op1[31]}}, i_op1[30:0]}) >>> i_op2[4:0]; end
      `YSYX210544_INST_SRL     : begin o_rd_wdata = i_op1 >> i_op2[5:0]; end
      `YSYX210544_INST_SRLI    : begin o_rd_wdata = i_op1 >> i_op2[5:0]; end
      `YSYX210544_INST_SRLW    : begin o_rd_wdata = {{32{reg32_t1[31]}}, reg32_t1}; end
      `YSYX210544_INST_SRLIW   : begin o_rd_wdata = {{32{reg32_t1[31]}}, reg32_t1}; end
      `YSYX210544_INST_LUI     : begin o_rd_wdata = i_op1; end
      `YSYX210544_INST_AUIPC   : begin o_rd_wdata = i_op1 + i_op2; end
      `YSYX210544_INST_JAL     : begin o_rd_wdata = i_op1 + i_op2; end
      `YSYX210544_INST_JALR    : begin o_rd_wdata = i_op3; end
      `YSYX210544_INST_CSRRW   : begin o_rd_wdata = i_csr_rdata; end
      `YSYX210544_INST_CSRRS   : begin o_rd_wdata = i_csr_rdata; end
      `YSYX210544_INST_CSRRC   : begin o_rd_wdata = i_csr_rdata; end
      `YSYX210544_INST_CSRRWI  : begin o_rd_wdata = i_csr_rdata; end
      `YSYX210544_INST_CSRRSI  : begin o_rd_wdata = i_csr_rdata; end
      `YSYX210544_INST_CSRRCI  : begin o_rd_wdata = i_csr_rdata; end
      default       : begin o_rd_wdata = `YSYX210544_ZERO_WORD; end
    endcase
  end
end

// o_pc_jmp
always @(*) begin
  if ( i_disable ) begin
    o_pc_jmp = 1'd0;
  end
  else begin
    case (i_inst_opcode)
      `YSYX210544_INST_BEQ   : begin o_pc_jmp = (i_op1 == i_op2) ? 1'd1 : 1'd0; end
      `YSYX210544_INST_BNE   : begin o_pc_jmp = (i_op1 != i_op2) ? 1'd1 : 1'd0; end
      `YSYX210544_INST_BLT   : begin o_pc_jmp = ($signed(i_op1) <  $signed(i_op2)) ? 1'd1 : 1'd0; end
      `YSYX210544_INST_BGE   : begin o_pc_jmp = ($signed(i_op1) >= $signed(i_op2)) ? 1'd1 : 1'd0; end
      `YSYX210544_INST_BLTU  : begin o_pc_jmp = (i_op1 <  i_op2) ? 1'd1 : 1'd0; end
      `YSYX210544_INST_BGEU  : begin o_pc_jmp = (i_op1 >= i_op2) ? 1'd1 : 1'd0; end
      `YSYX210544_INST_JAL   : begin o_pc_jmp = 1'd1; end
      `YSYX210544_INST_JALR  : begin o_pc_jmp = 1'd1; end
      default     : begin o_pc_jmp = 1'd0; end
    endcase
  end
end

// o_pc_jmpaddr
always @(*) begin
  if ( i_disable ) begin
    o_pc_jmpaddr = 64'd0;
  end
  else begin
    case (i_inst_opcode)
      `YSYX210544_INST_JAL   : begin o_pc_jmpaddr = i_op3; end
      `YSYX210544_INST_JALR  : begin o_pc_jmpaddr = (i_op1 + i_op2) & ~64'd1; end
      `YSYX210544_INST_BEQ   : begin o_pc_jmpaddr = i_op3; end
      `YSYX210544_INST_BNE   : begin o_pc_jmpaddr = i_op3; end
      `YSYX210544_INST_BLT   : begin o_pc_jmpaddr = i_op3; end
      `YSYX210544_INST_BGE   : begin o_pc_jmpaddr = i_op3; end
      `YSYX210544_INST_BLTU  : begin o_pc_jmpaddr = i_op3; end
      `YSYX210544_INST_BGEU  : begin o_pc_jmpaddr = i_op3; end
      default     : begin o_pc_jmpaddr = 64'd0; end
    endcase
  end
end

// ------------- csr -----------------

assign inst_csr = 
  (i_inst_opcode == `YSYX210544_INST_CSRRW ) | (i_inst_opcode == `YSYX210544_INST_CSRRS ) | 
  (i_inst_opcode == `YSYX210544_INST_CSRRC ) | (i_inst_opcode == `YSYX210544_INST_CSRRWI) | 
  (i_inst_opcode == `YSYX210544_INST_CSRRSI) | (i_inst_opcode == `YSYX210544_INST_CSRRCI) ;

assign o_csr_ren  = (i_disable) ?  1'd0 : inst_csr;
assign o_csr_wen  = (i_disable) ?  1'd0 : inst_csr;
assign o_csr_addr = (i_disable) ? 12'd0 : (inst_csr ? i_op2[11:0] : 12'd0);

always @(*) begin
  if (i_disable) begin
    o_csr_wdata = 64'd0;
  end
  else begin
    case (i_inst_opcode)
      `YSYX210544_INST_CSRRW   : o_csr_wdata = i_op1;
      `YSYX210544_INST_CSRRS   : o_csr_wdata = i_csr_rdata | i_op1;
      `YSYX210544_INST_CSRRC   : o_csr_wdata = i_csr_rdata & (~i_op1);
      `YSYX210544_INST_CSRRWI  : o_csr_wdata = i_op1;
      `YSYX210544_INST_CSRRSI  : o_csr_wdata = i_csr_rdata | i_op1;
      `YSYX210544_INST_CSRRCI  : o_csr_wdata = i_csr_rdata & (~i_op1);
      default       : o_csr_wdata = 64'd0;
    endcase
  end
end

assign o_exeU_skip_cmt = (inst_csr && (o_csr_addr == 12'hB00));

//wire _unused_ok = &{1'b0,
//  reg64_t1[63:32],
//  reg64_t2[63:32],
//  reg64_t3[63:32],
//  reg64_t4[63:32],
//  1'b0};

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
  input   wire  [`YSYX210544_BUS_64]     i_pc,
  output  reg                 o_pc_jmp,
  output  reg   [`YSYX210544_BUS_64]     o_pc_jmpaddr,
  input   wire  [`YSYX210544_BUS_64]     i_csr_rdata,
  output  reg   [11 : 0]      o_csr_addr,
  output  reg                 o_csr_ren,
  output  reg                 o_csr_wen,
  output  reg   [`YSYX210544_BUS_64]     o_csr_wdata
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
reg [3:0] next_state;
reg [1:0] step;
// 在异常发生的第一个时钟周期就确定下来，因为有些输入信号只保持一个周期
reg [63:0] exception_cause;     // 异常原因
wire hs;
reg [63:0] csr_rdata_save1;
reg [63:0] csr_rdata_save2;


// state machine
always @(posedge clk) begin
  if (rst) begin
    state <= STATE_NULL;
  end
  else begin
    state <= next_state;
  end
end

assign hs = ack & req;

// user action
always @(posedge clk) begin
  if (rst) begin
    next_state          <= STATE_NULL;
    step                <= 0;
    exception_cause     <= 0;
    o_pc_jmp            <= 0;
    o_pc_jmpaddr        <= 0;

    o_csr_addr          <= 0;
    o_csr_ren           <= 0;
    o_csr_wen           <= 0;
    o_csr_wdata         <= 0;
    csr_rdata_save1     <= 0;
    csr_rdata_save2     <= 0;

    req                 <= 0;
  end
  else begin
    if (!hs) begin
      case (state)
        STATE_NULL: begin
          // 如果有使能信号，则进入不同的状态
          if (ena) begin
            if (i_inst_opcode == `YSYX210544_INST_ECALL) begin
              next_state <= STATE_ENTER_WRITE_MEPC;
              exception_cause <= 64'd11;
              //$write("#ecall\n"); $fflush();
            end
            else if (i_inst_opcode == `YSYX210544_INST_MRET) begin
              next_state <= STATE_LEAVE_READ_MSTATUS;
            end
            else begin
              next_state <= STATE_ENTER_WRITE_MEPC;
              exception_cause <= 64'h80000000_00000007;
              // $write("#time-instr\n"); $fflush();
              // $write("."); $fflush();
            end
          end

          // 空闲时清空jmp信号
          o_pc_jmp <= 0;
          o_pc_jmpaddr <= 0;  
        end

        STATE_ENTER_WRITE_MEPC: begin
          case (step)
            0:  begin 
              // 防止再次进入
              if (state == next_state) begin 
                o_csr_addr      <=`YSYX210544_CSR_ADR_MEPC; 
                o_csr_wen       <= 1; 
                o_csr_wdata     <= i_pc;
                step            <= 1;
              end
            end
            1:  begin
              o_csr_wen       <= 0;
              step            <= 2;
            end
            2:  begin
              next_state 		  <= STATE_ENTER_WRITE_MCAUSE;
              step 				    <= 0;
            end
            default: ;
          endcase
        end

        STATE_ENTER_WRITE_MCAUSE: begin
          case (step)
            0:  begin 
              // 防止再次进入
              if (state == next_state) begin 
                o_csr_addr      <=`YSYX210544_CSR_ADR_MCAUSE; 
                o_csr_wen       <= 1; 
                o_csr_wdata     <= exception_cause;
                step            <= 1;
              end
            end
            1:  begin
              o_csr_wen       <= 0;
              step            <= 2;
            end
            2:  begin
              next_state      <= STATE_ENTER_READ_MTVEC;
              step            <= 0;
            end
            default: ;
          endcase
        end

        STATE_ENTER_READ_MTVEC: begin
          case (step)
            0:  begin 
              // 防止再次进入
              if (state == next_state) begin 
                o_csr_addr      <=`YSYX210544_CSR_ADR_MTVEC; 
                o_csr_ren       <= 1; 
                step            <= 1;
              end
            end
            1:  begin
              o_csr_ren       <= 0;
              step            <= 2;
              csr_rdata_save2 <= i_csr_rdata;
            end
            2:  begin
              next_state      <= STATE_ENTER_READ_MSTATUS;
              step            <= 0;
            end
            default: ;
          endcase
        end
        
        STATE_ENTER_READ_MSTATUS: begin
          case (step)
            0:  begin 
              // 防止再次进入
              if (state == next_state) begin 
                o_csr_addr      <=`YSYX210544_CSR_ADR_MSTATUS; 
                o_csr_ren       <= 1; 
                step            <= 1;
              end
            end
            1:  begin
              o_csr_ren       <= 0;
              step            <= 2;
              csr_rdata_save1 <= i_csr_rdata;
            end
            2:  begin
              next_state      <= STATE_ENTER_WRITE_MSTATUS;
              step            <= 0;
            end
            default: ;
          endcase
        end
        
        STATE_ENTER_WRITE_MSTATUS: begin
          case (step)
            0:  begin 
              // 防止再次进入
              if (state == next_state) begin 
                o_csr_addr      <=`YSYX210544_CSR_ADR_MSTATUS; 
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
            end
            1:  begin
              o_csr_wen       <= 0;
              step            <= 2;
              o_pc_jmp        <= 1;
              o_pc_jmpaddr    <= csr_rdata_save2;
            end
            2:  begin
              next_state      <= STATE_NULL;
              step            <= 0;
              req             <= 1;
            end
            default: ;
          endcase
        end
        
        STATE_LEAVE_READ_MSTATUS: begin
          case (step)
            0:  begin
              // 防止再次进入
              if (state == next_state) begin 
                o_csr_addr      <=`YSYX210544_CSR_ADR_MSTATUS; 
                o_csr_ren       <= 1; 
                step            <= 1;
              end
            end
            1:  begin
              o_csr_ren       <= 0;
              step            <= 2;
              csr_rdata_save1 <= i_csr_rdata;
            end
            2:  begin
              next_state      <= STATE_LEAVE_READ_MEPC;
              step            <= 0;
            end
            default: ;
          endcase
        end

        STATE_LEAVE_READ_MEPC: begin
          case (step)
            0:  begin 
              // 防止再次进入
              if (state == next_state) begin 
                o_csr_addr      <=`YSYX210544_CSR_ADR_MEPC; 
                o_csr_ren       <= 1; 
                step            <= 1;
              end
            end
            1:  begin
              o_csr_ren       <= 0;
              csr_rdata_save2 <= i_csr_rdata;
              step            <= 2;
            end
            2:  begin
              next_state      <= STATE_LEAVE_WRITE_MSTATUS;
              step            <= 0;
            end
            default: ;
          endcase
        end
        
        STATE_LEAVE_WRITE_MSTATUS: begin
          case (step)
            0:  begin 
              // 防止再次进入
              if (state == next_state) begin 
                o_csr_addr      <=`YSYX210544_CSR_ADR_MSTATUS; 
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
            end
            1:  begin
              o_csr_wen       <= 0;
              step            <= 2;
              o_pc_jmp        <= 1;
              o_pc_jmpaddr    <= csr_rdata_save2;
            end
            2:  begin
              next_state      <= STATE_NULL;
              step            <= 0;
              req             <= 1;
            end
            default: ;
          endcase
        end

        default: ;
      endcase
    end
    else begin
      req <= 0;
    end
  end
end

//wire _unused_ok = &{1'b0,
//  csr_rdata_save1[12:11],
//  1'b0};

endmodule

// ZhengpuShi

// Memory Interface


module ysyx_210544_mem_stage(
  input   wire                clk,
  input   wire                rst,
  input   wire                i_mem_executed_req,
  output  wire                o_mem_executed_ack,
  output  reg                 o_mem_memoryed_req,
  input   wire                i_mem_memoryed_ack,
  input   wire  [`YSYX210544_BUS_64]     i_mem_pc,
  input   wire  [`YSYX210544_BUS_32]     i_mem_inst,
  input   wire  [`YSYX210544_BUS_RIDX]   i_mem_rd,
  input   wire                i_mem_rd_wen,
  input   wire  [`YSYX210544_BUS_64]     i_mem_rd_wdata,
  input   wire                i_mem_skipcmt,
  input   wire  [7 : 0]       i_mem_inst_opcode,
  input   wire  [`YSYX210544_BUS_64]     i_mem_op1,
  input   wire  [`YSYX210544_BUS_64]     i_mem_op2,
  input   wire  [`YSYX210544_BUS_64]     i_mem_op3,
  output  wire  [`YSYX210544_BUS_RIDX]   o_mem_rd,
  output  wire                o_mem_rd_wen,
  output  reg   [`YSYX210544_BUS_64]     o_mem_rd_wdata,
  output  wire  [`YSYX210544_BUS_64]     o_mem_pc,
  output  wire  [`YSYX210544_BUS_32]     o_mem_inst,
  output  wire                o_mem_skipcmt,
  output  wire                o_mem_clint_mtime_overflow,
  input   wire  [`YSYX210544_BUS_32]     i_mem_intrNo,
  output  reg   [`YSYX210544_BUS_32]     o_mem_intrNo,
  output  wire                o_mem_fencei_req,
  input   wire                i_mem_fencei_ack,

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

wire                          executed_hs;
wire                          memoryed_hs;
wire                          addr_is_mem;
wire                          addr_is_mmio;
wire                          ren_or_wen;
wire                          ch_cachesync; 
wire                          ch_mem;   
wire                          ch_mmio;  
wire                          ch_none;  

// memoryed request for different slaves
wire                          memoryed_req_cachesync;
wire                          memoryed_req_mem;
wire                          memoryed_req_mmio;
wire                          memoryed_req_none;
wire   [`YSYX210544_BUS_64]              rdata_mem;      // readed data from mmio
wire   [`YSYX210544_BUS_64]              rdata_mmio;     // readed data from main memory
reg    [`YSYX210544_BUS_64]              rdata;          // readed data from main memory or mmio

// 保存输入信息
reg   [`YSYX210544_BUS_64]               tmp_i_mem_pc;
reg   [`YSYX210544_BUS_32]               tmp_i_mem_inst;
reg   [`YSYX210544_BUS_RIDX]             tmp_i_mem_rd;
reg                           tmp_i_mem_rd_wen;
reg   [`YSYX210544_BUS_64]               tmp_i_mem_rd_wdata;
reg   [7 : 0]                 tmp_i_mem_inst_opcode;
reg                           tmp_i_mem_skipcmt;
reg                           tmp_ch_cachesync;
reg                           tmp_ch_mem;
reg                           tmp_ch_mmio;

wire [63:0]                   mem_addr;
reg  [2:0]                    mem_bytes;
reg                           mem_ren;
reg                           mem_wen;
reg  [63:0]                   mem_wdata;



assign o_mem_executed_ack = 1'b1;

assign executed_hs = i_mem_executed_req & o_mem_executed_ack;
assign memoryed_hs = i_mem_memoryed_ack & o_mem_memoryed_req;

assign addr_is_mem  = (mem_addr[31:28] != 4'b0);
assign addr_is_mmio = (mem_addr[31:24] == 8'h02);// & (64'hFF000000)) == 64'h02000000;

// channel select, only valid in one pulse
assign ren_or_wen = mem_ren | mem_wen;

assign ch_cachesync = i_mem_inst_opcode == `YSYX210544_INST_FENCEI;
assign ch_mem   = addr_is_mem & ren_or_wen;
assign ch_mmio  = addr_is_mmio & ren_or_wen;
assign ch_none  = (!ch_cachesync) & ((!(addr_is_mem | addr_is_mmio)) | (!ren_or_wen));

// o_mem_memoryed_req
always @(*) begin
  if (rst) begin
    o_mem_memoryed_req = 0;
  end
  else if (tmp_ch_cachesync) begin
    o_mem_memoryed_req = memoryed_req_cachesync;
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
      tmp_i_mem_skipcmt,
      tmp_ch_cachesync,
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
      tmp_i_mem_skipcmt         <= i_mem_skipcmt;
      tmp_ch_cachesync          <= ch_cachesync;
      tmp_ch_mem                <= ch_mem;
      tmp_ch_mmio               <= ch_mmio;

      o_mem_intrNo <= i_mem_intrNo;
    end
    else if (memoryed_hs) begin
      // 该通道号需要消除，不能留到下一个指令
      tmp_ch_cachesync          <= 0;
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
// assign o_mem_rd_wdata     = tmp_i_mem_rd_wdata;
assign o_mem_skipcmt      = tmp_i_mem_skipcmt | tmp_ch_mmio;

// ren, only valid at one pulse
always @(*) begin
  if (rst) begin
    mem_ren = 0;
  end
  else begin
    case (i_mem_inst_opcode)
      `YSYX210544_INST_LB  : begin mem_ren = 1; end
      `YSYX210544_INST_LBU : begin mem_ren = 1; end
      `YSYX210544_INST_LH  : begin mem_ren = 1; end
      `YSYX210544_INST_LHU : begin mem_ren = 1; end 
      `YSYX210544_INST_LW  : begin mem_ren = 1; end
      `YSYX210544_INST_LWU : begin mem_ren = 1; end
      `YSYX210544_INST_LD  : begin mem_ren = 1; end
      default   : begin mem_ren = 0; end
    endcase
  end
end

// wen, only valid at one pulse
always @(*) begin
  if (rst) begin
    mem_wen = 0;
  end
  else begin
    case (i_mem_inst_opcode)
      `YSYX210544_INST_SB  : begin mem_wen = 1; end
      `YSYX210544_INST_SH  : begin mem_wen = 1; end
      `YSYX210544_INST_SW  : begin mem_wen = 1; end
      `YSYX210544_INST_SD  : begin mem_wen = 1; end
      default   : begin mem_wen = 0; end
    endcase
  end
end

// addr, only valid at one pulse
assign mem_addr = i_mem_op1 + i_mem_op3;

// bytes, only valid at one pulse
always @(*) begin
  if (rst) begin
    mem_bytes = 0;
  end
  else begin
    case (i_mem_inst_opcode)
      `YSYX210544_INST_LB  : begin mem_bytes = 0; end
      `YSYX210544_INST_LBU : begin mem_bytes = 0; end
      `YSYX210544_INST_SB  : begin mem_bytes = 0; end
      `YSYX210544_INST_LH  : begin mem_bytes = 1; end
      `YSYX210544_INST_LHU : begin mem_bytes = 1; end 
      `YSYX210544_INST_SH  : begin mem_bytes = 1; end
      `YSYX210544_INST_LW  : begin mem_bytes = 3; end
      `YSYX210544_INST_SW  : begin mem_bytes = 3; end
      `YSYX210544_INST_LWU : begin mem_bytes = 3; end
      `YSYX210544_INST_LD  : begin mem_bytes = 7; end
      `YSYX210544_INST_SD  : begin mem_bytes = 7; end
      default   : begin mem_bytes = 0; end
    endcase
  end
end

// wdata, only valid at one pulse
always @(*) begin
  if (rst) begin
    mem_wdata = 0;
  end
  else begin
    case (i_mem_inst_opcode)
      `YSYX210544_INST_SB  : begin mem_wdata = {56'd0, i_mem_op2[7:0]}; end
      `YSYX210544_INST_SH  : begin mem_wdata = {48'd0, i_mem_op2[15:0]}; end
      `YSYX210544_INST_SW  : begin mem_wdata = {32'd0, i_mem_op2[31:0]}; end
      `YSYX210544_INST_SD  : begin mem_wdata = i_mem_op2[63:0]; end
      default   : begin mem_wdata = 0; end
    endcase
  end
end

// rdata, valid at several pulses
always @(*) begin
  if (rst) begin
    o_mem_rd_wdata = 0;
  end
  else begin
    case (tmp_i_mem_inst_opcode)
      `YSYX210544_INST_LB  : begin o_mem_rd_wdata = {{57{rdata[7]}}, rdata[6:0]} ; end
      `YSYX210544_INST_LBU : begin o_mem_rd_wdata = {56'd0, rdata[7:0]}; end
      `YSYX210544_INST_LH  : begin o_mem_rd_wdata = {{49{rdata[15]}}, rdata[14:0]}; end
      `YSYX210544_INST_LHU : begin o_mem_rd_wdata = {48'd0, rdata[15:0]}; end
      `YSYX210544_INST_LW  : begin o_mem_rd_wdata = {{33{rdata[31]}}, rdata[30:0]}; end
      `YSYX210544_INST_LWU : begin o_mem_rd_wdata = {32'd0, rdata[31:0]}; end
      `YSYX210544_INST_LD  : begin o_mem_rd_wdata = rdata[63:0]; end
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

// 访问Cache
ysyx_210544_mem_cachesync Mem_cachesync(
  .clk                        (clk                        ),
  .rst                        (rst                        ),
  .start                      (i_mem_executed_req & ch_cachesync),
  .ack                        (i_mem_memoryed_ack         ),
  .req                        (memoryed_req_cachesync     ),
  .o_cachesync_req            (o_mem_fencei_req           ),
  .i_cachesync_ack            (i_mem_fencei_ack           )
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

  input   wire  [`YSYX210544_BUS_64]     i_addr,
  input   wire  [2:0]         i_bytes,
  input   wire                i_ren,
  input   wire                i_wen,
  input   wire  [`YSYX210544_BUS_64]     i_wdata,
  output  reg   [`YSYX210544_BUS_64]     o_rdata,

  ///////////////////////////////////////////////
  // DCache interface
  output  reg                 o_dcache_req,
  output  reg   [63:0]        o_dcache_addr,
  output  reg                 o_dcache_op,
  output  reg   [2 :0]        o_dcache_bytes,
  output  reg   [63:0]        o_dcache_wdata,
  input   wire                i_dcache_ack,
  input   wire  [63:0]        i_dcache_rdata
);

wire                          hs_dcache;
reg                           wait_finish;  // 是否等待访存完毕？


assign hs_dcache  = o_dcache_req & i_dcache_ack;

always @(posedge clk) begin
  if (rst) begin
    wait_finish     <= 0;
    req             <= 0;
    o_rdata         <= 0;
    o_dcache_req    <= 0;
    o_dcache_op     <= 0;
    o_dcache_addr   <= 0;
    o_dcache_bytes  <= 0;
    o_dcache_wdata  <= 0;
  end
  else begin
    if (start) begin
      if (i_ren) begin
        o_dcache_req      <= 1;
        o_dcache_op       <= `YSYX210544_REQ_READ;
        o_dcache_addr     <= i_addr;
        o_dcache_bytes    <= i_bytes;
        wait_finish       <= 1;
      end
      else if (i_wen) begin
        o_dcache_req      <= 1;
        o_dcache_op       <= `YSYX210544_REQ_WRITE;
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
  input   wire [`YSYX210544_BUS_64]      addr,
  input   wire [`YSYX210544_BUS_64]      wdata,
  output  reg  [`YSYX210544_BUS_64]      rdata,
  output  wire                o_clint_mtime_overflow
);

// rtc设备
wire  [`YSYX210544_BUS_64]               rtc_rdata;
wire  [`YSYX210544_BUS_64]               i_clint_rdata;



ysyx_210544_rtc Rtc(
  .clk                (clk              ),
  .rst                (rst              ),
  .ren                (ren & (addr == `YSYX210544_DEV_RTC)),
  .rdata              (rtc_rdata        )
);

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

// Custom MMIO area
reg   [`YSYX210544_BUS_64]               custom_regs[0:15];

/*
---------original info-----------------
DESIGNED BY ZHENGPU SHI
LAST UPDATE TIME : 2021/10/23 15:12:50
AT NUAA/CS/ROOM 415
---------binary data-------------------
44 45 53 49 47 4E 45 44 
20 42 59 20 5A 48 45 4E 
47 50 55 20 53 48 49 0A 
4C 41 53 54 20 55 50 44 
41 54 45 20 54 49 4D 45 
20 3A 20 32 30 32 31 2F 
31 30 2F 32 33 20 31 35 
3A 31 32 3A 35 30 0A 41 
54 20 4E 55 41 41 2F 43 
53 2F 52 4F 4F 4D 20 34 
31 35 0A 00 00 00 00 00
---------verilog code-------------------
64'h44_45_4E_47_49_53_45_44; 
64'h4E_45_48_5A_20_59_42_20; 
64'h0A_49_48_53_20_55_50_47; 
64'h44_50_55_20_54_53_41_4C; 
64'h45_4D_49_54_20_45_54_41; 
64'h2F_31_32_30_32_20_3A_20; 
64'h35_31_20_33_32_2F_30_31; 
64'h41_0A_30_35_3A_32_31_3A; 
64'h43_2F_41_41_55_4E_20_54; 
64'h34_20_4D_4F_4F_52_2F_53; 
64'h00_00_00_00_00_0A_35_31;
--------usage --------------------------
1. get data from 0x02008000,+1,+2,..., get 64bit (8byte) every time.
2. show byte from lsb, if find \00, then stop
3. we should print the original info.
*/
always @(posedge clk) begin
  if (rst) begin
    custom_regs[0] <= 64'h44_45_4E_47_49_53_45_44;
    custom_regs[1] <= 64'h4E_45_48_5A_20_59_42_20;
    custom_regs[2] <= 64'h0A_49_48_53_20_55_50_47;
    custom_regs[3] <= 64'h44_50_55_20_54_53_41_4C;
    custom_regs[4] <= 64'h45_4D_49_54_20_45_54_41;
    custom_regs[5] <= 64'h2F_31_32_30_32_20_3A_20;
    custom_regs[6] <= 64'h35_31_20_33_32_2F_30_31;
    custom_regs[7] <= 64'h41_0A_30_35_3A_32_31_3A;
    custom_regs[8] <= 64'h43_2F_41_41_55_4E_20_54;
    custom_regs[9] <= 64'h34_20_4D_4F_4F_52_2F_53;
    custom_regs[10] <= 64'h00_00_00_00_00_0A_35_31;
    custom_regs[11] <= 0;
    custom_regs[12] <= 0;
    custom_regs[13] <= 0;
    custom_regs[14] <= 0;
    custom_regs[15] <= 0;
  end
end

always @(posedge clk) begin
    if (rst) begin
        req   <= 0;
        rdata <= 0;
    end
    else begin
        // set request
        if (start) begin
            if (ren) begin
                if (addr == `YSYX210544_DEV_RTC)             rdata <= rtc_rdata;
                else if (addr == `YSYX210544_DEV_MTIME)      rdata <= i_clint_rdata;
                else if (addr == `YSYX210544_DEV_MTIMECMP)   rdata <= i_clint_rdata;
                else if ((addr & `YSYX210544_DEV_CUSTOM_MASK) == `YSYX210544_DEV_CUSTOM) begin
                  rdata <= custom_regs[addr[3:0]];
                end
                req <= 1;
            end
            else begin
                req <= 1;
            end
        end
        // clear request
        else if (ack) begin
            req   <= 0;
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

// Memory State for Cache Sync


module ysyx_210544_mem_cachesync(
  input   wire                clk,
  input   wire                rst,

  input   wire                start,
  input   wire                ack,
  output  reg                 req,

  ///////////////////////////////////////////////
  // Cache Sync interface
  output  reg                 o_cachesync_req,
  input   wire                i_cachesync_ack
);

wire hs_cachesync;



assign hs_cachesync  = o_cachesync_req & i_cachesync_ack;

always @(posedge clk) begin
  if (rst) begin
    req <= 0;
    o_cachesync_req <= 0;
  end
  else begin
    if (start) begin
      o_cachesync_req <= 1;
    end
    else begin
      if (hs_cachesync) begin
        o_cachesync_req   <= 0;
        req <= 1;
      end
      // 清除req信号
      else if (ack) begin
        req <= 0;
      end
    end
  end
end

endmodule

// ZhengpuShi

// Writeback Interface


module ysyx_210544_wb_stage(
  input   wire                clk,
  input   wire                rst,
  input   wire                i_wb_memoryed_req,
  output  wire                o_wb_memoryed_ack,
  output  reg                 o_wb_writebacked_req,
  input   wire                i_wb_writebacked_ack,
  input   wire  [`YSYX210544_BUS_64]     i_wb_pc,
  input   wire  [`YSYX210544_BUS_32]     i_wb_inst,
  input   wire  [`YSYX210544_BUS_RIDX]   i_wb_rd,
  input   wire                i_wb_rd_wen,
  input   wire  [`YSYX210544_BUS_64]     i_wb_rd_wdata,
  input   wire                i_wb_skipcmt,
  output  wire  [`YSYX210544_BUS_64]     o_wb_pc,
  output  wire  [`YSYX210544_BUS_32]     o_wb_inst,
  output  wire  [`YSYX210544_BUS_RIDX]   o_wb_rd,
  output  wire                o_wb_rd_wen,
  output  wire  [`YSYX210544_BUS_64]     o_wb_rd_wdata,
  output  wire                o_wb_skipcmt,
  input   wire  [`YSYX210544_BUS_32]     i_wb_intrNo,
  output  reg   [`YSYX210544_BUS_32]     o_wb_intrNo
);

reg                           i_ena;    // 是否使能组合逻辑单元部件
wire                          i_disable = !i_ena;

// 保存输入信息
reg   [`YSYX210544_BUS_64]               tmp_i_wb_pc;
reg   [`YSYX210544_BUS_32]               tmp_i_wb_inst;
reg   [4 : 0]                 tmp_i_wb_rd;
reg                           tmp_i_wb_rd_wen;
reg   [`YSYX210544_BUS_64]               tmp_i_wb_rd_wdata;
reg                           tmp_i_wb_skipcmt;

wire memoryed_hs;



assign o_wb_memoryed_ack = 1'b1;
assign memoryed_hs = i_wb_memoryed_req & o_wb_memoryed_ack;

always @(posedge clk) begin
  if (rst) begin
    {
      tmp_i_wb_pc,
      tmp_i_wb_inst,
      tmp_i_wb_rd, 
      tmp_i_wb_rd_wen, 
      tmp_i_wb_rd_wdata,
      tmp_i_wb_skipcmt
    } <= 0;

    o_wb_writebacked_req    <= 0;
    i_ena                   <= 0;
    o_wb_intrNo             <= 0;
  end
  else begin
    if (memoryed_hs) begin
      tmp_i_wb_pc             <= i_wb_pc;
      tmp_i_wb_inst           <= i_wb_inst;
      tmp_i_wb_rd             <= i_wb_rd; 
      tmp_i_wb_rd_wen         <= i_wb_rd_wen;
      tmp_i_wb_rd_wdata       <= i_wb_rd_wdata;
      tmp_i_wb_skipcmt        <= i_wb_skipcmt;

      o_wb_writebacked_req  <= 1;
      i_ena                 <= 1;
      o_wb_intrNo           <= i_wb_intrNo;
    end
    else if (i_wb_writebacked_ack) begin
      o_wb_writebacked_req  <= 0;
      i_ena                 <= 0;
      o_wb_intrNo           <= 0;
    end
  end
end

assign o_wb_pc        = i_disable ? 64'd0 : tmp_i_wb_pc;
assign o_wb_inst      = i_disable ? 32'd0 : tmp_i_wb_inst;
assign o_wb_skipcmt   = i_disable ?  1'd0 : tmp_i_wb_skipcmt;
assign o_wb_rd        = i_disable ?  5'd0 : tmp_i_wb_rd;
assign o_wb_rd_wen    = i_disable ?  1'd0 : tmp_i_wb_rd_wen;
assign o_wb_rd_wdata  = i_disable ? 64'd0 : tmp_i_wb_rd_wdata;

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
wire  [`YSYX210544_BUS_64]               o_if_pc;
wire  [`YSYX210544_BUS_32]               o_if_inst;

// id_stage
// id_stage -> regfile
wire                          o_id_rs1_ren;
wire  [`YSYX210544_BUS_RIDX]             o_id_rs1;
wire                          o_id_rs2_ren;
wire  [`YSYX210544_BUS_RIDX]             o_id_rs2;
// id_stage -> exe_stage
wire  [`YSYX210544_BUS_RIDX]             o_id_rd;
wire                          o_id_rd_wen;
wire  [7 : 0]                 o_id_inst_opcode;
wire  [`YSYX210544_BUS_64]               o_id_op1;
wire  [`YSYX210544_BUS_64]               o_id_op2;
wire  [`YSYX210544_BUS_64]               o_id_op3;
wire                          o_id_skipcmt;
wire  [`YSYX210544_BUS_64]               o_id_pc;
wire  [`YSYX210544_BUS_32]               o_id_inst;

// exe_stage
// exe_stage -> mem_stage
wire  [`YSYX210544_BUS_64]               o_ex_pc;
wire  [`YSYX210544_BUS_32]               o_ex_inst;
wire                          o_ex_pc_jmp;
wire  [`YSYX210544_BUS_64]               o_ex_pc_jmpaddr;
wire  [7 : 0]                 o_ex_inst_opcode;
wire  [`YSYX210544_BUS_RIDX]             o_ex_rd;
wire                          o_ex_rd_wen;
wire  [`YSYX210544_BUS_64]               o_ex_rd_wdata;
wire  [`YSYX210544_BUS_64]               o_ex_op1;
wire  [`YSYX210544_BUS_64]               o_ex_op2;
wire  [`YSYX210544_BUS_64]               o_ex_op3;
wire                          o_ex_skipcmt;
wire  [`YSYX210544_BUS_32]               o_ex_intrNo;

// ex_stage -> csrfile
wire  [11 : 0]                o_ex_csr_addr;
wire                          o_ex_csr_ren;
wire                          o_ex_csr_wen;
wire  [`YSYX210544_BUS_64]               o_ex_csr_wdata;

// mem_stage
// mem_stage -> wb_stage
wire  [`YSYX210544_BUS_64]               o_mem_pc;
wire  [`YSYX210544_BUS_32]               o_mem_inst;
wire  [`YSYX210544_BUS_RIDX]             o_mem_rd;
wire                          o_mem_rd_wen;
wire  [`YSYX210544_BUS_64]               o_mem_rd_wdata;
wire                          o_mem_skipcmt;
wire  [`YSYX210544_BUS_32]               o_mem_intrNo;
// mem_stage -> cache
wire                          o_mem_fencei_req;
wire                          i_mem_fencei_ack;

// wb_stage
// wb_stage -> cmt_stage
wire  [`YSYX210544_BUS_64]               o_wb_pc;
wire  [`YSYX210544_BUS_32]               o_wb_inst;
wire                          o_wb_skipcmt;
wire  [`YSYX210544_BUS_32]               o_wb_intrNo;
// wb_stage -> regfile
wire  [`YSYX210544_BUS_RIDX]             o_wb_rd;
wire                          o_wb_rd_wen;
wire  [`YSYX210544_BUS_64]               o_wb_rd_wdata;

// regfile
// regfile -> id_stage
wire  [`YSYX210544_BUS_64]               o_reg_id_rs1_data;
wire  [`YSYX210544_BUS_64]               o_reg_id_rs2_data;

`ifdef YSYX210544_DIFFTEST_FLAG
// regfile -> difftest
wire  [`YSYX210544_BUS_64]               o_reg_regs[0 : 31];
`endif

// csrfile
// csrfile -> ex_stage
wire  [`YSYX210544_BUS_64]               o_csr_rdata;
// csrfile -> wb_stage
wire  [`YSYX210544_BUS_64]               o_csr_csrs_mcycle;
wire  [`YSYX210544_BUS_64]               o_csr_csrs_mstatus;
wire  [`YSYX210544_BUS_64]               o_csr_csrs_mie;
wire  [`YSYX210544_BUS_64]               o_csr_csrs_mtvec;
wire  [`YSYX210544_BUS_64]               o_csr_csrs_mscratch;
wire  [`YSYX210544_BUS_64]               o_csr_csrs_mepc;
wire  [`YSYX210544_BUS_64]               o_csr_csrs_mcause;
wire  [`YSYX210544_BUS_64]               o_csr_csrs_mip;

// clint
wire                          o_clint_mstatus_mie;
wire                          o_clint_mie_mtie;
wire                          o_clint_mtime_overflow;

// cache
wire                          o_icache_req;
wire  [63:0]                  o_icache_addr;
wire                          i_icache_ack;
wire  [31:0]                  i_icache_rdata;

wire                          o_dcache_req;
wire  [63:0]                  o_dcache_addr;
wire                          o_dcache_op;
wire  [2 :0]                  o_dcache_bytes;
wire  [63:0]                  o_dcache_wdata;
wire                          i_dcache_ack;
wire  [63:0]                  i_dcache_rdata;


`ifdef YSYX210544_DIFFTEST_FLAG

always @(posedge clk) begin
  if (o_if_inst == 32'h7b) begin
    $write("%c", o_reg_regs[10][7:0]);
    $fflush();
  end
end

`endif

ysyx_210544_cache Cache (
  .clk                        (clk                        ),
  .rst                        (rst                        ),

  // fence.i
  .i_fencei_req               (o_mem_fencei_req           ),
  .o_fencei_ack               (i_mem_fencei_ack           ),

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
  .o_if_inst                  (o_if_inst                  )
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
  .i_mem_skipcmt              (o_ex_skipcmt               ),
  .o_mem_rd                   (o_mem_rd                   ),
  .o_mem_rd_wen               (o_mem_rd_wen               ),
  .o_mem_rd_wdata             (o_mem_rd_wdata             ),
  .o_mem_pc                   (o_mem_pc                   ),
  .o_mem_inst                 (o_mem_inst                 ),
  .o_mem_skipcmt              (o_mem_skipcmt              ),
  .o_mem_clint_mtime_overflow (o_clint_mtime_overflow     ),
  .i_mem_intrNo               (o_ex_intrNo                ),
  .o_mem_intrNo               (o_mem_intrNo               ),
  .o_mem_fencei_req           (o_mem_fencei_req           ),
  .i_mem_fencei_ack           (i_mem_fencei_ack           ),

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
  .i_wb_skipcmt               (o_mem_skipcmt              ),
  .o_wb_pc                    (o_wb_pc                    ),
  .o_wb_inst                  (o_wb_inst                  ),
  .o_wb_rd                    (o_wb_rd                    ),
  .o_wb_rd_wen                (o_wb_rd_wen                ),
  .o_wb_rd_wdata              (o_wb_rd_wdata              ),
  .o_wb_skipcmt               (o_wb_skipcmt               ),
  .i_wb_intrNo                (o_mem_intrNo               ),
  .o_wb_intrNo                (o_wb_intrNo                )
);

`ifdef YSYX210544_DIFFTEST_FLAG

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
  .i_cmt_skipcmt              (o_wb_skipcmt               ),
  .i_cmt_regs                 (o_reg_regs                 ),
  .i_cmt_csrs_mstatus         (o_csr_csrs_mstatus         ),
  .i_cmt_csrs_mie             (o_csr_csrs_mie             ),
  .i_cmt_csrs_mtvec           (o_csr_csrs_mtvec           ),
  .i_cmt_csrs_mscratch        (o_csr_csrs_mscratch        ),
  .i_cmt_csrs_mepc            (o_csr_csrs_mepc            ),
  .i_cmt_csrs_mcause          (o_csr_csrs_mcause          ),

  .i_cmt_intrNo               (o_wb_intrNo                )
);

`else
    assign writebacked_ack = 1'b1;
`endif


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
  .o_rs2_data                 (o_reg_id_rs2_data          )
  
`ifdef YSYX210544_DIFFTEST_FLAG
    ,
  .o_regs                     (o_reg_regs                 )
`endif
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
  .o_csrs_mcycle              (o_csr_csrs_mcycle          ),
  .o_csrs_mstatus             (o_csr_csrs_mstatus         ),
  .o_csrs_mie                 (o_csr_csrs_mie             ),
  .o_csrs_mtvec               (o_csr_csrs_mtvec           ),
  .o_csrs_mscratch            (o_csr_csrs_mscratch        ),
  .o_csrs_mepc                (o_csr_csrs_mepc            ),
  .o_csrs_mcause              (o_csr_csrs_mcause          ),
  .o_csrs_mip                 (o_csr_csrs_mip             )
);

endmodule

// ZhengpuShi
// SoC Top Module


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

//wire _unused_ok = &{1'b0,
// io_interrupt,
// io_slave_awaddr,
// io_slave_awid,
// io_slave_awlen,
// io_slave_awsize,
// io_slave_awburst,
// io_slave_awvalid,
// io_slave_wvalid,
// io_slave_wdata,
// io_slave_wstrb,
// io_slave_wlast,
// io_slave_bready,
// io_slave_arvalid,
// io_slave_araddr,
// io_slave_arid,
// io_slave_arlen,
// io_slave_arsize,
// io_slave_arburst,
// io_slave_rready,
// axi_aw_addr_o[63:32],
// axi_ar_addr_o[63:32],
// o_user_axi_resp,
// 1'b0};

endmodule
