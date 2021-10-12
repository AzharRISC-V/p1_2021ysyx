
// AXI Read & Write Unit

`include "defines.v"

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
    output reg                          axi_w_valid_o,
    output reg  [63:0]                  axi_w_data_o,
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
wire [`AXI_ID_WIDTH-1:0] axi_id;
wire rw_ready_nxt;
wire rw_ready_en;
reg [1:0] rw_resp;
wire [1:0] rw_resp_nxt;
wire resp_en;
wire [2:0] axi_addr_offset_bytes;       // 输入地址的 字节偏移量(0~7)
wire [5:0] axi_addr_offset_bits;        // 输入地址的   位偏移量(0~56)
reg  [7:0] axi_w_strb_orig;

wire size_b;
wire size_h;
wire size_w;
wire size_d;
reg  [63:0] mask_rdata;
wire [5:0] aligned_offset;                      // 移位的bit数。0~7 转换为 0~56
wire [63:0] axi_r_data_masked_unaligned;        // 已掩码，已移位后的数据



assign w_trans    = user_req_i == `REQ_WRITE;
assign r_trans    = user_req_i == `REQ_READ;
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
assign axi_id           = {`AXI_ID_WIDTH{1'b0}};

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
assign axi_aw_burst_o   = `AXI_BURST_TYPE_INCR;

// Write data channel signals

// 由于 w_valid 使能之时需要同时送出 wdata，所以改用时序逻辑
always @(posedge clock) begin
    if (reset) begin
        axi_w_valid_o <= 1'b0;
    end
    else begin
        if (w_state_write) begin
            if (!axi_w_valid_o) begin
                axi_w_valid_o <= 1'b1;
            end
        end
        else if (w_state_resp) begin
            axi_w_valid_o <= 1'b0;
        end
    end
end

assign axi_w_last_o     = w_hs & (len == axi_len);

// 仅根据size生成的wstrb，需要移位后使用，是吗？？

always @(*) begin
    if (reset) begin
        axi_w_strb_orig = 8'd0;
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

assign axi_addr_offset_bytes  = user_addr_i[2:0];
assign axi_addr_offset_bits   = {3'b0, axi_addr_offset_bytes} << 2'd3;

// 移位生成最终的 w_strb。wdata 和 wstrb 都需要移位
// assign axi_w_strb_o     = 8'b1111_1111;     // 每个bit代表一个字节是否要写入
assign axi_w_strb_o = w_valid ? (axi_w_strb_orig << axi_addr_offset_bytes) : 8'd0;

// Wreite response channel signals
assign axi_b_ready_o    = w_state_resp;

always @(posedge clock) begin
    if (reset) begin
        axi_w_data_o <= 0;
    end
    else begin
        // sent first wdata
        if (w_state_write && (!axi_w_valid_o)) begin
            axi_w_data_o  <= user_wdata_i[63:0] << axi_addr_offset_bits;
        end
        else begin
            // sent remain wdata
            if (w_hs) begin
                if (axi_len > 0) begin
                    case (len)
                        8'd0: axi_w_data_o <= user_wdata_i[64*1 +:64] << axi_addr_offset_bits;
                        8'd1: axi_w_data_o <= user_wdata_i[64*2 +:64] << axi_addr_offset_bits;
                        8'd2: axi_w_data_o <= user_wdata_i[64*3 +:64] << axi_addr_offset_bits;
                        8'd3: axi_w_data_o <= user_wdata_i[64*4 +:64] << axi_addr_offset_bits;
                        8'd4: axi_w_data_o <= user_wdata_i[64*5 +:64] << axi_addr_offset_bits;
                        8'd5: axi_w_data_o <= user_wdata_i[64*6 +:64] << axi_addr_offset_bits;
                        8'd6: axi_w_data_o <= user_wdata_i[64*7 +:64] << axi_addr_offset_bits;
                        default: ;
                    endcase
                end
            end
        end
    end
 end


// ------------------Read Transaction------------------

// Read address channel signals
assign axi_ar_valid_o   = r_state_addr & user_valid_i;
assign axi_ar_addr_o    = r_trans ? axi_addr : 64'd0;
assign axi_ar_id_o      = r_trans ? axi_id : 4'd0;
assign axi_ar_len_o     = r_trans ? axi_len : 8'd0;
assign axi_ar_size_o    = r_trans ? axi_size : 3'd0;
assign axi_ar_burst_o   = `AXI_BURST_TYPE_INCR;

// Read data channel signals
assign axi_r_ready_o    = r_state_read;

// User Data Size
assign size_b             = user_size_i == `SIZE_B;
assign size_h             = user_size_i == `SIZE_H;
assign size_w             = user_size_i == `SIZE_W;
assign size_d             = user_size_i == `SIZE_D;

// Read data mask
// assign mask_rdata   = (({64{size_b}} & {{64- 8{1'b0}},  8'hff}) 
//                      | ({64{size_h}} & {{64-16{1'b0}}, 16'hffff})
//                      | ({64{size_w}} & {{64-32{1'b0}}, 32'hffffffff})
//                      | ({64{size_d}} & {{64-64{1'b0}}, 64'hffffffff_ffffffff})
//                       );
always @(*) begin
    if (size_d)         mask_rdata = 64'hffffffff_ffffffff;
    else if (size_w)    mask_rdata = 64'h00000000_ffffffff;
    else if (size_h)    mask_rdata = 64'h00000000_0000ffff;
    else if (size_b)    mask_rdata = 64'h00000000_000000ff;
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
