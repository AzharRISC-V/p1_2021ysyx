
`include "defines.v"
`define AXI_TOP_INTERFACE(name) io_memAXI_0_``name

module SimTop(
    input                               clock,
    input                               reset,

    input  [63:0]                       io_logCtrl_log_begin,
    input  [63:0]                       io_logCtrl_log_end,
    input  [63:0]                       io_logCtrl_log_level,
    input                               io_perfInfo_clean,
    input                               io_perfInfo_dump,

    output                              io_uart_out_valid,
    output [7:0]                        io_uart_out_ch,
    output                              io_uart_in_valid,
    input  [7:0]                        io_uart_in_ch,

    input                               `AXI_TOP_INTERFACE(aw_ready),
    output                              `AXI_TOP_INTERFACE(aw_valid),
    output [`AXI_ADDR_WIDTH-1:0]        `AXI_TOP_INTERFACE(aw_bits_addr),
    output [2:0]                        `AXI_TOP_INTERFACE(aw_bits_prot),
    output [`AXI_ID_WIDTH-1:0]          `AXI_TOP_INTERFACE(aw_bits_id),
    output [`AXI_USER_WIDTH-1:0]        `AXI_TOP_INTERFACE(aw_bits_user),
    output [7:0]                        `AXI_TOP_INTERFACE(aw_bits_len),
    output [2:0]                        `AXI_TOP_INTERFACE(aw_bits_size),
    output [1:0]                        `AXI_TOP_INTERFACE(aw_bits_burst),
    output                              `AXI_TOP_INTERFACE(aw_bits_lock),
    output [3:0]                        `AXI_TOP_INTERFACE(aw_bits_cache),
    output [3:0]                        `AXI_TOP_INTERFACE(aw_bits_qos),
    
    input                               `AXI_TOP_INTERFACE(w_ready),
    output                              `AXI_TOP_INTERFACE(w_valid),
    output [`AXI_DATA_WIDTH-1:0]        `AXI_TOP_INTERFACE(w_bits_data)         [3:0],
    output [`AXI_DATA_WIDTH/8-1:0]      `AXI_TOP_INTERFACE(w_bits_strb),
    output                              `AXI_TOP_INTERFACE(w_bits_last),
    
    output                              `AXI_TOP_INTERFACE(b_ready),
    input                               `AXI_TOP_INTERFACE(b_valid),
    input  [1:0]                        `AXI_TOP_INTERFACE(b_bits_resp),
    input  [`AXI_ID_WIDTH-1:0]          `AXI_TOP_INTERFACE(b_bits_id),
    input  [`AXI_USER_WIDTH-1:0]        `AXI_TOP_INTERFACE(b_bits_user),

    input                               `AXI_TOP_INTERFACE(ar_ready),
    output                              `AXI_TOP_INTERFACE(ar_valid),
    output [`AXI_ADDR_WIDTH-1:0]        `AXI_TOP_INTERFACE(ar_bits_addr),
    output [2:0]                        `AXI_TOP_INTERFACE(ar_bits_prot),
    output [`AXI_ID_WIDTH-1:0]          `AXI_TOP_INTERFACE(ar_bits_id),
    output [`AXI_USER_WIDTH-1:0]        `AXI_TOP_INTERFACE(ar_bits_user),
    output [7:0]                        `AXI_TOP_INTERFACE(ar_bits_len),
    output [2:0]                        `AXI_TOP_INTERFACE(ar_bits_size),
    output [1:0]                        `AXI_TOP_INTERFACE(ar_bits_burst),
    output                              `AXI_TOP_INTERFACE(ar_bits_lock),
    output [3:0]                        `AXI_TOP_INTERFACE(ar_bits_cache),
    output [3:0]                        `AXI_TOP_INTERFACE(ar_bits_qos),
    
    output                              `AXI_TOP_INTERFACE(r_ready),
    input                               `AXI_TOP_INTERFACE(r_valid),
    input  [1:0]                        `AXI_TOP_INTERFACE(r_bits_resp),
    input  [`AXI_DATA_WIDTH-1:0]        `AXI_TOP_INTERFACE(r_bits_data)         [3:0],
    input                               `AXI_TOP_INTERFACE(r_bits_last),
    input  [`AXI_ID_WIDTH-1:0]          `AXI_TOP_INTERFACE(r_bits_id),
    input  [`AXI_USER_WIDTH-1:0]        `AXI_TOP_INTERFACE(r_bits_user)
);

    wire aw_ready;
    wire aw_valid;
    wire [`AXI_ADDR_WIDTH-1:0] aw_addr;
    wire [2:0] aw_prot;
    wire [`AXI_ID_WIDTH-1:0] aw_id;
    wire [`AXI_USER_WIDTH-1:0] aw_user;
    wire [7:0] aw_len;
    wire [2:0] aw_size;
    wire [1:0] aw_burst;
    wire aw_lock;
    wire [3:0] aw_cache;
    wire [3:0] aw_qos;
    wire [3:0] aw_region;

    wire w_ready;
    wire w_valid;
    wire [`AXI_DATA_WIDTH-1:0] w_data;
    wire [`AXI_DATA_WIDTH/8-1:0] w_strb;
    wire w_last;
    wire [`AXI_USER_WIDTH-1:0] w_user;
    
    wire b_ready;
    wire b_valid;
    wire [1:0] b_resp;
    wire [`AXI_ID_WIDTH-1:0] b_id;
    wire [`AXI_USER_WIDTH-1:0] b_user;

    wire ar_ready;
    wire ar_valid;
    wire [`AXI_ADDR_WIDTH-1:0] ar_addr;
    wire [2:0] ar_prot;
    wire [`AXI_ID_WIDTH-1:0] ar_id;
    wire [`AXI_USER_WIDTH-1:0] ar_user;
    wire [7:0] ar_len;
    wire [2:0] ar_size;
    wire [1:0] ar_burst;
    wire ar_lock;
    wire [3:0] ar_cache;
    wire [3:0] ar_qos;
    wire [3:0] ar_region;
    
    wire r_ready;
    wire r_valid;
    wire [1:0] r_resp;
    wire [`AXI_DATA_WIDTH-1:0] r_data;
    wire r_last;
    wire [`AXI_ID_WIDTH-1:0] r_id;
    wire [`AXI_USER_WIDTH-1:0] r_user;

    assign ar_ready                                 = `AXI_TOP_INTERFACE(ar_ready);
    assign `AXI_TOP_INTERFACE(ar_valid)             = ar_valid;
    assign `AXI_TOP_INTERFACE(ar_bits_addr)         = ar_addr;
    assign `AXI_TOP_INTERFACE(ar_bits_prot)         = ar_prot;
    assign `AXI_TOP_INTERFACE(ar_bits_id)           = ar_id;
    assign `AXI_TOP_INTERFACE(ar_bits_user)         = ar_user;
    assign `AXI_TOP_INTERFACE(ar_bits_len)          = ar_len;
    assign `AXI_TOP_INTERFACE(ar_bits_size)         = ar_size;
    assign `AXI_TOP_INTERFACE(ar_bits_burst)        = ar_burst;
    assign `AXI_TOP_INTERFACE(ar_bits_lock)         = ar_lock;
    assign `AXI_TOP_INTERFACE(ar_bits_cache)        = ar_cache;
    assign `AXI_TOP_INTERFACE(ar_bits_qos)          = ar_qos;
    
    assign `AXI_TOP_INTERFACE(r_ready)              = r_ready;
    assign r_valid                                  = `AXI_TOP_INTERFACE(r_valid);
    assign r_resp                                   = `AXI_TOP_INTERFACE(r_bits_resp);
    assign r_data                                   = `AXI_TOP_INTERFACE(r_bits_data)[0];
    assign r_last                                   = `AXI_TOP_INTERFACE(r_bits_last);
    assign r_id                                     = `AXI_TOP_INTERFACE(r_bits_id);
    assign r_user                                   = `AXI_TOP_INTERFACE(r_bits_user);

    axi_rw u_axi_rw (
        .clock                          (clock),
        .reset                          (reset),

        .user_valid_i                   (user_axi_valid),
        .user_ready_o                   (user_axi_ready),
        .user_blks_i                    (user_axi_blks),
        .user_req_i                     (user_axi_req),
        .user_rdata_o                   (user_axi_rdata),
        .user_wdata_i                   (user_axi_wdata),
        .user_addr_i                    (user_axi_addr),
        .user_size_i                    (user_axi_size),
        .user_resp_o                    (user_axi_resp),

        .axi_aw_ready_i                 (aw_ready),
        .axi_aw_valid_o                 (aw_valid),
        .axi_aw_addr_o                  (aw_addr),
        .axi_aw_prot_o                  (aw_prot),
        .axi_aw_id_o                    (aw_id),
        .axi_aw_user_o                  (aw_user),
        .axi_aw_len_o                   (aw_len),
        .axi_aw_size_o                  (aw_size),
        .axi_aw_burst_o                 (aw_burst),
        .axi_aw_lock_o                  (aw_lock),
        .axi_aw_cache_o                 (aw_cache),
        .axi_aw_qos_o                   (aw_qos),
        .axi_aw_region_o                (aw_region),

        .axi_w_ready_i                  (w_ready),
        .axi_w_valid_o                  (w_valid),
        .axi_w_data_o                   (w_data),
        .axi_w_strb_o                   (w_strb),
        .axi_w_last_o                   (w_last),
        .axi_w_user_o                   (w_user),
        
        .axi_b_ready_o                  (b_ready),
        .axi_b_valid_i                  (b_valid),
        .axi_b_resp_i                   (b_resp),
        .axi_b_id_i                     (b_id),
        .axi_b_user_i                   (b_user),

        .axi_ar_ready_i                 (ar_ready),
        .axi_ar_valid_o                 (ar_valid),
        .axi_ar_addr_o                  (ar_addr),
        .axi_ar_prot_o                  (ar_prot),
        .axi_ar_id_o                    (ar_id),
        .axi_ar_user_o                  (ar_user),
        .axi_ar_len_o                   (ar_len),
        .axi_ar_size_o                  (ar_size),
        .axi_ar_burst_o                 (ar_burst),
        .axi_ar_lock_o                  (ar_lock),
        .axi_ar_cache_o                 (ar_cache),
        .axi_ar_qos_o                   (ar_qos),
        .axi_ar_region_o                (ar_region),
        
        .axi_r_ready_o                  (r_ready),
        .axi_r_valid_i                  (r_valid),
        .axi_r_resp_i                   (r_resp),
        .axi_r_data_i                   (r_data),
        .axi_r_last_i                   (r_last),
        .axi_r_id_i                     (r_id),
        .axi_r_user_i                   (r_user)
    );

wire [7:0] user_axi_blks = 7;
wire axi_wen;
wire user_axi_valid;
wire user_axi_ready;
wire user_axi_req = `REQ_READ;
wire [511:0] user_axi_rdata;
reg  [511:0] user_axi_wdata;
wire [63:0] user_axi_addr;
wire [1:0] user_axi_size;
wire [1:0] user_axi_resp;

    
// 演示，每隔一段时间，取出32字节的数据
reg [`BUS_64] cnt;
reg cache_rw_req;
wire cache_rw_ack;
reg read_write;   // 0:read, 1:write
wire cache_rw_hs = cache_rw_req & cache_rw_ack;
reg [`BUS_64] cache_addr;

reg [511:0] reg_rand [0:3];
assign reg_rand[0] = 512'h8c2078a707e5484d4765af4e5226ec818046a8874f66de44243344048c940a7d01dec34002e85dec9bb5df909d43c9b62b9b566d5c040a78196df530aeb93dad;
assign reg_rand[1] = 512'h8427ded070f66aff829090a992d822f6d7477e69aae19c9bed2767d58bd2ca7a37ce99843039c999a3ecf039b77bee7dfbba330c20f7432f2acd9f1bc3a105fd;
assign reg_rand[2] = 512'h6c4ea3ae19c5e79f1f8c4ac4d007725a00103055127d5e14f27d58b6664054f8946dd2c7cd1c01e0b3b6f42197d34c0fab0040188966ba425d5555922928817c;
assign reg_rand[3] = 512'h1d8b9dca096d58007ecd5ced25bf4f2b2fd2f12acaefb8884aecb935bf9b02927a5b474b92e91310e7fe4114767f4695d5fa24cf90ea673bbb20a132d0aa6fed;
reg [1:0] reg_rand_idx;

always @(posedge clock) begin
  if (reset) begin
    cnt <= 0;
    cache_rw_req <= 0;
    cache_addr  <= `PC_START;
    read_write  <= 1;
  end
  else begin
    // 收到ack，则撤销请求，并且计时器清零
    if (cache_rw_hs) begin
      cache_rw_req <= 0;
      cnt <= 0;
      cache_addr  <= cache_addr + 64'h40;
      user_axi_wdata <= 0;
      reg_rand_idx <= 0;
      // 切换到下一组数据
      reg_rand_idx <= reg_rand_idx + 1;
    end
    else begin
      // 计数1000后发出请求
      cnt <= cnt + 1;
      if (cnt > 1000) begin
        if (read_write) begin
          // 准备数据
          user_axi_wdata <= reg_rand[reg_rand_idx];
        end
        cache_rw_req <= 1;
      end
    end
  end
end

wire cache_rw_ren;
wire cache_rw_wen;
wire [511:0] cache_rw_rdata;
wire [511:0] cache_rw_wdata;

cache_rw Cache_rw(
  .clk                        (clock                      ),
  .rst                        (reset                      ),
	.i_cache_rw_req             (cache_rw_req               ),
	.o_cache_rw_ack             (cache_rw_ack               ),
	.i_cache_rw_addr            (cache_addr                 ),
	.o_cache_rw_ren             (cache_rw_ren               ),
	.o_cache_rw_wen             (cache_rw_wen               ),
	.o_cache_rw_wdata           (cache_rw_wdata             ),
	.o_cache_rw_rdata           (cache_rw_rdata             ),

  .i_cache_axi_wen            (axi_wen               ),
  .i_cache_axi_ready          (user_axi_ready             ),
  .i_cache_axi_rdata          (user_axi_rdata              ),
  .i_cache_axi_resp           (user_axi_resp              ),
  .o_cache_axi_valid          (user_axi_valid             ),
  .o_cache_axi_addr           (user_axi_addr              ),
  .o_cache_axi_size           (user_axi_size              )
);


cpu u_cpu(
    .clk                            (clock),
    .rst                            (reset),

    .if_valid                       ( ),//user_axi_valid),
    .if_ready                       ( ),
    .if_rdata                       ( ),
    .if_addr                        ( ),//user_axi_addr),
    .if_size                        ( ),
    .if_resp                        ( )
);


endmodule