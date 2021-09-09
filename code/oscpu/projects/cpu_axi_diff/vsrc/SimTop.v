
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

assign aw_ready                                 = `AXI_TOP_INTERFACE(aw_ready);
assign `AXI_TOP_INTERFACE(aw_valid)             = aw_valid;
assign `AXI_TOP_INTERFACE(aw_bits_addr)         = aw_addr;
assign `AXI_TOP_INTERFACE(aw_bits_prot)         = aw_prot;
assign `AXI_TOP_INTERFACE(aw_bits_id)           = aw_id;
assign `AXI_TOP_INTERFACE(aw_bits_user)         = aw_user;
assign `AXI_TOP_INTERFACE(aw_bits_len)          = aw_len;
assign `AXI_TOP_INTERFACE(aw_bits_size)         = aw_size;
assign `AXI_TOP_INTERFACE(aw_bits_burst)        = aw_burst;
assign `AXI_TOP_INTERFACE(aw_bits_lock)         = aw_lock;
assign `AXI_TOP_INTERFACE(aw_bits_cache)        = aw_cache;
assign `AXI_TOP_INTERFACE(aw_bits_qos)          = aw_qos;

assign w_ready                                  = `AXI_TOP_INTERFACE(w_ready);
assign `AXI_TOP_INTERFACE(w_valid)              = w_valid;
assign `AXI_TOP_INTERFACE(w_bits_data)[0]       = w_data;
assign `AXI_TOP_INTERFACE(w_bits_strb)          = w_strb;
assign `AXI_TOP_INTERFACE(w_bits_last)          = w_last;

assign `AXI_TOP_INTERFACE(b_ready)              = b_ready;
assign b_valid                                  = `AXI_TOP_INTERFACE(b_valid);
assign b_resp                                   = `AXI_TOP_INTERFACE(b_bits_resp);
assign b_id                                     = `AXI_TOP_INTERFACE(b_bits_id);
assign b_user                                   = `AXI_TOP_INTERFACE(b_bits_user);

axi_rw u_axi_rw (
    .clock                          (clock),
    .reset                          (reset),

    .user_valid_i                   (user_axi_valid),
    .user_ready_o                   (user_axi_ready),
    .user_blks_i                    (user_axi_blks),
    .user_req_i                     (user_axi_op),
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


// ========== CACHE访问接口示例 =================

// ====== cache_rw 主机端，请求传输数据 ===============
wire                          i_cache_test_ack;         // 应答
wire  [511 : 0]               i_cache_test_rdata;       // 已读出的数据
reg                           o_cache_test_req;         // 请求
reg   [63 : 0]                o_cache_test_addr;        // 存储器地址（字节为单位），64字节对齐，低6位为0。
reg                           o_cache_test_op;          // 操作类型：0读取，1写入
reg   [511 : 0]               o_cache_test_wdata;       // 要写入的数据

cache_test Cache_test(
  .rst                        (reset                      ),
  .clk                        (clock                      ),
  .i_cache_test_ack           (i_cache_test_ack           ),
  .i_cache_test_rdata         (i_cache_test_rdata         ),
  .o_cache_test_req           (o_cache_test_req           ),
  .o_cache_test_addr          (o_cache_test_addr          ),
  .o_cache_test_op            (o_cache_test_op            ),
  .o_cache_test_wdata         (o_cache_test_wdata         ) 
);

// ====== cache_rw 从机端，适配AXI接口 ===============
wire [511:0]                  user_axi_rdata;
wire [511:0]                  user_axi_wdata;
wire                          user_axi_op;
wire                          user_axi_valid;
wire                          user_axi_ready;
wire [63:0]                   user_axi_addr;
wire [1:0]                    user_axi_size;
wire [1:0]                    user_axi_resp;
wire [7:0]                    user_axi_blks;

cache_rw Cache_rw(
  .clk                        (clock                      ),
  .rst                        (reset                      ),
	.i_cache_rw_req             (o_cache_test_req           ),
	.i_cache_rw_addr            (o_cache_test_addr          ),
	.i_cache_rw_op              (o_cache_test_op            ),
	.i_cache_rw_wdata           (o_cache_test_wdata         ),
	.o_cache_rw_rdata           (i_cache_test_rdata         ),
	.o_cache_rw_ack             (i_cache_test_ack           ),

  .o_cache_axi_op             (user_axi_op                ),
  .i_cache_axi_ready          (user_axi_ready             ),
  .i_cache_axi_rdata          (user_axi_rdata             ),
  .o_cache_axi_valid          (user_axi_valid             ),
  .o_cache_axi_wdata          (user_axi_wdata             ),
  .o_cache_axi_addr           (user_axi_addr              ),
  .o_cache_axi_size           (user_axi_size              ),
  .o_cache_axi_blks           (user_axi_blks              )
);

cpu u_cpu(
    .clk                            (clock),
    .rst                            (reset),

    .if_valid                       ( ),//cache_axi_valid),
    .if_ready                       ( ),
    .if_rdata                       ( ),
    .if_addr                        ( ),//cache_axi_addr),
    .if_size                        ( ),
    .if_resp                        ( )
);


endmodule