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

    input                               io_memAXI_0_aw_ready,
    output                              io_memAXI_0_aw_valid,
    output [63:0]                       io_memAXI_0_aw_bits_addr,
    output [2:0]                        io_memAXI_0_aw_bits_prot,
    output [`AXI_ID_WIDTH-1:0]          io_memAXI_0_aw_bits_id,
    output                              io_memAXI_0_aw_bits_user,
    output [7:0]                        io_memAXI_0_aw_bits_len,
    output [2:0]                        io_memAXI_0_aw_bits_size,
    output [1:0]                        io_memAXI_0_aw_bits_burst,
    output                              io_memAXI_0_aw_bits_lock,
    output [3:0]                        io_memAXI_0_aw_bits_cache,
    output [3:0]                        io_memAXI_0_aw_bits_qos,
    
    input                               io_memAXI_0_w_ready,
    output                              io_memAXI_0_w_valid,
    output [63:0]                       io_memAXI_0_w_bits_data         [3:0],
    output [7:0]                        io_memAXI_0_w_bits_strb,
    output                              io_memAXI_0_w_bits_last,
    
    output                              io_memAXI_0_b_ready,
    input                               io_memAXI_0_b_valid,
    input  [1:0]                        io_memAXI_0_b_bits_resp,
    input  [`AXI_ID_WIDTH-1:0]          io_memAXI_0_b_bits_id,
    input                               io_memAXI_0_b_bits_user,

    input                               io_memAXI_0_ar_ready,
    output                              io_memAXI_0_ar_valid,
    output [63:0]                       io_memAXI_0_ar_bits_addr,
    output [2:0]                        io_memAXI_0_ar_bits_prot,
    output [`AXI_ID_WIDTH-1:0]          io_memAXI_0_ar_bits_id,
    output                              io_memAXI_0_ar_bits_user,
    output [7:0]                        io_memAXI_0_ar_bits_len,
    output [2:0]                        io_memAXI_0_ar_bits_size,
    output [1:0]                        io_memAXI_0_ar_bits_burst,
    output                              io_memAXI_0_ar_bits_lock,
    output [3:0]                        io_memAXI_0_ar_bits_cache,
    output [3:0]                        io_memAXI_0_ar_bits_qos,
    
    output                              io_memAXI_0_r_ready,
    input                               io_memAXI_0_r_valid,
    input  [1:0]                        io_memAXI_0_r_bits_resp,
    input  [63:0]                       io_memAXI_0_r_bits_data         [3:0],
    input                               io_memAXI_0_r_bits_last,
    input  [`AXI_ID_WIDTH-1:0]          io_memAXI_0_r_bits_id,
    input                               io_memAXI_0_r_bits_user
);

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

    .axi_aw_ready_i                 (io_memAXI_0_aw_ready),
    .axi_aw_valid_o                 (io_memAXI_0_aw_valid),
    .axi_aw_addr_o                  (io_memAXI_0_aw_bits_addr),
    .axi_aw_id_o                    (io_memAXI_0_aw_bits_id),
    .axi_aw_len_o                   (io_memAXI_0_aw_bits_len),
    .axi_aw_size_o                  (io_memAXI_0_aw_bits_size),
    .axi_aw_burst_o                 (io_memAXI_0_aw_bits_burst),
    .axi_w_ready_i                  (io_memAXI_0_w_ready),
    .axi_w_valid_o                  (io_memAXI_0_w_valid),
    .axi_w_data_o                   (io_memAXI_0_w_bits_data[0]),
    .axi_w_strb_o                   (io_memAXI_0_w_bits_strb),
    .axi_w_last_o                   (io_memAXI_0_w_bits_last),
    .axi_b_ready_o                  (io_memAXI_0_b_ready),
    .axi_b_valid_i                  (io_memAXI_0_b_valid),
    .axi_b_resp_i                   (io_memAXI_0_b_bits_resp),
    .axi_b_id_i                     (io_memAXI_0_b_bits_id),
    .axi_ar_ready_i                 (io_memAXI_0_ar_ready),
    .axi_ar_valid_o                 (io_memAXI_0_ar_valid),
    .axi_ar_addr_o                  (io_memAXI_0_ar_bits_addr),
    .axi_ar_id_o                    (io_memAXI_0_ar_bits_id),
    .axi_ar_len_o                   (io_memAXI_0_ar_bits_len),
    .axi_ar_size_o                  (io_memAXI_0_ar_bits_size),
    .axi_ar_burst_o                 (io_memAXI_0_ar_bits_burst),
    .axi_r_ready_o                  (io_memAXI_0_r_ready),
    .axi_r_valid_i                  (io_memAXI_0_r_valid),
    .axi_r_resp_i                   (io_memAXI_0_r_bits_resp),
    .axi_r_data_i                   (io_memAXI_0_r_bits_data[0]),
    .axi_r_last_i                   (io_memAXI_0_r_bits_last),
    .axi_r_id_i                     (io_memAXI_0_r_bits_id)
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

assign io_uart_out_valid = 0;
assign io_uart_out_ch = 0;
assign io_uart_in_valid = 0;

assign io_memAXI_0_aw_bits_prot = 0;
assign io_memAXI_0_aw_bits_user = 0;
assign io_memAXI_0_aw_bits_lock = 0;
assign io_memAXI_0_aw_bits_cache = 0;
assign io_memAXI_0_aw_bits_qos = 0;
assign io_memAXI_0_ar_bits_prot = 0;
assign io_memAXI_0_ar_bits_user = 0;
assign io_memAXI_0_ar_bits_lock = 0;
assign io_memAXI_0_ar_bits_cache = 0;
assign io_memAXI_0_ar_bits_qos = 0;


wire _unused_ok = &{1'b0,
  io_logCtrl_log_begin,
  io_logCtrl_log_end,
  io_logCtrl_log_level,
  io_perfInfo_clean,
  io_perfInfo_dump,
  io_uart_in_ch,
  io_memAXI_0_b_bits_user,
  io_memAXI_0_r_bits_user,
  o_user_axi_resp,
  1'b0};

endmodule
