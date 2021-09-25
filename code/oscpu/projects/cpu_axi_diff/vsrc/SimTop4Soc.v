`include "defines.v"

module SimTop4Soc(
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
wire [1:0]                    o_user_axi_size;
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
