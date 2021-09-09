
// ZhengpuShi

// Cache Test Interface
// 模拟CPU对Cache的需求，测试写入、读取。

`include "defines.v"

module cache_test(
  input   wire                      clk,
  input   wire                      rst,
	input   wire                      i_cache_test_ack,         // 读写完成应答
  input   wire  [511 : 0]           i_cache_test_rdata,       // 读出的数据
	output  reg                       o_cache_test_req,         // 请求读写
  output  reg   [63 : 0]            o_cache_test_addr,        // 存储器地址（字节为单位），128字节对齐，低7位为0。
  output  reg                       o_cache_test_op,          // 操作类型：0读取，1写入
  output  reg   [511 : 0]           o_cache_test_wdata        // 写入的数据
);


// 测试数据
reg [511:0] reg_rand [0:3];
//                        |                 |                 |                 |                 |                 |                 |                 |
assign reg_rand[0] = 512'h8c2078a7_07e5484d_4765af4e_5226ec81_8046a887_4f66de44_24334404_8c940a7d_01dec340_02e85dec_9bb5df90_9d43c9b6_2b9b566d_5c040a78_196df530_aeb93dad;
assign reg_rand[1] = 512'h8427ded0_70f66aff_829090a9_92d822f6_d7477e69_aae19c9b_ed2767d5_8bd2ca7a_37ce9984_3039c999_a3ecf039_b77bee7d_fbba330c_20f7432f_2acd9f1b_c3a105fd;
assign reg_rand[2] = 512'h6c4ea3ae_19c5e79f_1f8c4ac4_d007725a_00103055_127d5e14_f27d58b6_664054f8_946dd2c7_cd1c01e0_b3b6f421_97d34c0f_ab004018_8966ba42_5d555592_2928817c;
assign reg_rand[3] = 512'h1d8b9dca_096d5800_7ecd5ced_25bf4f2b_2fd2f12a_caefb888_4aecb935_bf9b0292_7a5b474b_92e91310_e7fe4114_767f4695_d5fa24cf_90ea673b_bb20a132_d0aa6fed;
reg [1:0] reg_rand_idx;

// 指示读出的数据是否与写入的一致
wire equal_flag = o_cache_test_wdata == i_cache_test_rdata;


// 演示：延时；写入64字节；延时；读取64字节；。。。
reg [`BUS_64] cnt;
wire cache_hs = o_cache_test_req & i_cache_test_ack;
wire cache_hs_read = cache_hs & (o_cache_test_op == `REQ_READ);
wire cache_hs_write = cache_hs & (o_cache_test_op == `REQ_WRITE);

always @(posedge clk) begin
  if (rst) begin
    cnt <= 0;
    o_cache_test_req      <= 0;
    o_cache_test_addr     <= `PC_START;
    o_cache_test_op       <= `REQ_WRITE;
    o_cache_test_wdata    <= 0;
  end
  else begin
    // 写入完毕
    if (cache_hs_write) begin
      o_cache_test_req      <= 0;
      cnt                   <= 0;
      o_cache_test_op       <= `REQ_READ;
    end
    // 读取完毕
    else if (cache_hs_read) begin
      o_cache_test_req      <= 0;
      cnt                   <= 0;
      o_cache_test_op       <= `REQ_WRITE;
      reg_rand_idx          <= reg_rand_idx + 1;              // 数据偏移
      o_cache_test_addr     <= o_cache_test_addr + 64'h40;    // 地址偏移
    end
    else begin
      // 计数1000后发出请求
      cnt <= cnt + 1;
      if (cnt > 1000) begin
        o_cache_test_req <= 1;
        // 准备要写入的数据
        if (o_cache_test_op == `REQ_WRITE) begin
          o_cache_test_wdata    <= reg_rand[reg_rand_idx];
        end
      end
    end
  end
end

endmodule
