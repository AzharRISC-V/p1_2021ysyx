
// ZhengpuShi

// Fetch Unit

`include "defines.v"

module ifU(
  input   wire                i_ena,
  input   wire                clk,
  input   wire                rst,

  /////////////////////////////////////////////////////////
  // AXI interface for Fetch
	input                       i_axi_ready,
  input         [`BUS_64]     i_axi_data_read,
  input         [1:0]         i_axi_resp,
	output reg                  o_axi_valid,
  output reg    [`BUS_64]     o_axi_addr,
  output        [1:0]         o_axi_size,
  
  /////////////////////////////////////////////////////////
  input   wire                i_pc_jmp,
  input   wire  [`BUS_64]     i_pc_jmpaddr,
  output  reg   [`BUS_64]     o_pc,
  output  reg   [`BUS_64]     o_pc_pred,            // 预测的下一个PC
  output  reg   [`BUS_32]     o_inst,
  output                      o_fetched,            // 取到指令的通知
  output  reg                 o_nocmt               // 由于冲刷流水线而不提交这条指令
);


wire i_disable = !i_ena;

assign o_axi_valid = 1'b1;

wire handshake_done = o_axi_valid & i_axi_ready;

// fetch an instruction
always @( posedge clk ) begin
  if (rst) begin
    o_axi_addr              <= `PC_START;
    o_pc                    <= 0;
    o_pc_pred               <= 0;
    o_nocmt                 <= 0;
    o_fetched               <= 0;
  end
  else begin
    if (handshake_done) begin
      o_axi_addr              <= o_axi_addr + 4;
      o_pc                    <= o_axi_addr;
      o_pc_pred               <= o_axi_addr + 4;
      o_inst                  <= i_axi_data_read[31:0];
      o_nocmt                 <= 0;
      o_fetched               <= 1;
    end
    // 冲刷流水线：执行一条不需要提交的nop指令
    else if (flush_en) begin
      o_axi_addr              <= i_pc_jmpaddr;
      o_pc                    <= i_pc_jmpaddr;
      o_pc_pred               <= i_pc_jmpaddr + 4;
      o_inst                  <= `INST_NOP;
      o_nocmt                 <= 1;
      o_fetched               <= 1;
    end
    else begin
      o_pc                    <= 0;
      o_pc_pred               <= 0;
      o_inst                  <= 0;
      o_nocmt                 <= 0;
      o_fetched               <= 0;
    end
  end
end

// 顺序计算得出的pc值，用于同jump时的地址对比，若不同则需要冲刷流水线
assign o_axi_size = `SIZE_W;

// 是否冲刷流水线
wire      flush_en;
assign flush_en = i_pc_jmp ? (o_pc_pred != i_pc_jmpaddr ? 1 : 0) : 0;

endmodule
