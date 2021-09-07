
// ZhengpuShi

// Fetch Unit

`include "defines.v"

module ifU(
  input   wire                i_clk,
  input   wire                i_rst,

  /////////////////////////////////////////////////////////
  // AXI interface for Fetch
	input                       i_axi_ready,
  input         [63:0]        i_axi_data_read,
  input         [1:0]         i_axi_resp,
	output reg                  o_axi_valid,
  output reg    [63:0]        o_axi_addr,
  output        [1:0]         o_axi_size,
  
  /////////////////////////////////////////////////////////
  input   wire                i_pc_jmp,
  input   wire  [`BUS_64]     i_pc_jmpaddr,
  output  reg   [`BUS_64]     o_pc_old,
  output  reg   [`BUS_64]     o_pc,
  output  wire  [`BUS_64]     o_pc_pred,    // 预测的下一个PC
  output  reg   [`BUS_32]     o_inst,
  output                      fetched_pulse     // 取到指令的通知
);

assign o_axi_valid = 1'b1;

wire handshake_done = o_axi_valid & i_axi_ready;

// fetch an instruction
always @( posedge i_clk ) begin
  if (i_rst) begin
    // pc_old    <= 0;
    o_pc                      <= 0;
    o_axi_addr                <= `PC_START;
  end
  else begin
    if (handshake_done) begin
      o_inst                  <= i_axi_data_read[31:0];
      o_pc                    <= o_axi_addr;
      o_axi_addr              <= o_axi_addr + 4;
    end
  end
end

assign fetched_pulse = handshake_done;

assign o_pc_pred = o_pc + 4;
assign o_axi_size = `SIZE_W;

endmodule
