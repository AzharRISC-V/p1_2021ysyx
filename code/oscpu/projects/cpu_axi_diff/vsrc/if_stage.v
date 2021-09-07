
// ZhengpuShi

// Instruction Fetch Interface

`include "defines.v"

module if_stage(
  input   wire                  clk,
  input   wire                  rst,

  /////////////////////////////////////////////////////////
  // AXI interface for Fetch
	output reg                    if_valid,
	input                         if_ready,
  input         [63:0]          if_data_read,
  output reg    [63:0]          if_addr,
  output        [1:0]           if_size,
  input         [1:0]           if_resp,
  
  /////////////////////////////////////////////////////////
  input   wire                  pc_jmp,
  input   wire  [`BUS_64]       pc_jmpaddr,

  output  reg   [`BUS_64]       pc_old,
  output  reg   [`BUS_64]       pc,
  output  wire  [`BUS_64]       pc_pred_o,    // 预测的下一个PC
  output  reg   [`BUS_32]       inst,


  output reg                    if_fetched_req,//,
  input  reg                    if_fetched_ack//,

  // 冲刷流水线
  // input   wire                  pipe_flush_req,
  // input   wire  [`BUS_64]       pipe_flush_pc,
  // output  wire                  pipe_flush_ack
  
  // ,
	// input                         if_flush      // 冲刷掉这条指令，使用 addi x0,x0,0
);

wire handshake_done = if_valid & if_ready;
reg [63:0] addr;

// wire pipe_flush_hs = pipe_flush_req & pipe_flush_ack;
// assign pipe_flush_ack = 1'b1;

// pc生成
// always @(posedge clk) begin
//   if (rst) begin
//     pc      <= `PC_START;
//   end
//   else begin
//     // 
//     if (i_jump_flush_req) begin
//       pc    <= i_jump_flush_pc;
//     end
//     else begin
      
//     end
//   end
// end

// fetch an instruction
assign if_valid = 1'b1;

always @( posedge clk ) begin
  if (rst) begin
    // pc_old    <= 0;
    pc              <= 0;
    if_addr         <= `PC_START;
    if_fetched_req  <= 0;
  end
  else begin
    if (handshake_done) begin
      inst              <= if_data_read[31:0];
      pc                <= if_addr;
      if_addr           <= if_addr + 4;
      if_fetched_req    <= 1;
    end
    else if (if_fetched_ack) begin
      if_fetched_req    <= 0; 
    end
  end
end

assign pc_pred_o = pc + 4;

assign if_size = `SIZE_W;

endmodule
