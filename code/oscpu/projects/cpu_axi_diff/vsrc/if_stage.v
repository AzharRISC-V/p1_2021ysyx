
//--xuezhen--

`include "defines.v"


module if_stage(
  input wire clk,
  input wire rst,
  
  input   wire                  pc_jmp,
  input   wire  [`BUS_64]       pc_jmpaddr,

  output  reg   [`BUS_64]       pc_old,
  output  reg   [`BUS_64]       pc,
  output  reg   [`BUS_32]       inst,

	output if_valid,
	input  if_ready,
  input  [63:0] if_data_read,
  output reg [63:0] if_addr,
  output [1:0] if_size,
  input  [1:0] if_resp,

  output reg fetched
);

wire handshake_done = if_valid & if_ready;
reg [63:0] addr;

// fetch an instruction
always @( posedge clk ) begin
  if (rst) begin
    pc_old    <= 0;
    pc <= `PC_START;
    if_addr <= `PC_START;
    fetched <= 0;
  end
  else if ( handshake_done ) begin
    pc_old  <= pc;
    pc <= if_addr;
    if_addr <= pc_jmp ? pc_jmpaddr : (if_addr + 4);
    fetched <= 1;
    inst <= if_data_read[31:0];
  end
  else begin
    fetched <= 0;
  end
end

assign if_valid = 1'b1;
assign if_size = `SIZE_W;

endmodule
