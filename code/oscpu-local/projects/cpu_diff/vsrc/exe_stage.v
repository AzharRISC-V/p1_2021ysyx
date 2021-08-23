
//--xuezhen--

`include "defines.v"

module exe_stage(
  input wire rst,
  input wire [2 : 0]inst_type_i,
  input wire [4 : 0]inst_opcode_i,
  input wire [2 : 0]inst_funct3,
  input wire [6 : 0]inst_funct7,
  input wire [`REG_BUS]op1,
  input wire [`REG_BUS]op2,
  
  output wire [2 : 0]inst_opcode_o,
  output reg  [`REG_BUS]rd_data
);

assign inst_opcode_o = inst_opcode_i;

always@( * ) begin
  if( rst == 1'b1 ) begin
    rd_data = `ZERO_WORD;
  end
  else begin
    case( inst_opcode_i )
      `OPCODE_ADDI: begin
        case( inst_funct3 )
          `FUNCT3_ADDI:   begin rd_data = op1 + op2; end
          default:;
        endcase
      end
      default:            begin rd_data = `ZERO_WORD; end
    endcase
  end
end


endmodule
