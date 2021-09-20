
// ZhengpuShi

// Exception Unit, 时序电路

`include "../defines.v"

module exceptionU(
  input   wire                rst,
  input   wire                clk,
  input   wire                ena,
  input   wire                ack,
  output  reg                 req,
  input   wire  [4 : 0]       i_inst_type,
  input   wire  [7 : 0]       i_inst_opcode,
  input   wire  [`BUS_64]     i_pc,
  input   reg   [`BUS_64]     i_csr_rdata,
  output  reg   [11 : 0]      o_csr_addr,
  output  reg                 o_csr_ren,
  output  reg                 o_csr_wen,
  output  reg   [`BUS_64]     o_csr_wdata
);

parameter [1:0] STATE_NULL      = 2'd0;
parameter [1:0] STATE_MEPC      = 2'd1;
parameter [1:0] STATE_MCAUSE    = 2'd2;
parameter [1:0] STATE_MSTATUS   = 2'd3;

reg [1:0] state;
// wire state_null             = state == STATE_IDLE;
// wire state_ready            = state == STATE_READY;
// wire state_store_from_ram   = state == STATE_STORE_FROM_RAM;
// wire state_store_to_bus     = state == STATE_STORE_TO_BUS;
// wire state_load_from_bus    = state == STATE_LOAD_FROM_BUS;
// wire state_load_to_ram      = state == STATE_LOAD_TO_RAM;
reg [1:0] step;

wire hs = ack & req;


always @(posedge clk) begin
  if (rst) begin
    state <= STATE_NULL;
    step <= 0;
  end
  else begin
    if (!hs) begin
      case (state)
        STATE_NULL:   begin
          if (ena) begin
            state <= STATE_MEPC;
            step <= 0;
          end
        end
        
        STATE_MEPC: begin
          if (step == 2) begin
            state <= STATE_MCAUSE;
            step <= 0;
          end
        end
        
        STATE_MCAUSE: begin
          if (step == 2) begin
            state <= STATE_NULL;
            step <= 0;
            req <= 1;
          end
        end

        default: ;
      endcase
    end
    else begin
      req <= 0;
    end
    
  end
end

reg [63:0] csr_rdata_save;

always @(posedge clk) begin
  if (rst) begin
    csr_rdata_save = 0;
  end
  else begin
    case (state)
      STATE_MEPC: begin
        case (step)
          0:  begin 
            o_csr_addr      <=`CSR_ADR_MEPC; 
            o_csr_wen       <= 1; 
            o_csr_wdata     <= i_pc;
            step            <= 1;
          end
          1:  begin
            o_csr_wen       <= 0;
            step            <= 2;
          end
          default: ;
        endcase
      end
      STATE_MCAUSE: begin
        case (step)
          0:  begin 
            o_csr_addr      <=`CSR_ADR_MCAUSE; 
            o_csr_wen       <= 1; 
            o_csr_wdata     <= 64'd11;
            step            <= 1;
          end
          1:  begin
            o_csr_wen       <= 0;
            step            <= 2;
          end
          default: ;
        endcase
      end
      default: ;
    endcase
  end
end


endmodule
