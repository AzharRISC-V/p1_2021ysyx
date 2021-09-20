
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
  output  reg                 o_pc_jmp,
  output  reg   [`BUS_64]     o_pc_jmpaddr,
  input   reg   [`BUS_64]     i_csr_rdata,
  output  reg   [11 : 0]      o_csr_addr,
  output  reg                 o_csr_ren,
  output  reg                 o_csr_wen,
  output  reg   [`BUS_64]     o_csr_wdata
);

parameter [2:0] STATE_NULL                    = 3'd0;
parameter [2:0] STATE_ECALL_WRITE_MEPC        = 3'd1;   // machine exception program counter
parameter [2:0] STATE_ECALL_WRITE_MCAUSE      = 3'd2;   // machine trap cause
parameter [2:0] STATE_ECALL_READ_MTVEC        = 3'd3;   // machine trap-handler base address
parameter [2:0] STATE_ECALL_WRITE_MSTATUS     = 3'd4;   // machine status register
parameter [2:0] STATE_MRET_READ_MSTATUS       = 3'd5;   // machine status register
parameter [2:0] STATE_MRET_READ_MEPC          = 3'd6;   // machine exception program counter
parameter [2:0] STATE_MRET_WRITE_MSTATUS      = 3'd7;   // machine status register

parameter [63:0] MSTATUS_MPIE_MASK      = 64'h80;
parameter [63:0] MSTATUS_MPP_MASK       = 64'h1800;

reg [2:0] state;
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
            if (i_inst_opcode == `INST_ECALL)       state <= STATE_ECALL_WRITE_MEPC;
            else if (i_inst_opcode == `INST_MRET)   state <= STATE_MRET_READ_MSTATUS;
            step <= 0;
          end
        end
        
        STATE_ECALL_WRITE_MEPC: begin
          if (step == 2) begin
            state <= STATE_ECALL_WRITE_MCAUSE;
            step <= 0;
          end
        end
        
        STATE_ECALL_WRITE_MCAUSE: begin
          if (step == 2) begin
            state <= STATE_ECALL_READ_MTVEC;
            step <= 0;
          end
        end
        
        STATE_ECALL_READ_MTVEC: begin
          if (step == 2) begin
            state <= STATE_ECALL_WRITE_MSTATUS;
            step <= 0;
          end
        end
        
        STATE_ECALL_WRITE_MSTATUS: begin
          if (step == 2) begin
            state <= STATE_NULL;
            step <= 0;
            req <= 1;
          end
        end
        
        STATE_MRET_READ_MSTATUS: begin
          if (step == 2) begin
            state <= STATE_MRET_READ_MEPC;
            step <= 0;
          end
        end
        
        STATE_MRET_READ_MEPC: begin
          if (step == 2) begin
            state <= STATE_MRET_WRITE_MSTATUS;
            step <= 0;
          end
        end
        
        STATE_MRET_WRITE_MSTATUS: begin
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

reg [63:0] csr_rdata_save1;
reg [63:0] csr_rdata_save2;

always @(posedge clk) begin
  if (rst) begin
    o_pc_jmp        <= 0;
    o_pc_jmpaddr    <= 0;
    csr_rdata_save1  <= 0;
  end
  else begin
    case (state)
      STATE_NULL: begin
        o_pc_jmp <= 0;
        o_pc_jmpaddr <= 0;  
      end

      STATE_ECALL_WRITE_MEPC: begin
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

      STATE_ECALL_WRITE_MCAUSE: begin
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

      STATE_ECALL_READ_MTVEC: begin
        case (step)
          0:  begin 
            o_csr_addr      <=`CSR_ADR_MTVEC; 
            o_csr_ren       <= 1; 
            step            <= 1;
          end
          1:  begin
            o_csr_ren       <= 0;
            step            <= 2;
            csr_rdata_save1 <= i_csr_rdata;
          end
          default: ;
        endcase
      end
      
      STATE_ECALL_WRITE_MSTATUS: begin
        case (step)
          0:  begin 
            o_csr_addr      <=`CSR_ADR_MSTATUS; 
            o_csr_wen       <= 1; 
            o_csr_wdata     <= 64'h00000000_00001800;
            step            <= 1;
          end
          1:  begin
            o_csr_wen       <= 0;
            step            <= 2;
            o_pc_jmp        <= 1;
            o_pc_jmpaddr    <= csr_rdata_save1;
          end
          default: ;
        endcase
      end
      
      STATE_MRET_READ_MSTATUS: begin
        case (step)
          0:  begin 
            o_csr_addr      <=`CSR_ADR_MSTATUS; 
            o_csr_ren       <= 1; 
            step            <= 1;
          end
          1:  begin
            o_csr_ren       <= 0;
            step            <= 2;
            csr_rdata_save1 <= i_csr_rdata;
          end
          default: ;
        endcase
      end

      STATE_MRET_READ_MEPC: begin
        case (step)
          0:  begin 
            o_csr_addr      <=`CSR_ADR_MEPC; 
            o_csr_ren       <= 1; 
            step            <= 1;
          end
          1:  begin
            o_csr_ren       <= 0;
            csr_rdata_save2 <= i_csr_rdata;
            step            <= 2;
          end
          default: ;
        endcase
      end
      
      STATE_MRET_WRITE_MSTATUS: begin
        case (step)
          0:  begin 
            o_csr_addr      <=`CSR_ADR_MSTATUS; 
            o_csr_wen       <= 1; 
            o_csr_wdata     <= csr_rdata_save1 & (~MSTATUS_MPP_MASK) | MSTATUS_MPIE_MASK;
            step            <= 1;
          end
          1:  begin
            o_csr_wen       <= 0;
            step            <= 2;
            o_pc_jmp        <= 1;
            o_pc_jmpaddr    <= csr_rdata_save2;
          end
          default: ;
        endcase
      end

      default: ;
    endcase
  end
end


endmodule
