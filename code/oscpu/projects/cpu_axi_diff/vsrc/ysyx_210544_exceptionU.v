
// ZhengpuShi

// Exception Unit, 时序电路

`include "defines.v"

module ysyx_210544_exceptionU(
  input   wire                rst,
  input   wire                clk,
  input   wire                ena,
  input   wire                ack,
  output  reg                 req,
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

parameter [3:0] STATE_NULL                    = 4'd0;
// 异常或中断进入：ecall、定时器中断等
parameter [3:0] STATE_ENTER_WRITE_MEPC        = 4'd1;   // machine exception program counter
parameter [3:0] STATE_ENTER_WRITE_MCAUSE      = 4'd2;   // machine trap cause
parameter [3:0] STATE_ENTER_READ_MTVEC        = 4'd3;   // machine trap-handler base address
parameter [3:0] STATE_ENTER_READ_MSTATUS      = 4'd4;   // machine status register
parameter [3:0] STATE_ENTER_WRITE_MSTATUS     = 4'd5;   // machine status register
// 异常或中断返回：mret
parameter [3:0] STATE_LEAVE_READ_MSTATUS      = 4'd6;   // machine status register
parameter [3:0] STATE_LEAVE_READ_MEPC         = 4'd7;   // machine exception program counter
parameter [3:0] STATE_LEAVE_WRITE_MSTATUS     = 4'd8;   // machine status register

reg [3:0] state;
reg [1:0] step;
// 在异常发生的第一个时钟周期就确定下来，因为有些输入信号只保持一个周期
reg [63:0] exception_cause;     // 异常原因

wire hs = ack & req;

always @(posedge clk) begin
  if (rst) begin
    state <= STATE_NULL;
    step <= 0;
    exception_cause <= 0;
  end
  else begin
    if (!hs) begin
      case (state)
        STATE_NULL:   begin
          if (ena) begin
            if (i_inst_opcode == `INST_ECALL) begin
              state <= STATE_ENTER_WRITE_MEPC;
              exception_cause <= 64'd11;
              //$write("#ecall\n"); $fflush();
            end
            else if (i_inst_opcode == `INST_MRET) begin
              state <= STATE_LEAVE_READ_MSTATUS;
            end
            else begin
              state <= STATE_ENTER_WRITE_MEPC;
              exception_cause <= 64'h80000000_00000007;
              // $write("#time-instr\n"); $fflush();
              $write("."); $fflush();
            end
            step <= 0;
          end
        end
        
        STATE_ENTER_WRITE_MEPC: begin
          if (step == 2) begin
            state <= STATE_ENTER_WRITE_MCAUSE;
            step <= 0;
          end
        end
        
        STATE_ENTER_WRITE_MCAUSE: begin
          if (step == 2) begin
            state <= STATE_ENTER_READ_MTVEC;
            step <= 0;
          end
        end
        
        STATE_ENTER_READ_MTVEC: begin
          if (step == 2) begin
            state <= STATE_ENTER_READ_MSTATUS;
            step <= 0;
          end
        end
        
        STATE_ENTER_READ_MSTATUS: begin
          if (step == 2) begin
            state <= STATE_ENTER_WRITE_MSTATUS;
            step <= 0;
          end
        end
        
        STATE_ENTER_WRITE_MSTATUS: begin
          if (step == 2) begin
            state <= STATE_NULL;
            step <= 0;
            req <= 1;
          end
        end
        
        STATE_LEAVE_READ_MSTATUS: begin
          if (step == 2) begin
            state <= STATE_LEAVE_READ_MEPC;
            step <= 0;
          end
        end
        
        STATE_LEAVE_READ_MEPC: begin
          if (step == 2) begin
            state <= STATE_LEAVE_WRITE_MSTATUS;
            step <= 0;
          end
        end
        
        STATE_LEAVE_WRITE_MSTATUS: begin
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

      STATE_ENTER_WRITE_MEPC: begin
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

      STATE_ENTER_WRITE_MCAUSE: begin
        case (step)
          0:  begin 
            o_csr_addr      <=`CSR_ADR_MCAUSE; 
            o_csr_wen       <= 1; 
            o_csr_wdata     <= exception_cause;
            step            <= 1;
          end
          1:  begin
            o_csr_wen       <= 0;
            step            <= 2;
          end
          default: ;
        endcase
      end

      STATE_ENTER_READ_MTVEC: begin
        case (step)
          0:  begin 
            o_csr_addr      <=`CSR_ADR_MTVEC; 
            o_csr_ren       <= 1; 
            step            <= 1;
          end
          1:  begin
            o_csr_ren       <= 0;
            step            <= 2;
            csr_rdata_save2 <= i_csr_rdata;
          end
          default: ;
        endcase
      end
      
      STATE_ENTER_READ_MSTATUS: begin
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
      
      STATE_ENTER_WRITE_MSTATUS: begin
        case (step)
          0:  begin 
            o_csr_addr      <=`CSR_ADR_MSTATUS; 
            o_csr_wen       <= 1; 
            o_csr_wdata     <= {
              csr_rdata_save1[63:13],
              2'b11,                    // [12:11]: MPP, set to M-mode
              csr_rdata_save1[10:8], 
              csr_rdata_save1[3],       // [7]: MPIE, set with MIE
              csr_rdata_save1[6:4], 
              1'b0,                     // [3]: MIE, set 0
              csr_rdata_save1[2:0]
              };
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
      
      STATE_LEAVE_READ_MSTATUS: begin
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

      STATE_LEAVE_READ_MEPC: begin
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
      
      STATE_LEAVE_WRITE_MSTATUS: begin
        case (step)
          0:  begin 
            o_csr_addr      <=`CSR_ADR_MSTATUS; 
            o_csr_wen       <= 1; 
            o_csr_wdata     <= {
              csr_rdata_save1[63:13],
              2'b00,                    // [12:11]: MPP, set to U-mode
              csr_rdata_save1[10:8], 
              1'b1,                     // [7]: MPIE, set to 1
              csr_rdata_save1[6:4], 
              csr_rdata_save1[7],       // [3]: MIE, set with MPIE
              csr_rdata_save1[2:0]
              };
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

wire _unused_ok = &{1'b0,
  csr_rdata_save1[12:11],
  1'b0};

endmodule
