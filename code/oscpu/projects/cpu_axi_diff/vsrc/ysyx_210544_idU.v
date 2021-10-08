
// ZhengpuShi

// Instruction Decode Unit, 组合逻辑电路

`include "defines.v"

module ysyx_210544_idU(
  input   wire                rst,
  input   wire  [`BUS_32]     i_inst,
  input   wire  [`BUS_64]     i_rs1_data,
  input   wire  [`BUS_64]     i_rs2_data,
  input   wire  [`BUS_64]     i_pc,
  output  wire                o_rs1_ren,
  output  wire  [`BUS_RIDX]   o_rs1,
  output  wire                o_rs2_ren,
  output  wire  [`BUS_RIDX]   o_rs2,
  output  wire  [`BUS_RIDX]   o_rd,
  output  wire                o_rd_wen,
  output  wire  [7 : 0]       o_inst_opcode,
  output  reg   [`BUS_64]     o_op1,
  output  reg   [`BUS_64]     o_op2,
  output  reg   [`BUS_64]     o_op3,
  output  wire                o_skipcmt
);

wire [7  : 0] inst_opcode;

wire [6  : 0] opcode;
wire [4  : 0] rs1;
wire [4  : 0] rs2;
wire [4  : 0] rd;
wire [2  : 0] func3;
wire [6  : 0] func7;
wire [5  : 0] shamt;
wire [63 : 0] imm_I;
wire [63 : 0] imm_S;
wire [63 : 0] imm_B;
wire [63 : 0] imm_U;
wire [63 : 0] imm_J;
wire inst_lui;     
wire inst_auipc;   
wire inst_jal;     
wire inst_jalr;    
wire inst_beq;     
wire inst_bne;     
wire inst_blt;     
wire inst_bge;     
wire inst_bltu;    
wire inst_bgeu;    
wire inst_lb;      
wire inst_lh;      
wire inst_lw;      
wire inst_lbu;     
wire inst_lhu;     
wire inst_sb;      
wire inst_sh;      
wire inst_sw;      
wire inst_addi;    
wire inst_slti;    
wire inst_sltiu;   
wire inst_xori;    
wire inst_ori;     
wire inst_andi;    
wire inst_slli;    
wire inst_srli;    
wire inst_srai;    
wire inst_add;     
wire inst_sub;     
wire inst_sll;     
wire inst_slt;     
wire inst_sltu;    
wire inst_xor;     
wire inst_srl;     
wire inst_sra;     
wire inst_or;      
wire inst_and;     
wire inst_fence;   
wire inst_fencei;  
wire inst_ecall;   
wire inst_ebreak;  
wire inst_csrrw;   
wire inst_csrrs;   
wire inst_csrrc;   
wire inst_csrrwi;  
wire inst_csrrsi;  
wire inst_csrrci;  
wire inst_lwu;     
wire inst_ld;      
wire inst_sd;      
wire inst_addiw;   
wire inst_slliw;   
wire inst_srliw;   
wire inst_sraiw;   
wire inst_addw;    
wire inst_subw;    
wire inst_sllw;    
wire inst_srlw;    
wire inst_sraw;    
wire inst_mret;    
wire inst_load;    
wire inst_store;   

wire inst_type_R;
wire inst_type_I;
wire inst_type_S;
wire inst_type_B;
wire inst_type_U;
wire inst_type_J;
wire inst_type_CSRI;  // csr immediate



assign o_inst_opcode = inst_opcode;
assign opcode     = i_inst[6  :  0];
assign rs1        = i_inst[19 : 15];
assign rs2        = i_inst[24 : 20];
assign rd         = i_inst[11 :  7];
assign func3      = i_inst[14 : 12];
assign func7      = i_inst[31 : 25];
assign shamt      = i_inst[25 : 20];
assign imm_I      = { {52{i_inst[31]}}, i_inst[31 : 20] };
assign imm_S      = { {52{i_inst[31]}}, i_inst[31 : 25], i_inst[11 : 7] };
assign imm_B      = { {52{i_inst[31]}}, i_inst[7], i_inst[30 : 25], i_inst[11 : 8], 1'b0 };
assign imm_U      = { {32{i_inst[31]}}, i_inst[31 : 12], 12'b0 };
assign imm_J      = { {44{i_inst[31]}}, i_inst[19 : 12], i_inst[20], i_inst[30 : 21], 1'b0 };

assign inst_lui     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] &  opcode[2];
assign inst_auipc   = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] &  opcode[2];
assign inst_jal     =  opcode[6] &  opcode[5] & ~opcode[4] &  opcode[3] &  opcode[2];
assign inst_jalr    =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] &  opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
assign inst_beq     =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
assign inst_bne     =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
assign inst_blt     =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] & ~func3[0];
assign inst_bge     =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0];
assign inst_bltu    =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
assign inst_bgeu    =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] &  func3[0];
assign inst_lb      = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
assign inst_lh      = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
assign inst_lw      = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];
assign inst_lbu     = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] & ~func3[0];
assign inst_lhu     = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0];
assign inst_sb      = ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
assign inst_sh      = ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
assign inst_sw      = ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];
assign inst_addi    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
assign inst_slti    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];
assign inst_sltiu   = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
assign inst_xori    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] & ~func3[0];
assign inst_ori     = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
assign inst_andi    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] &  func3[0];
assign inst_slli    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
assign inst_srli    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] & ~func7[5];
assign inst_srai    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] &  func7[5];
assign inst_add     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] & ~func7[5];
assign inst_sub     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] &  func7[5];
assign inst_sll     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
assign inst_slt     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];
assign inst_sltu    = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
assign inst_xor     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] & ~func3[0];
assign inst_srl     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] & ~func7[5];
assign inst_sra     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] &  func7[5];
assign inst_or      = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
assign inst_and     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] &  func3[0];
assign inst_fence   = ~opcode[6] & ~opcode[5] & ~opcode[4] &  opcode[3] &  opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
assign inst_fencei  = ~opcode[6] & ~opcode[5] & ~opcode[4] &  opcode[3] &  opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
assign inst_ecall   =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] & ~func7[4] & ~func7[3] & ~func7[0] & ~rs2[1];
assign inst_ebreak  =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] & ~func7[4] & ~func7[3] &  func7[0] & ~rs2[1];
assign inst_csrrw   =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
assign inst_csrrs   =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];
assign inst_csrrc   =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
assign inst_csrrwi  =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0];
assign inst_csrrsi  =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
assign inst_csrrci  =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] &  func3[0];
assign inst_lwu     = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
assign inst_ld      = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
assign inst_sd      = ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
assign inst_addiw   = ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
assign inst_slliw   = ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
assign inst_srliw   = ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] & ~func7[5];
assign inst_sraiw   = ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] &  func7[5];
assign inst_addw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] & ~func7[5];
assign inst_subw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] &  func7[5];
assign inst_sllw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
assign inst_srlw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] & ~func7[5];
assign inst_sraw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] &  func7[5];
assign inst_mret    =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] &  func7[4] &  func7[3] & ~func7[0] & rs2[1];
assign inst_load    = inst_lb | inst_lbu | inst_lh | inst_lhu | inst_lw | inst_lwu | inst_ld;
assign inst_store   = inst_sb | inst_sh | inst_sw | inst_sd;

// arith inst: 10000; logic: 01000;
// load-store: 00100; j: 00010;  sys: 000001
// === I don't use the logic above!
assign inst_opcode[7] = rst ? 0 : 0;
assign inst_opcode[6] = rst ? 0 : 0;
assign inst_opcode[5] = rst ? 0 : 
  ( inst_sltu   | inst_xor    | inst_srl    | inst_sra    | 
    inst_or     | inst_and    | inst_fence  | inst_fencei | 
    inst_ecall  | inst_ebreak | inst_csrrw  | inst_csrrs  | 
    inst_csrrc  | inst_csrrwi | inst_csrrsi | inst_csrrci |
    inst_lwu    | inst_ld     | inst_sd     | inst_addiw  |
    inst_slliw  | inst_srliw  | inst_sraiw  | inst_addw   | 
    inst_subw   | inst_sllw   | inst_srlw   | inst_sraw   |
    inst_mret   );
assign inst_opcode[4] = rst ? 0 : 
  ( inst_sb     | inst_sh     | inst_sw     | inst_addi   | 
    inst_slti   | inst_sltiu  | inst_xori   | inst_ori    | 
    inst_andi   | inst_slli   | inst_srli   | inst_srai   | 
    inst_add    | inst_sub    | inst_sll    | inst_slt    |
    inst_lwu    | inst_ld     | inst_sd     | inst_addiw  |
    inst_slliw  | inst_srliw  | inst_sraiw  | inst_addw   | 
    inst_subw   | inst_sllw   | inst_srlw   | inst_sraw   |
    inst_mret   );
assign inst_opcode[3] = rst ? 0 : 
  ( inst_bge    | inst_bltu   | inst_bgeu   | inst_lb     | 
    inst_lh     | inst_lw     | inst_lbu    | inst_lhu    | 
    inst_andi   | inst_slli   | inst_srli   | inst_srai   | 
    inst_add    | inst_sub    | inst_sll    | inst_slt    | 
    inst_ecall  | inst_ebreak | inst_csrrw  | inst_csrrs  | 
    inst_csrrc  | inst_csrrwi | inst_csrrsi | inst_csrrci |
    inst_sllw   | inst_srlw   | inst_sraw   | inst_subw   |
    inst_mret   );
assign inst_opcode[2] = rst ? 0 : 
  ( inst_jalr   | inst_beq    | inst_bne    | inst_blt    | 
    inst_lh     | inst_lw     | inst_lbu    | inst_lhu    | 
    inst_slti   | inst_sltiu  | inst_xori   | inst_ori    | 
    inst_add    | inst_sub    | inst_sll    | inst_slt    | 
    inst_or     | inst_and    | inst_fence  | inst_fencei | 
    inst_csrrc  | inst_csrrwi | inst_csrrsi | inst_csrrci |
    inst_slliw  | inst_srliw  | inst_sraiw  | inst_mret   );
assign inst_opcode[1] = rst ? 0 : 
  ( inst_auipc  | inst_jal    | inst_bne    | inst_blt    | 
    inst_bgeu   | inst_lb     | inst_lbu    | inst_lhu    | 
    inst_sw     | inst_addi   | inst_xori   | inst_ori    | 
    inst_srli   | inst_srai   | inst_sll    | inst_slt    | 
    inst_srl    | inst_sra    | inst_fence  | inst_fencei | 
    inst_csrrw  | inst_csrrs  | inst_csrrsi | inst_csrrci |
    inst_sd     | inst_addiw  | inst_sraiw  | inst_addw   | 
    inst_srlw   | inst_sraw   );
assign inst_opcode[0] = rst ? 0 : 
  ( inst_lui    | inst_jal    | inst_beq    | inst_blt    | 
    inst_bltu   | inst_lb     | inst_lw     | inst_lhu    | 
    inst_sh     | inst_addi   | inst_sltiu  | inst_ori    | 
    inst_slli   | inst_srai   | inst_sub    | inst_slt    | 
    inst_xor    | inst_sra    | inst_and    | inst_fencei | 
    inst_ebreak | inst_csrrs  | inst_csrrwi | inst_csrrci |
    inst_ld     | inst_addiw  | inst_srliw  | inst_addw   | 
    inst_sllw   | inst_sraw   ); 

assign inst_type_R    = rst ? 0 : 
  ( inst_add    | inst_sub    | inst_sll    | inst_slt    | 
    inst_sltu   | inst_xor    | inst_srl    | inst_sra    | 
    inst_or     | inst_and    | inst_addw   | inst_subw   | 
    inst_sllw   | inst_srlw   | inst_sraw   );
assign inst_type_I    = rst ? 0 : 
  ( inst_jalr   | inst_lb     | inst_lh     | inst_lw     | 
    inst_ld     | inst_lbu    | inst_lhu    | inst_lwu    | 
    inst_addi   | inst_slti   | inst_sltiu  | inst_xori   | 
    inst_ori    | inst_andi   | inst_slli   | inst_srli   | 
    inst_srai   | inst_csrrw  | inst_csrrs  | inst_csrrc  |
    inst_lwu    | inst_ld     | inst_addiw  | inst_slliw  | 
    inst_srliw  | inst_sraiw  | inst_csrrwi | inst_csrrsi | 
    inst_csrrci );
assign inst_type_S    = rst ? 0 : 
  ( inst_sb     | inst_sh     | inst_sw     | inst_sd     );
assign inst_type_B    = rst ? 0 : 
  ( inst_beq    | inst_bne    | inst_blt    | inst_bge   | 
    inst_bltu   | inst_bgeu   );
assign inst_type_U    = rst ? 0 : 
  ( inst_lui    | inst_auipc  );
assign inst_type_J    = rst ? 0 : 
  ( inst_jal    );
assign inst_type_CSRI = rst ? 0 : 
  ( inst_csrrwi | inst_csrrsi | inst_csrrci );

assign o_rs1_ren  = rst ? 0 : ( inst_type_R | inst_type_I | inst_type_S | inst_type_B);
assign o_rs1      = rst ? 0 : ((inst_type_R | inst_type_I | inst_type_S | inst_type_B) ? rs1 : 0 );
assign o_rs2_ren  = rst ? 0 : ( inst_type_R | inst_type_S | inst_type_B);
assign o_rs2      = rst ? 0 : ((inst_type_R | inst_type_S | inst_type_B) ? rs2 : 0 );

assign o_rd_wen   = rst ? 0 : ( inst_type_R | inst_type_I | inst_type_U | inst_type_J | inst_type_CSRI);
assign o_rd       = rst ? 0 : ((inst_type_R | inst_type_I | inst_type_U | inst_type_J | inst_type_CSRI) ? rd  : 0 );

always @(*) begin
  if (rst) begin
    o_op1 = 0;
  end
  else begin
    if (inst_type_R | inst_type_I | inst_type_S | inst_type_B) begin
      if (inst_csrrwi | inst_csrrsi | inst_csrrci) begin
        o_op1 = {59'd0, rs1};
      end
      else begin
        o_op1 = i_rs1_data;
      end
    end
    else if (inst_type_U) begin
      o_op1 = imm_U;
    end
    else if (inst_type_J) begin
      o_op1 = i_pc;
    end
    else if (inst_type_CSRI) begin
      o_op1 = {59'd0, rs1};
    end
    else begin
      o_op1 = 0;
    end
  end
end

always @(*) begin
  if (rst) begin
    o_op2 = 0;
  end
  else begin
    if (inst_type_R | inst_type_S | inst_type_B) begin
      o_op2 = i_rs2_data;
    end
    else if (inst_type_J) begin
      o_op2 = 4;
    end
    else if (inst_type_I) begin
      if (inst_slliw | inst_srai) begin
        o_op2 = {58'd0, shamt};
      end
      else begin
        o_op2 = imm_I;
      end
    end
    else if (inst_type_U) begin
      o_op2 = i_pc;
    end
    else begin
      o_op2 = 0;
    end
  end
end

// o_op3
always @(*) begin
  if (rst) begin
    o_op3 = 0;
  end
  else begin
    if (inst_type_B) begin
      o_op3 = i_pc + imm_B;
    end
    else if (inst_type_J) begin
      o_op3 = i_pc + imm_J;
    end
    else if (inst_type_S) begin
      o_op3 = imm_S;
    end
    else if (inst_type_I) begin
      if (inst_jalr) begin
        o_op3 = i_pc + 4;
      end
      else if (inst_load | inst_store) begin
        o_op3 = imm_I;
      end
      else begin
        o_op3 = 0;
      end
    end
    else begin
      o_op3 = 0;
    end
  end
end

// 某些自定义指令，需要通知difftest跳过比对（提交，但不对比）
assign o_skipcmt = 
  (i_inst == 32'h7b)                 // putch
  // | (o_opcode == `OPCODE_CSR)   
  // | mem_addr_is_device
  ;

wire _unused_ok = &{1'b0,
  opcode[1:0],
  func7[6],
  func7[2:1],
  1'b0};

endmodule
