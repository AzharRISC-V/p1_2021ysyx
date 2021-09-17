
// ZhengpuShi

// Instruction Decode Unit, 组合逻辑电路

`include "../defines.v"

module idU(
  input   wire                rst,
  input   wire                i_ena,
  input   wire  [`BUS_32]     i_inst,
  input   wire  [`BUS_64]     i_rs1_data,
  input   wire  [`BUS_64]     i_rs2_data,
  input   wire  [`BUS_64]     i_pc,
  input   wire  [`BUS_64]     i_pc_pred,
  output  reg                 o_rs1_ren,
  output  wire  [`BUS_RIDX]   o_rs1,
  output  wire                o_rs2_ren,
  output  wire  [`BUS_RIDX]   o_rs2,
  output  wire  [`BUS_RIDX]   o_rd,
  output  wire                o_rd_wen,
  output  wire                o_memren,
  output  wire  [`BUS_64]     o_memaddr,
  output  wire                o_memwen,
  output  wire  [`BUS_64]     o_memwdata,
  output  reg   [11 : 0]      o_csr_addr,
  output  reg   [1 : 0]       o_csr_op,
  output  reg   [`BUS_64]     o_csr_wdata,
  input   reg   [`BUS_64]     i_csr_rdata,
  output  wire  [4 : 0]       o_inst_type,
  output  wire  [7 : 0]       o_inst_opcode,
  output  wire  [2 : 0]       o_itype,
  output  wire  [`BUS_OPCODE] o_opcode,
  output  wire  [`BUS_FUNCT3] o_funct3,
  output  wire  [`BUS_FUNCT7] o_funct7,
  output  wire  [`BUS_64]     o_op1,
  output  wire  [`BUS_64]     o_op2,
  output  wire  [`BUS_64]     o_op3,
  output  wire  [`BUS_64]     o_pc_pred,
  output  wire  [1:0]         o_memaction,
  output  wire                o_skipcmt
);

wire [4  : 0] inst_type;
wire [7  : 0] inst_opcode;

assign o_inst_type = inst_type;
assign o_inst_opcode = inst_opcode;

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

wire inst_lui     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] &  opcode[2];
wire inst_auipc   = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] &  opcode[2];
wire inst_jal     =  opcode[6] &  opcode[5] & ~opcode[4] &  opcode[3] &  opcode[2];
wire inst_jalr    =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] &  opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];

wire inst_beq     =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
wire inst_bne     =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
wire inst_blt     =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] & ~func3[0];
wire inst_bge     =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0];
wire inst_bltu    =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
wire inst_bgeu    =  opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] &  func3[0];

wire inst_lb      = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
wire inst_lh      = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
wire inst_lw      = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];
wire inst_lbu     = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] & ~func3[0];
wire inst_lhu     = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0];

wire inst_sb      = ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
wire inst_sh      = ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
wire inst_sw      = ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];

wire inst_addi    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
wire inst_slti    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];
wire inst_sltiu   = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
wire inst_xori    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] & ~func3[0];
wire inst_ori     = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
wire inst_andi    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] &  func3[0];
wire inst_slli    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
wire inst_srli    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] & ~func7[5];
wire inst_srai    = ~opcode[6] & ~opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] &  func7[5];

wire inst_add     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] & ~func7[5];
wire inst_sub     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] &  func7[5];
wire inst_sll     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
wire inst_slt     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];
wire inst_sltu    = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
wire inst_xor     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] & ~func3[0];
wire inst_srl     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] & ~func7[5];
wire inst_sra     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] &  func7[5];
wire inst_or      = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
wire inst_and     = ~opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] &  func3[0];

wire inst_fence   = ~opcode[6] & ~opcode[5] & ~opcode[4] &  opcode[3] &  opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
wire inst_fencei  = ~opcode[6] & ~opcode[5] & ~opcode[4] &  opcode[3] &  opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
wire inst_ecall   =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] & ~func7[0];
wire inst_ebreak  =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] &  func7[0];

wire inst_csrrw   =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
wire inst_csrrs   =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] & ~func3[0];
wire inst_csrrc   =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
wire inst_csrrwi  =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0];
wire inst_csrrsi  =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
wire inst_csrrci  =  opcode[6] &  opcode[5] &  opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] &  func3[0];

wire inst_lwu     = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] &  func3[2] &  func3[1] & ~func3[0];
wire inst_ld      = ~opcode[6] & ~opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
wire inst_sd      = ~opcode[6] &  opcode[5] & ~opcode[4] & ~opcode[3] & ~opcode[2] & ~func3[2] &  func3[1] &  func3[0];
wire inst_addiw   = ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0];
wire inst_slliw   = ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
wire inst_srliw   = ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] & ~func7[5];
wire inst_sraiw   = ~opcode[6] & ~opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] &  func7[5];
wire inst_addw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] & ~func7[5];
wire inst_subw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] & ~func3[0] &  func7[5];
wire inst_sllw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] & ~func3[2] & ~func3[1] &  func3[0];
wire inst_srlw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] & ~func7[5];
wire inst_sraw    = ~opcode[6] &  opcode[5] &  opcode[4] &  opcode[3] & ~opcode[2] &  func3[2] & ~func3[1] &  func3[0] &  func7[5];

wire inst_load    = inst_lb | inst_lbu | inst_lh | inst_lhu | inst_lw | inst_lwu | inst_ld;
wire inst_store   = inst_sb | inst_sh | inst_sw | inst_sd;

// arith inst: 10000; logic: 01000;
// load-store: 00100; j: 00010;  sys: 000001
// I don't use this!
assign inst_opcode[7] = (  rst == 1'b1 ) ? 0 : 0;
assign inst_opcode[6] = (  rst == 1'b1 ) ? 0 : 0;
assign inst_opcode[5] = (  rst == 1'b1 ) ? 0 : 
  ( inst_sltu   | inst_xor    | inst_srl    | inst_sra    | 
    inst_or     | inst_and    | inst_fence  | inst_fencei | 
    inst_ecall  | inst_ebreak | inst_csrrw  | inst_csrrs  | 
    inst_csrrc  | inst_csrrwi | inst_csrrsi | inst_csrrci |
    inst_lwu    | inst_ld     | inst_sd     | inst_addiw  |
    inst_slliw  | inst_srliw  | inst_sraiw  | inst_addw   | 
    inst_subw   | inst_sllw   | inst_srlw   | inst_sraw   );
assign inst_opcode[4] = (  rst == 1'b1 ) ? 0 : 
  ( inst_sb     | inst_sh     | inst_sw     | inst_addi   | 
    inst_slti   | inst_sltiu  | inst_xori   | inst_ori    | 
    inst_andi   | inst_slli   | inst_srli   | inst_srai   | 
    inst_add    | inst_sub    | inst_sll    | inst_slt    |
    inst_lwu    | inst_ld     | inst_sd     | inst_addiw  |
    inst_slliw  | inst_srliw  | inst_sraiw  | inst_addw   | 
    inst_subw   | inst_sllw   | inst_srlw   | inst_sraw   );
assign inst_opcode[3] = (  rst == 1'b1 ) ? 0 : 
  ( inst_bge    | inst_bltu   | inst_bgeu   | inst_lb     | 
    inst_lh     | inst_lw     | inst_lbu    | inst_lhu    | 
    inst_andi   | inst_slli   | inst_srli   | inst_srai   | 
    inst_add    | inst_sub    | inst_sll    | inst_slt    | 
    inst_ecall  | inst_ebreak | inst_csrrw  | inst_csrrs  | 
    inst_csrrc  | inst_csrrwi | inst_csrrsi | inst_csrrci |
    inst_sllw   | inst_srlw   | inst_sraw   | inst_subw   );
assign inst_opcode[2] = (  rst == 1'b1 ) ? 0 : 
  ( inst_jalr   | inst_beq    | inst_bne    | inst_blt    | 
    inst_lh     | inst_lw     | inst_lbu    | inst_lhu    | 
    inst_slti   | inst_sltiu  | inst_xori   | inst_ori    | 
    inst_add    | inst_sub    | inst_sll    | inst_slt    | 
    inst_or     | inst_and    | inst_fence  | inst_fencei | 
    inst_csrrc  | inst_csrrwi | inst_csrrsi | inst_csrrci |
    inst_slliw  | inst_srliw  | inst_sraiw  );
assign inst_opcode[1] = (  rst == 1'b1 ) ? 0 : 
  ( inst_auipc  | inst_jal    | inst_bne    | inst_blt    | 
    inst_bgeu   | inst_lb     | inst_lbu    | inst_lhu    | 
    inst_sw     | inst_addi   | inst_xori   | inst_ori    | 
    inst_srli   | inst_srai   | inst_sll    | inst_slt    | 
    inst_srl    | inst_sra    | inst_fence  | inst_fencei | 
    inst_csrrw  | inst_csrrs  | inst_csrrsi | inst_csrrci |
    inst_sd     | inst_addiw  | inst_sraiw  | inst_addw   | 
    inst_srlw   | inst_sraw   );
assign inst_opcode[0] = (  rst == 1'b1 ) ? 0 : 
  ( inst_lui    | inst_jal    | inst_beq    | inst_blt    | 
    inst_bltu   | inst_lb     | inst_lw     | inst_lhu    | 
    inst_sh     | inst_addi   | inst_sltiu  | inst_ori    | 
    inst_slli   | inst_srai   | inst_sub    | inst_slt    | 
    inst_xor    | inst_sra    | inst_and    | inst_fencei | 
    inst_ebreak | inst_csrrs  | inst_csrrwi | inst_csrrci |
    inst_ld     | inst_addiw  | inst_srliw  | inst_addw   | 
    inst_sllw   | inst_sraw   ); 

wire inst_type_R;
wire inst_type_I;
wire inst_type_S;
wire inst_type_B;
wire inst_type_U;
wire inst_type_J;
wire inst_type_CSRI;  // csr immediate

assign inst_type_R    = ( rst == 1'b1 ) ? 0 : 
  ( inst_add    | inst_sub    | inst_sll    | inst_slt    | 
    inst_sltu   | inst_xor    | inst_srl    | inst_sra    | 
    inst_or     | inst_and    | inst_addw   | inst_subw   | 
    inst_sllw   | inst_srlw   | inst_sraw   );
assign inst_type_I    = ( rst == 1'b1 ) ? 0 : 
  ( inst_jalr   | inst_lb     | inst_lh     | inst_lw     | 
    inst_ld     | inst_lbu    | inst_lhu    | inst_lwu    | 
    inst_addi   | inst_slti   | inst_sltiu  | inst_xori   | 
    inst_ori    | inst_andi   | inst_slli   | inst_srli   | 
    inst_srai   | inst_csrrw  | inst_csrrs  | inst_csrrc  |
    inst_lwu    | inst_ld     | inst_addiw  | inst_slliw  | 
    inst_srliw  | inst_sraiw  );
assign inst_type_S    = ( rst == 1'b1 ) ? 0 : 
  ( inst_sb     | inst_sh     | inst_sw     | inst_sd     );
assign inst_type_B    = ( rst == 1'b1 ) ? 0 : 
  ( inst_beq    | inst_bne    | inst_blt    | inst_bge   | 
    inst_bltu   | inst_bgeu   );
assign inst_type_U    = ( rst == 1'b1 ) ? 0 : 
  ( inst_lui    | inst_auipc  );
assign inst_type_J    = ( rst == 1'b1 ) ? 0 : 
  ( inst_jal    );
assign inst_type_CSRI = ( rst == 1'b1 ) ? 0 : 
  ( inst_csrrwi | inst_csrrsi | inst_csrrci );

assign o_rs1_ren  = ( rst == 1'b1 ) ? 0 : ( inst_type_R | inst_type_I | inst_type_S | inst_type_B);
assign o_rs1      = ( rst == 1'b1 ) ? 0 : ((inst_type_R | inst_type_I | inst_type_S | inst_type_B) ? rs1 : 0 );
assign o_rs2_ren  = ( rst == 1'b1 ) ? 0 : ( inst_type_R | inst_type_S | inst_type_B);
assign o_rs2      = ( rst == 1'b1 ) ? 0 : ((inst_type_R | inst_type_S | inst_type_B) ? rs2 : 0 );

assign o_rd_wen   = ( rst == 1'b1 ) ? 0 : ( inst_type_R | inst_type_I | inst_type_U | inst_type_J);
assign o_rd       = ( rst == 1'b1 ) ? 0 : ((inst_type_R | inst_type_I | inst_type_U | inst_type_J) ? rd  : 0 );

always @(*) begin
  if (rst == 1'b1) begin
    o_op1 = 0;
  end
  else begin
    if (inst_type_R | inst_type_I | inst_type_S | inst_type_B) begin
      o_op1 = i_rs1_data;
    end
    else if (inst_type_U) begin
      o_op1 = imm_U;
    end
    else if (inst_type_J) begin
      o_op1 = i_pc;
    end
    else begin
      o_op1 = 0;
    end
  end
end


// // o_op1
// always @(*) begin
//   if (i_disable) begin
//     o_op1 = 0;
//   end
//   else begin
//     case (o_itype)
//       `INST_TYPE_R  : o_op1 = i_rs1_data;
//       `INST_TYPE_B  : o_op1 = i_rs1_data;
//       `INST_TYPE_I  : o_op1 = i_rs1_data;
//       `INST_TYPE_J  : o_op1 = i_pc + 4;
//       `INST_TYPE_U  : begin
//         if (o_opcode == `opcode_lui)            o_op1 = imm;
//         else if (o_opcode == `opcode_auipc)     o_op1 = i_pc;
//         else                                    o_op1 = 0;
//       end
//       default       : o_op1 = 0;
//     endcase
//   end
// end

always @(*) begin
  if (rst == 1'b1) begin
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


// // o_op2
// always @(*) begin
//   if (i_disable) begin
//     o_op2 = 0;
//   end
//   else begin
//     case (o_itype)
//       `INST_R_TYPE  : o_op2 = i_rs2_data;
//       `INST_B_TYPE  : o_op2 = i_rs2_data;
//       `INST_I_TYPE  : begin
//         case (o_funct3)
//           `FUNCT3_SLLI  : o_op2 = shamt_64;
//           `FUNCT3_SRLI  : o_op2 = shamt_64;
//           default       : o_op2 = imm;
//         endcase
//       end
//       `INST_J_TYPE  : o_op2 = i_pc + imm;
//       `INST_U_TYPE  : begin
//         if (o_opcode == `OPCODE_AUIPC)    o_op2 = imm;
//         else                              o_op2 = 0;
//       end
//       `INST_S_TYPE  : o_op2 = i_rs2_data;
//       default       : o_op2 = 0;
//     endcase
//   end
// end


// o_op3
always @(*) begin
  if (rst == 1'b1) begin
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
    //   `OPCODE_JALR  : o_op3 = i_pc + 4;
    //   `OPCODE_BEQ   : o_op3 = i_pc + imm_B;
    //   `OPCODE_CSR   : o_op3 = i_csr_rdata;
    //   default       : o_op3 = 0;
    // endcase
  end
end

// wire i_disable = !i_ena;

// assign o_pc_pred = i_disable ? 0 : i_pc_pred;

// // decode
// // 带符号扩展的imm
// wire  [`BUS_64]               imm;
// wire  [`BUS_32]               R_imm;
// wire  [`BUS_32]               I_imm;
// wire  [`BUS_32]               S_imm;
// wire  [`BUS_32]               B_imm;
// wire  [`BUS_32]               U_imm;
// wire  [`BUS_32]               J_imm;

// wire  [5 : 0]                 shamt;
// wire  [`BUS_64]               shamt_64;   // 扩展为64位后的值

// assign o_opcode   = i_disable ? 0 : i_inst[6  :  0];
// assign o_rd       = i_disable ? 0 : i_inst[11 :  7];
// assign o_funct3   = i_disable ? 0 : i_inst[14 : 12];
// assign o_rs1      = i_disable ? 0 : i_inst[19 : 15];
// assign o_rs2      = i_disable ? 0 : i_inst[24 : 20];
// assign o_funct7   = i_disable ? 0 : i_inst[31 : 25];

// assign R_imm    = 0;
// assign I_imm    = i_disable ? 0 : 
//   { {20{i_inst[31]}}, i_inst[31 : 20] };
// assign S_imm    = i_disable ? 0 : 
//   { {20{i_inst[31]}}, i_inst[31 : 25], i_inst[11 : 7] };
// assign B_imm    = i_disable ? 0 : 
//   { {20{i_inst[31]}}, i_inst[7], i_inst[30 : 25], i_inst[11 : 8], 1'b0 };
// assign U_imm    = i_disable ? 0 : 
//   { i_inst[31 : 12], 12'b0 };
// assign J_imm    = i_disable ? 0 : 
//   { {12{i_inst[31]}}, i_inst[19 : 12], i_inst[20], i_inst[30 : 21], 1'b0 };
// assign shamt    = i_disable ? 0 : 
//   i_inst[25 : 20];
// assign shamt_64 = i_disable ? 0 : 
//   {58'd0, shamt};


// // instruction type : R,I,S,B,U,J
// always@(*) begin
//   if (i_disable) begin
//     o_itype = 0;
//   end
//   else begin
//     case (o_opcode)
//       `OPCODE_LUI   : o_itype = `INST_U_TYPE;
//       `OPCODE_AUIPC : o_itype = `INST_U_TYPE;
//       `OPCODE_JAL   : o_itype = `INST_J_TYPE;
//       `OPCODE_JALR  : o_itype = `INST_I_TYPE;
//       `OPCODE_BEQ   : o_itype = `INST_B_TYPE;
//       `OPCODE_LB    : o_itype = `INST_I_TYPE;
//       `OPCODE_SB    : o_itype = `INST_S_TYPE;
//       `OPCODE_ADDI  : o_itype = `INST_I_TYPE;
//       `OPCODE_ADD   : o_itype = `INST_R_TYPE;
//       `OPCODE_FENCE : o_itype = `INST_I_TYPE;
//       `OPCODE_ENV   : o_itype = `INST_I_TYPE;
//       `OPCODE_ADDIW : o_itype = `INST_I_TYPE;
//       `OPCODE_ADDW  : o_itype = `INST_R_TYPE;
//       default       : o_itype = 0;
//     endcase
//   end
// end

// // 立即数的值
// reg [`BUS_32]imm0;
// always @(*) begin
//   case (o_itype)
//     `INST_R_TYPE  : imm0 = R_imm;
//     `INST_I_TYPE  : imm0 = I_imm;
//     `INST_S_TYPE  : imm0 = S_imm;
//     `INST_B_TYPE  : imm0 = B_imm;
//     `INST_U_TYPE  : imm0 = U_imm;
//     `INST_J_TYPE  : imm0 = J_imm;
//     default       : imm0 = 0;
//   endcase
// end
// assign imm = {{32{imm0[31]}}, imm0};

// // rs1读使能
// always @(*) begin
//   if (i_disable) begin
//     o_rs1_ren = 0;
//   end
//   else begin
//     case (o_itype)
//       `INST_R_TYPE  : o_rs1_ren = 1;
//       `INST_I_TYPE  : o_rs1_ren = 1;
//       `INST_S_TYPE  : o_rs1_ren = 1;
//       `INST_B_TYPE  : o_rs1_ren = 1;
//       default       : o_rs1_ren = 0;
//     endcase
//   end
// end

// // rs2读使能
// always @(*) begin
//   if (i_disable) begin
//     o_rs2_ren = 0;
//   end
//   else begin
//     case (o_itype)
//       `INST_R_TYPE  : o_rs2_ren = 1;
//       `INST_S_TYPE  : o_rs2_ren = 1;
//       `INST_B_TYPE  : o_rs2_ren = 1;
//       default       : o_rs2_ren = 0;
//     endcase
//   end
// end

// // mem_ren
// assign o_memren = i_disable ? 0 :
//   ((o_opcode == `OPCODE_LB) ? 1 : 0);

// // mem_addr
// assign o_memaddr = i_disable ? 0 :
//   ((o_memren | o_memwen) ? $signed(i_rs1_data) + $signed(imm) : 0);

// // mem_wen
// assign o_memwen = i_disable ? 0 : 
//   ((o_itype == `INST_S_TYPE) ? 1 : 0);

// // mem_wdata
// assign o_memwdata = i_disable ? 0 : i_rs2_data;

// // o_op1
// always @(*) begin
//   if (i_disable) begin
//     o_op1 = 0;
//   end
//   else begin
//     case (o_itype)
//       `INST_R_TYPE  : o_op1 = i_rs1_data;
//       `INST_B_TYPE  : o_op1 = i_rs1_data;
//       `INST_I_TYPE  : o_op1 = i_rs1_data;
//       `INST_J_TYPE  : o_op1 = i_pc + 4;
//       `INST_U_TYPE  : begin
//         if (o_opcode == `OPCODE_LUI)            o_op1 = imm;
//         else if (o_opcode == `OPCODE_AUIPC)     o_op1 = i_pc;
//         else                                    o_op1 = 0;
//       end
//       default       : o_op1 = 0;
//     endcase
//   end
// end

// // o_op2
// always @(*) begin
//   if (i_disable) begin
//     o_op2 = 0;
//   end
//   else begin
//     case (o_itype)
//       `INST_R_TYPE  : o_op2 = i_rs2_data;
//       `INST_B_TYPE  : o_op2 = i_rs2_data;
//       `INST_I_TYPE  : begin
//         case (o_funct3)
//           `FUNCT3_SLLI  : o_op2 = shamt_64;
//           `FUNCT3_SRLI  : o_op2 = shamt_64;
//           default       : o_op2 = imm;
//         endcase
//       end
//       `INST_J_TYPE  : o_op2 = i_pc + imm;
//       `INST_U_TYPE  : begin
//         if (o_opcode == `OPCODE_AUIPC)    o_op2 = imm;
//         else                              o_op2 = 0;
//       end
//       `INST_S_TYPE  : o_op2 = i_rs2_data;
//       default       : o_op2 = 0;
//     endcase
//   end
// end

// // o_op3
// always @(*) begin
//   if (i_disable) begin
//     o_op3 = 0;
//   end
//   else begin
//     case (o_opcode)
//       `OPCODE_JALR  : o_op3 = i_pc + 4;
//       `OPCODE_BEQ   : o_op3 = i_pc + imm;
//       `OPCODE_CSR   : o_op3 = i_csr_rdata;
//       default       : o_op3 = 0;
//     endcase
//   end
// end

// // ------------- csr -----------------

// // o_csr_op
// always @(*) begin
//   if (i_disable) begin
//     o_csr_op = `CSROP_NONE;
//   end
//   else begin
//     if (o_opcode == `OPCODE_CSR) begin
//       case (o_funct3)
//         `FUNCT3_CSRRW   : o_csr_op = `CSROP_READ_WRITE;
//         `FUNCT3_CSRRS   : o_csr_op = `CSROP_READ_SET;
//         `FUNCT3_CSRRC   : o_csr_op = `CSROP_READ_CLEAR;
//         `FUNCT3_CSRRWI  : o_csr_op = `CSROP_READ_WRITE;
//         `FUNCT3_CSRRSI  : o_csr_op = `CSROP_READ_SET;
//         `FUNCT3_CSRRCI  : o_csr_op = `CSROP_READ_CLEAR;
//         default         : o_csr_op = `CSROP_NONE;
//       endcase
//     end
//     else begin
//       o_csr_op = `CSROP_NONE;
//     end
//   end
// end

// // o_csr_addr
// assign o_csr_addr = i_inst[31 : 20];

// // csr_zimm
// wire [`BUS_64] csr_zimm = {{60{i_inst[19]}}, i_inst[18:15]};

// // o_csr_wdata
// always@(*) begin
//   if (o_opcode == `OPCODE_CSR) begin
//     case (o_funct3)
//       `FUNCT3_CSRRW   : o_csr_wdata = i_rs1_data;
//       `FUNCT3_CSRRS   : o_csr_wdata = i_rs1_data;
//       `FUNCT3_CSRRC   : o_csr_wdata = i_rs1_data;
//       `FUNCT3_CSRRWI  : o_csr_wdata = csr_zimm;
//       `FUNCT3_CSRRSI  : o_csr_wdata = csr_zimm;
//       `FUNCT3_CSRRCI  : o_csr_wdata = csr_zimm;
//       default         : o_csr_wdata = 0;
//     endcase
//   end
//   else begin
//     o_csr_wdata = 0;
//   end
// end

// // memaction
// always@(*) begin
//   if (i_disable) begin
//     o_memaction = `MEM_ACTION_NONE;
//   end
//   else begin
//     case (o_opcode)
//       `OPCODE_LB    : o_memaction = `MEM_ACTION_LOAD;
//       `OPCODE_SB    : o_memaction = `MEM_ACTION_STORE;
//       default       : o_memaction = `MEM_ACTION_NONE;
//     endcase
//   end
// end

// // 让REF跳过指令比对
// wire mem_addr_is_device = (o_memaddr & ~(64'hFFF)) == 64'h2000_0000;

// // 某些自定义指令，需要通知difftest跳过比对（提交，但不对比）
// assign o_skipcmt = 
//   (i_inst == 32'h7b)                 // putch
//   | (o_opcode == `OPCODE_CSR)   
//   | mem_addr_is_device
//   ;


endmodule
