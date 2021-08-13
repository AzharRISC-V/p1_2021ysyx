// pipeline CPU
`timescale 1ns/1ns
`include "def.v"

module pcpu(
    input clk,                  // clock
    input ena,                  // enable CPU
    input rst_n,                // reset signal, Low is valid
    input start,                // start CPU
    input [15:0] i_datain,      // instruction data in
    input [15:0] d_datain,      // data data in
    output [7:0] i_addr,        // instruction address
    output [7:0] d_addr,        // data address
    output d_we,                // data write enable
    output [15:0] d_dataout     // data data output
);

    reg cf_buf;
    reg [15:0] ALUo;            // ALU output
    reg state, next_state;      // state of CPU
    reg zf,nf,cf,dw;            // Zero flag, Negative flag, Carry flag, Data Write Eanble flag
    reg [7:0] pc;
    reg [15:0] id_ir, ex_ir, mem_ir, wb_ir;     // Instructon Decode, Execute, Memeory, Write Back
    reg [15:0] reg_A, reg_B, reg_C, reg_C1, smdr, smdr1;    // smdr: data for save memroy directly
    reg [15:0] gr[7:0];         // general registers
    wire branch_flag;           // need branch jump? 

    /******************** CPU Control *******************/
    always @(posedge clk) begin
        if (!rst_n)
            state <= `idle;
        else
            state <= next_state;
    end

    always @(*) begin
        case (state)
            `idle:
                if (ena && start)
                    next_state <= `exec;
                else
                    next_state <= `idle;
            `exec:
                if (!ena || (wb_ir[15:11] == `HALT))
                    next_state <= `idle;
                else
                    next_state <= `exec;
            default:
                next_state <= `idle;
        endcase
    end

    /******************** IF: Instruction Fetch Stage *******************/
    assign i_addr = pc;
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Clear all output registers and wires at this stage when got reset signal
            id_ir <= {`NOP, 11'b000_0000_0000};
            pc <= 8'b0000_0000;
        end
        else if (state == `exec) begin
            id_ir <= i_datain;

            if (branch_flag)
                pc <= reg_C[7:0];
            else
                pc <= pc + 1;
        end
        else
            id_ir <= id_ir;
    end

    /******************** ID: Instruction Decode Stage *******************/
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ex_ir <= {`NOP, 11'b000_0000_0000};
            reg_A <= 16'b0000_0000_0000_0000;
            reg_B <= 16'b0000_0000_0000_0000;
            smdr <= 16'b0000_0000_0000_0000;
        end
        else if (state == `exec) begin
            ex_ir <= id_ir;

            if (id_ir[15:11] == `STORE)
                smdr <= gr[id_ir[10:8]];
            else
                smdr <= smdr;
            
            if (id_ir[15:11] == `JUMP)
                reg_A <= 16'd0;
            else if (I_R1_TYPE(id_ir[15:11]))
                reg_A <= gr[id_ir[10:8]];
            else if (I_R2_TYPE(id_ir[15:11]))
                reg_A <= gr[id_ir[6:4]];
            else
                reg_A <= reg_A;
            
            if (I_V3_TYPE(id_ir[15:11]))
                reg_B <= {12'd0, id_ir[3:0]};
            else if (I_ZEROV2V3_TYPE(id_ir[15:11]))
                reg_B <= {8'd0, id_ir[7:0]};
            else if (I_V2V3ZERO_TYPE(id_ir[15:11]))
                reg_B <= {id_ir[7:0], 8'd0};
            else if (I_R3_TYPE(id_ir[15:11]))
                reg_B <= gr[id_ir[2:0]];
            else
                reg_B <= reg_B;
        end
    end

    /******************** EX: Execute Stage *******************/
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem_ir <= {`NOP, 11'b000_0000_0000};
            reg_C <= 16'b0000_0000_0000_0000;
            smdr1 <= 16'b0000_0000_0000_0000;
            dw <= 1'b0;
            zf <= 1'b0;
            nf <= 1'b0;
            cf <= 1'b0;
        end
        else if (state == `exec) begin
            reg_C <= ALUo;
            mem_ir <= ex_ir;

            // Handle zf/nf/cf flag
            if ((ex_ir[15:11] == `LDIH)
                || (ex_ir[15:11] == `SUIH)
                || (ex_ir[15:11] == `ADD)
                || (ex_ir[15:11] == `ADDI)
                || (ex_ir[15:11] == `ADDC)
                || (ex_ir[15:11] == `SUB)
                || (ex_ir[15:11] == `SUBI)
                || (ex_ir[15:11] == `SUBC)
                || (ex_ir[15:11] == `CMP)
                || (ex_ir[15:11] == `AND)
                || (ex_ir[15:11] == `OR)
                || (ex_ir[15:11] == `XOR)
                || (ex_ir[15:11] == `SLL)
                || (ex_ir[15:11] == `SRL)
                || (ex_ir[15:11] == `SLA)
                || (ex_ir[15:11] == `SRA)) begin
                cf <= cf_buf;
                if (ALUo == 16'd0)
                    zf <= 1'b1;
                else
                    zf <= 1'b0;

                if (ALUo[15] == 1'b1)
                    nf <= 1'b1;
                else
                    nf <= 1'b0;
            end
            else begin
                zf <= zf;
                nf <= nf;
                cf <= cf;
            end

            // Handle Data for store to memroy
            if (ex_ir[15:11] == `STORE) begin
                dw <= 1'b1;
                smdr1 <= smdr;
            end
            else begin
                dw <= 1'b0;
                smdr1 <= smdr1;
            end

        end
    end

    // execute instructions
    always @(*) begin
        if (ex_ir[15:11] == `AND) begin
            cf_buf <= 1'b0;
            ALUo <= reg_A & reg_B;
        end

        else if (ex_ir[15:11] == `OR) begin
            cf_buf <= 1'b0;
            ALUo <= reg_A | reg_B;
        end

        else if (ex_ir[15:11] == `XOR) begin
            cf_buf <= 1'b0;
            ALUo <= reg_A ^ reg_B;
        end

        else if (ex_ir[15:11] == `SLL)
            {cf_buf, ALUo[15:0]} <= {cf, reg_A[15:0]} << reg_B[3:0];
        else if (ex_ir[15:11] == `SRL)
            {ALUo[15:0], cf_buf} <= {reg_A[15:0], cf} >> reg_B[3:0];
        else if (ex_ir[15:11] == `SLA)
            {cf_buf, ALUo[15:0]} <= {cf, reg_A[15:0]} << reg_B[3:0];
        else if (ex_ir[15:11] == `SRA)
            {ALUo[15:0], cf_buf} <= {reg_A[15:0], cf} >> reg_B[3:0];
        else if ((ex_ir[15:11] == `SUB)
            || (ex_ir[15:11] == `SUBI)
            || (ex_ir[15:11] == `CMP)
            || (ex_ir[15:11] == `SUIH))
            {cf_buf, ALUo} <= reg_A - reg_B;
        else if (ex_ir[15:11] == `SUBC)
            {cf_buf, ALUo} <= reg_A - reg_B - cf;
        else if (ex_ir[15:11] == `ADDC)
            {cf_buf, ALUo} <= reg_A + reg_B + cf;
        else
            {cf_buf, ALUo} <= reg_A + reg_B;

    end


    /******************** MEM: Memory Operation *******************/
    assign d_addr = reg_C[7:0];
    assign d_we = dw;
    assign d_dataout = smdr1;
    assign branch_flag = ((mem_ir[15:11] == `JUMP)
        || (mem_ir[15:11] == `JMPR)
        || ((mem_ir[15:11] == `BZ) && (zf == 1'b1))
        || ((mem_ir[15:11] == `BNZ) && (zf == 1'b0))
        || ((mem_ir[15:11] == `BN) && (nf == 1'b1))
        || ((mem_ir[15:11] == `BNN) && (nf == 1'b0))
        || ((mem_ir[15:11] == `BC) && (cf == 1'b1))
        || ((mem_ir[15:11] == `BNC) && (cf == 1'b0)));

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wb_ir <= {`NOP, 11'b000_0000_0000};
            reg_C1 <= 16'b0000_0000_0000_0000;
        end
        else if (state == `exec) begin
            wb_ir <= mem_ir;

            if (mem_ir[15:11] == `LOAD)
                reg_C1 <= d_datain;
            else
                reg_C1 <= reg_C;
        end
    end

    
    /******************** WB: Write Back *******************/

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            gr[0] <= 16'd0;
            gr[1] <= 16'd0;
            gr[2] <= 16'd0;
            gr[3] <= 16'd0;
            gr[4] <= 16'd0;
            gr[5] <= 16'd0;
            gr[6] <= 16'd0;
            gr[7] <= 16'd0;
        end
        else if (state == `exec) begin
            if (I_REG_TYPE(wb_ir[15:11]))
                gr[wb_ir[10:8]] <= reg_C1;
        end
    end

    
    /******************** Judge an instruction whether alter the value of a register *******************/
    function I_REG_TYPE;
        input [4:0] op;
        begin
            I_REG_TYPE = ((op == `LOAD)
                || (op == `LDIH)
                || (op == `ADD)
                || (op == `ADDI)
                || (op == `ADDC)
                || (op == `SUIH)
                || (op == `SUB)
                || (op == `SUBI)
                || (op == `SUBC)
                || (op == `AND)
                || (op == `OR)
                || (op == `XOR)
                || (op == `SLL)
                || (op == `SRL)
                || (op == `SLA)
                || (op == `SRA));
        end
    endfunction


    /******************** R1 as reg_A *******************/
    function I_R1_TYPE;
        input [4:0] op;
        begin
            I_R1_TYPE = ((op == `LDIH)
                || (op == `SUIH)
                || (op == `SUIH)
                || (op == `SUBI)
                || (op == `JMPR)
                || (op == `BZ)
                || (op == `BNZ)
                || (op == `BN)
                || (op == `BNN)
                || (op == `BC)
                || (op == `BNC));
        end
    endfunction

    /******************** R2 as reg_A *******************/
    function I_R2_TYPE;
        input [4:0] op;
        begin
            I_R2_TYPE = ((op == `LOAD)
                || (op == `STORE)
                || (op == `ADD)
                || (op == `ADDC)
                || (op == `SUB)
                || (op == `SUBC)
                || (op == `CMP)
                || (op == `AND)
                || (op == `OR)
                || (op == `XOR)
                || (op == `SLL)
                || (op == `SRL)
                || (op == `SLA)
                || (op == `SRA));
        end
    endfunction

    /******************** R3 as reg_B *******************/
    function I_R3_TYPE;
        input [4:0] op;
        begin
            I_R3_TYPE = ((op == `ADD)
                || (op == `ADDC)
                || (op == `SUB)
                || (op == `SUBC)
                || (op == `CMP)
                || (op == `AND)
                || (op == `OR)
                || (op == `XOR));
        end
    endfunction

    /******************** val3 as reg_A *******************/
    function I_V3_TYPE;
        input [4:0] op;
        begin
            I_V3_TYPE = ((op == `LOAD)
                || (op == `STORE)
                || (op == `SLL)
                || (op == `SRL)
                || (op == `SLA)
                || (op == `SRA));
        end
    endfunction

    /******************** {8'b0,val2,val3} as reg_B *******************/
    function I_ZEROV2V3_TYPE;
        input [4:0] op;
        begin
            I_ZEROV2V3_TYPE = ((op == `ADDI)
                    || (op == `SUBI)
                    || (op == `JUMP)
                    || (op == `JMPR)
                    || (op == `BZ)
                    || (op == `BNZ)
                    || (op == `BN)
                    || (op == `BNN)
                    || (op == `BC)
                    || (op == `BNC));
        end
    endfunction

    /******************** {val2,val3,8'b0} as reg_B *******************/
    function I_V2V3ZERO_TYPE;
        input [4:0] op;
        begin
            I_V2V3ZERO_TYPE = ((op == `LDIH)
                    || (op == `SUIH));
        end
    endfunction

endmodule
