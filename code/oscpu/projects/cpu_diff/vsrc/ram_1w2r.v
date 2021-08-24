
// module ram_1w2r(
//     input clk,
    
//     input [`BUS_WIDTH]inst_addr,
//     input inst_ena,
//     output [31:0]inst,

//     // DATA PORT
//     input ram_wr_en,
//     input ram_rd_en,
//     input [`BUS_WIDTH]ram_wmask,
//     input [`BUS_WIDTH]ram_addr,
//     input [`BUS_WIDTH]ram_wr_data,
//     output reg [`BUS_WIDTH]ram_rd_data
// );

//     // INST PORT

//     wire[`BUS_WIDTH] inst_2 = ram_read_helper(inst_ena,{3'b000,(inst_addr-64'h0000_0000_8000_0000)>>3});

//     assign inst = inst_addr[2] ? inst_2[63:32] : inst_2[31:0];

//     // DATA PORT 
//     assign ram_rd_data = ram_read_helper(ram_rd_en, {3'b000,(ram_addr-64'h0000_0000_8000_0000)>>3});

//     always @(posedge clk) begin
//         ram_write_helper((ram_addr-64'h0000_0000_8000_0000)>>3, ram_wr_data, ram_wmask, ram_wr_en);
//     end

// endmodule

