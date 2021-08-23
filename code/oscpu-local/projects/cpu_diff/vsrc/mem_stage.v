// // Zhengpu Shi

// `include "defines.v";

// module mem_stage(clk,
//                 rst,
//                 mem_r_addr,
//                 mem_r_ena,
//                 mem_r_data,
//                 mem_w_addr,
//                 mem_w_ena,
//                 mem_w_data);
//     input   wire                        clk;
//     input   wire                        rst;

//     input   wire  [`RAM_ADDR_BUS ]       mem_r_addr;
//     input   wire                        mem_r_ena;
//     output  wire  [`RAM_DATA_BUS ]       mem_r_data;
//     input   wire  [`RAM_ADDR_BUS ]       mem_w_addr;
//     input   wire                        mem_w_ena;
//     output  wire  [`RAM_DATA_BUS ]       mem_w_data;

//     ram Ram(
//     .clk            (clk            ),
//     .rst            (rst            ),
//     .ram_r_addr     (mem_r_addr     ),
//     .ram_r_en       (mem_r_en       ),
//     .ram_r_data     (mem_r_data     ),
//     .ram_w_addr     (mem_w_addr     ),
//     .ram_w_en       (mem_w_en       ),
//     .ram_w_data     (mem_w_data     )
//     );
    
// endmodule
