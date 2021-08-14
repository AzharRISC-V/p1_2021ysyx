module rom(
    input ena, rd,      // enable, read
    input [7:0] addr,
    output [15:0] data
);
    reg [7:0] memory [255:0];

    initial begin
        memory[0] = 'h01;
        memory[1] = 'h02;
        memory[2] = 'h03;
        memory[3] = 'h04;
    end

    // read
    assign data = (ena && rd) ? memory[addr] : 8'hzz;

endmodule