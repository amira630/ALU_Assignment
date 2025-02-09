`timescale 1ns/1ps

module alu_top ();
    bit clk;

    // Interface
    alu_interface intf (clk);

    // DUT 
    alu dut (intf);

    // TEST
    alu_tb test (intf);

    // Monitor
    alu_monitor monitor (intf);

    // REF
    alu_ref ref_model (intf);

    // SVA
    bind alu alu_SVA SVA_inst(intf);

    // Clock Generation
    initial begin
        clk = 1;
        forever
            #5 clk = ~clk;
    end
    
endmodule