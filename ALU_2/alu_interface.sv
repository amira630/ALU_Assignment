import macro_pkg::*;

interface alu_interface (input clk);
    logic reset, valid_in, cin, valid_out, carry, zero;    
    logic [3:0] a, b, alu; 
    logic valid_out_ref, carry_ref, zero_ref;
    logic [3:0] alu_ref;

    opcode_e ctl;

    modport DUT (
    input clk, reset, valid_in, cin,
    input a, b, ctl,
    output valid_out, carry, zero,
    output alu
    );

    modport DRV (
    output reset, valid_in, cin,
    output a, b, ctl,
    input clk, valid_out, carry, zero,
    input alu
    );

    modport MONITOR (
    input clk, reset, valid_in, cin, valid_out, carry, zero,  
    input a, b, ctl, alu,  
    input valid_out_ref, carry_ref, zero_ref,
    input alu_ref 
    );

    modport REF (
    input clk, reset, valid_in, cin,
    input a, b, ctl,
    output valid_out_ref, carry_ref, zero_ref,
    output alu_ref
    );
endinterface