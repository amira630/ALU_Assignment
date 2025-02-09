import macro_pkg::*;
import alu_trans_pkg::*;
import alu_coverage_collector_pkg::*;
import alu_scoreboard_pkg::*;

module alu_monitor (alu_interface.MONITOR intf);
    
    logic clk, reset, valid_in, cin, valid_out, carry, zero;    
    logic [3:0] a, b, alu;
    logic valid_out_ref, carry_ref, zero_ref;
    logic [3:0] alu_ref; 

    opcode_e ctl;

    assign clk = intf.clk;
    assign reset = intf.reset; 
    assign a = intf.a;
    assign b = intf.b;
    assign cin = intf.cin;
    assign ctl = intf.ctl;
    assign valid_in = intf.valid_in;

    assign valid_out = intf.valid_out; 
    assign alu = intf.alu; 
    assign carry = intf.carry; 
    assign zero = intf.zero;

    assign valid_out_ref = intf.valid_out_ref; 
    assign alu_ref = intf.alu_ref; 
    assign carry_ref = intf.carry_ref; 
    assign zero_ref = intf.zero_ref;

    alu_transaction tr_dut, tr_ref;
    alu_scoreboard sb;
    alu_coverage_collector cov;

    initial begin
        tr_dut = new();
        tr_ref = new();
        sb     = new();
        cov    = new();

        forever begin
            @(negedge clk);
            tr_dut.reset     = reset;
            tr_dut.a         = a;
            tr_dut.b         = b;
            tr_dut.cin       = cin;
            tr_dut.ctl       = ctl;
            tr_dut.valid_in  = valid_in;
            tr_dut.valid_out = valid_out;
            tr_dut.alu       = alu;
            tr_dut.carry     = carry;
            tr_dut.zero      = zero;

            tr_ref.reset     = reset;
            tr_ref.a         = a;
            tr_ref.b         = b;
            tr_ref.cin       = cin;
            tr_ref.ctl       = ctl;
            tr_ref.valid_in  = valid_in;
            tr_ref.valid_out = valid_out_ref;
            tr_ref.alu   = alu_ref;
            tr_ref.carry = carry_ref;
            tr_ref.zero  = zero_ref;

            fork
                begin
                    #0;
                    tr_dut.reset     = reset;
                    tr_dut.ctl       = ctl;
                    tr_dut.valid_in  = valid_in;
                    tr_dut.valid_out = valid_out;
                    tr_dut.alu       = alu;
                    tr_dut.carry     = carry;
                    tr_dut.zero      = zero;

                    tr_ref.valid_out = valid_out_ref;
                    tr_ref.alu   = alu_ref;
                    tr_ref.carry = carry_ref;
                    tr_ref.zero  = zero_ref;

                    cov.sample_data(tr_dut);
                end
                begin
                    sb.check_result(tr_dut, tr_ref);
                end
            join
            if (test_finshed) begin
                $display("The simulation has been finished: Error Count = %0d, Correct Count = %0d", incorrect_count, correct_count);
                $stop;
            end
        end
    end

endmodule

