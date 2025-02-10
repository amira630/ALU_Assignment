import macro_pkg::*;
import alu_trans_pkg::*;
import alu_env_pkg::*;
import alu_sequence_pkg::*;

module alu_tb(alu_interface intf);

/////////////////////////////////////////////////////////
/////////// Testbench Signal Declaration ////////////////
/////////////////////////////////////////////////////////

logic       clk, reset, valid_in, cin, valid_out, carry, zero;    
logic [3:0] a, b, alu;     
opcode_e    opcode, ctl;

assign clk           = intf.clk;
assign alu           = intf.alu;
assign zero          = intf.zero;
assign carry         = intf.carry;
assign valid_out     = intf.valid_out;
assign intf.reset    = reset;
assign intf.valid_in = valid_in;
assign intf.cin      = cin;
assign intf.a        = a;
assign intf.b        = b;
assign intf.ctl      = ctl;

////////////////////////////////////////////////////////
/////////// Applying Stimulus on Inputs //////////////// 
////////////////////////////////////////////////////////

alu_transaction tr_tb;
alu_environment env;

int num_transactions = 300;

initial begin
    tr_tb = new();
    initialize();
    
    env = new(intf, num_transactions);
    env.run();
    
    wait(test_finshed);
    $display("Simulation ended at time %0t", $time);
    $display("Total correct cases: %0d", correct_count);
    $display("Total incorrect cases: %0d", incorrect_count);
    $finish;
end

////////////////////////////////////////////////////////
/////////////////////// TASKS //////////////////////////
////////////////////////////////////////////////////////

/////////////// Signals Initialization //////////////////

task initialize;
    begin
        valid_in = 1'b0;
        cin = 1'b0;
        a = 4'b0;
        b = 4'b0;
        ctl = opcode_e'(4'b0000);

        correct_count = 32'b0; 
        incorrect_count = 32'b0;

        $display("Simulation started at time %0t", $time);
        resetting();
    end
endtask

///////////////////////// RESET /////////////////////////

task resetting;
    begin
        reset = 1;
        @(negedge clk)
        reset = 0;
        @(negedge clk)
        reset = 1;
    end
endtask

endmodule