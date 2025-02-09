
import alu_pkg::*;

`timescale 1ns/1ps

module alu_tb();

/////////////////////////////////////////////////////////
///////////////////// Parameters ////////////////////////
/////////////////////////////////////////////////////////

parameter CLOCK_PERIOD  = 10;

/////////////////////////////////////////////////////////
/////////// Testbench Signal Declaration ////////////////
/////////////////////////////////////////////////////////

logic       clk_tb, reset_tb, valid_in_tb, cin_tb, valid_out_tb, carry_tb, zero_tb;    
logic [3:0] a_tb, b_tb, ctl_tb, alu_tb;     
opcode_e    opcode_tb;

logic       clk_g, reset_g, valid_in_g, cin_g, valid_out_g, carry_g, zero_g;    
logic [3:0] a_g, b_g, ctl_g, alu_g;  
opcode_e    opcode_g;

assign opcode_tb = opcode_e'(ctl_tb);
assign opcode_g  = opcode_e'(ctl_g);

////////////////////////////////////////////////////////
////////////////////// Counters ////////////////////////
////////////////////////////////////////////////////////

integer correct_count, incorrect_count;

////////////////////////////////////////////////////////
////////////////////// Random Signals //////////////////
////////////////////////////////////////////////////////

random_class RC;

////////////////////////////////////////////////////////
/////////////////// DUT Instantation ///////////////////
////////////////////////////////////////////////////////

alu DUT(clk_tb, reset_tb, valid_in_tb, a_tb, b_tb, cin_tb, ctl_tb, valid_out_tb, alu_tb, carry_tb, zero_tb);

////////////////////////////////////////////////////////
////////////////// Clock Generator  ////////////////////
////////////////////////////////////////////////////////

always #(CLOCK_PERIOD/2) clk_tb = ~clk_tb;

always #(CLOCK_PERIOD/2) clk_g = ~clk_g;

////////////////////////////////////////////////////////
////////////////////// Assertions //////////////////////
////////////////////////////////////////////////////////

property p_SEL;
    @(posedge clk_tb) disable iff (!reset_tb)
    valid_in_tb && ctl_tb == SEL |=> (alu_tb == $past(b_tb));
endproperty
assert property (p_SEL);
cover property (p_SEL);

property p_INC;
    @(posedge clk_tb) disable iff (!reset_tb)
    valid_in_tb && ctl_tb == INC |=> (alu_tb == ($past(b_tb) + 1)) ;
endproperty
assert property (p_INC);
cover property (p_INC);

property p_DEC;
    @(posedge clk_tb) disable iff (!reset_tb)
    valid_in_tb && ctl_tb == DEC |=> (alu_tb == ($past(b_tb) - 1)) ;
endproperty
assert property (p_DEC);
cover property (p_DEC);

property p_ADD;
    @(posedge clk_tb) disable iff (!reset_tb)
    valid_in_tb && ctl_tb == ADD |=> (alu_tb == ($past(a_tb) + $past(b_tb))) ;
endproperty
assert property (p_ADD);
cover property (p_ADD);

property p_ADD_c;
    @(posedge clk_tb) disable iff (!reset_tb)
    valid_in_tb && ctl_tb == ADD_c |=> (alu_tb == ($past(a_tb) + $past(b_tb) + $past(cin_tb))) ;
endproperty
assert property (p_ADD_c);
cover property (p_ADD_c);

property p_SUB;
    @(posedge clk_tb) disable iff (!reset_tb)
    valid_in_tb && ctl_tb == SUB |=> (alu_tb == ($past(a_tb) - $past(b_tb))) ;
endproperty
assert property (p_SUB);
cover property (p_SUB);

property p_SUB_b;
    @(posedge clk_tb) disable iff (!reset_tb)
    valid_in_tb && ctl_tb == SUB_b |=> (alu_tb == ($past(a_tb) - $past(b_tb) - $past(cin_tb))) ;
endproperty
assert property (p_SUB_b);
cover property (p_SUB_b);

property p_AND;
    @(posedge clk_tb) disable iff (!reset_tb)
    valid_in_tb && ctl_tb == AND |=> (alu_tb == ($past(a_tb) & $past(b_tb))) ;
endproperty
assert property (p_AND);
cover property (p_AND);

property p_OR;
    @(posedge clk_tb) disable iff (!reset_tb)
    valid_in_tb && ctl_tb == OR |=> (alu_tb == ($past(a_tb) | $past(b_tb))) ;
endproperty
assert property (p_OR);
cover property (p_OR);

property p_XOR;
    @(posedge clk_tb) disable iff (!reset_tb)
    valid_in_tb && ctl_tb == XOR |=> (alu_tb == ($past(a_tb) ^ $past(b_tb))) ;
endproperty
assert property (p_XOR);
cover property (p_XOR);

// property p_SHIFT_L;
//     @(posedge clk_tb) disable iff (!reset_tb)
//     valid_in_tb && ctl_tb == SHIFT_L |=> (alu_tb == ($past(a_tb) << 1)) && valid_out_tb;
// endproperty
// assert property (p_SHIFT_L);
// cover property (p_SHIFT_L);

// property p_SHIFT_R;
//     @(posedge clk_tb) disable iff (!reset_tb)
//     valid_in_tb && ctl_tb == SHIFT_R |=> (alu_tb == ($past(a_tb) >> 1)) && valid_out_tb;
// endproperty
// assert property (p_SHIFT_R);
// cover property (p_SHIFT_R);

// property p_ROTATE_L;
//     @(posedge clk_tb) disable iff (!reset_tb)
//     valid_in_tb && ctl_tb == ROTATE_L |=> (alu_tb == {$past(a_tb[2:0]), $past(a_tb[3])}) && valid_out_tb;
// endproperty
// assert property (p_ROTATE_L);
// cover property (p_ROTATE_L);

// property p_ROTATE_R;
//     @(posedge clk_tb) disable iff (!reset_tb)
//     valid_in_tb && ctl_tb == ROTATE_R |=> (alu_tb == {$past(a_tb[0]), $past(a_tb[3:1])}) && valid_out_tb;
// endproperty
// assert property (p_ROTATE_R);
// cover property (p_ROTATE_R);

// property p_CARRY;
//     @(posedge clk_tb) disable iff (!reset_tb)
//     valid_in_tb && (ctl_tb inside {ADD, ADD_c, SUB, SUB_b}) |=> 
//     (carry_tb == ((ctl_tb == ADD || ctl_tb == ADD_c) ? 
//                   (a_tb + b_tb + (ctl_tb == ADD_c ? cin_tb : 0)) >> $bits(alu_tb) :
//                   (a_tb < (b_tb + (ctl_tb == SUB_b ? cin_tb : 0)))) &&
//      valid_out_tb);
// endproperty

property p_CARRY;
    @(posedge clk_tb) disable iff (!reset_tb)
    valid_in_tb && !(ctl_tb inside {ADD, ADD_c, SUB, SUB_b, invalid_1, invalid_2}) |=> ~carry_tb;
endproperty
assert property (p_CARRY);
cover property (p_CARRY);

property p_ZERO;
    @(posedge clk_tb) disable iff (!reset_tb)
    valid_in_tb |=> zero_tb == (alu_tb == 4'b0);
endproperty
assert property (p_ZERO);
cover property (p_ZERO);

property p_Valid_out_off;
    @(posedge clk_tb) disable iff (!reset_tb)
    ~valid_in_tb || ((ctl_tb == invalid_1 || ctl_tb == invalid_2) && valid_in_tb) |=> ~valid_out_tb; 
endproperty
assert property (p_Valid_out_off);
cover property (p_Valid_out_off);

property p_Valid_out_on;
    @(posedge clk_tb) disable iff (!reset_tb)
    valid_in_tb && (ctl_tb != invalid_1 && ctl_tb != invalid_2) |=> valid_out_tb; 
endproperty
assert property (p_Valid_out_on);
cover property (p_Valid_out_on);

property p_Valid_in_off;
    @(posedge clk_tb) disable iff (!reset_tb)
    ~valid_in_tb |=> ($past(alu_tb) == $past(alu_tb,1) && $past(carry_tb) == $past(carry_tb,1) && ~valid_out_tb);
endproperty

////////////////////////////////////////////////////////
/////////// Applying Stimulus on Inputs //////////////// 
////////////////////////////////////////////////////////

initial begin
    RC = new();
    initialize();
    
    // Random check
    repeat(1000) begin
        assert (RC.randomize());
        reset_tb = RC.rst;
        reset_g = RC.rst;
        valid_in_tb = RC.valid_in;
        valid_in_g = RC.valid_in;
        cin_tb = RC.cin;
        cin_g = RC.cin;
        a_tb = RC.a;
        a_g = RC.a;
        b_tb = RC.b;
        b_g = RC.b;
        ctl_tb = RC.ctl;
        ctl_g = RC.ctl;

        RC.carry = carry_tb;
        RC.zero = zero_tb;
        RC.valid_out = valid_out_tb;
        RC.alu = alu_tb;

        RC.alu_cvr.sample();
        check_result();

    end

    $display("total number of errors = %d , total numbers of correct  = %d", incorrect_count, correct_count);
    #5
    $stop;
end

////////////////////////////////////////////////////////
/////////////////////// TASKS //////////////////////////
////////////////////////////////////////////////////////

/////////////// Signals Initialization //////////////////

task initialize;
    begin
        clk_tb = 1'b0;      clk_g = 1'b0;
        valid_in_tb = 1'b0; valid_in_g = 1'b0;
        cin_tb = 1'b0;      cin_g = 1'b0;
        a_tb = 4'b0;        a_g = 4'b0;
        b_tb = 4'b0;        b_g = 4'b0;
        ctl_tb = opcode_e'(4'b0000);      ctl_g = opcode_e'(4'b0000);

        correct_count = 32'b0; 
        incorrect_count = 32'b0;

        $display("Simulation started at time %0t", $time);
        reset();
    end
endtask

///////////////////////// RESET /////////////////////////

task reset;
    begin
        reset_tb = 1; reset_g = 1;
        @(negedge clk_tb)
        reset_tb = 0; reset_g = 0;
        check_result();
        reset_tb = 1; reset_g = 1;
    end
endtask

////////////////// Check Result Response  ////////////////////

task check_result();
    begin
        @(negedge clk_tb)
#1
		if (alu_tb !== alu_g) begin
			$display("Incorrect alu!, %t", $time);
			incorrect_count = incorrect_count +1;
		end	
		else if (valid_out_tb !==valid_out_g) begin
			$display("Incorrect valid_out!, %t", $time);
			incorrect_count = incorrect_count +1;
		end	
		else if (zero_tb !== zero_g) begin
			$display("Incorrect zero flag!, %t", $time);
			incorrect_count = incorrect_count +1;
        end
        else begin
			$display("Correct result, %t", $time);	
			correct_count = correct_count +1;
		end
    end
endtask

////////////////// Reference Model ////////////////////

alu_ref DUT_G(clk_g, reset_g, valid_in_g, a_g, b_g, cin_g, ctl_g, valid_out_g, alu_g, carry_g, zero_g);

endmodule