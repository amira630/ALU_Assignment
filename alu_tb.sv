//import Q1::*;//
`timescale 1ns/1ps

typedef enum bit [3:0] {SEL, INC, DEC, ADD, ADD_c, SUB, SUB_b, AND, OR, XOR, SHIFT_L, SHIFT_R, ROTATE_L, ROTATE_R} opcode_e;

module alu_tb();

/////////////////////////////////////////////////////////
///////////////////// Parameters ////////////////////////
/////////////////////////////////////////////////////////

parameter CLOCK_PERIOD  = 2;

/////////////////////////////////////////////////////////
/////////// Testbench Signal Declaration ////////////////
/////////////////////////////////////////////////////////

logic       clk_tb, reset_tb, valid_in_tb, cin_tb, valid_out_tb, carry_tb, zero_tb;    
logic [3:0] a_tb, b_tb, ctl_tb, alu_tb;     
opcode_e    opcode_tb;

logic       clk_g, reset_g, valid_in_g, cin_g, valid_out_g, carry_g, zero_g;    
logic [3:0] a_g, b_g, ctl_g, alu_g;  
opcode_e    opcode_g;

assign opcode_tb = ctl_tb;
assign opcode_g  = ctl_g;

////////////////////////////////////////////////////////
////////////////////// Counters ////////////////////////
////////////////////////////////////////////////////////

integer correct_count, incorrect_count;

////////////////////////////////////////////////////////
/////////////////// DUT Instantation ///////////////////
////////////////////////////////////////////////////////

alu DUT(clk_tb, reset_tb, valid_in_tb, a_tb, b_tb, cin_tb, ctl_tb, valid_out_tb, alu_tb, carry_tb, zero_tb);

////////////////////////////////////////////////////////
////////////////// Clock Generator  ////////////////////
////////////////////////////////////////////////////////

//q1 inputs = new();//

always #(CLOCK_PERIOD/2) clk_tb = ~clk_tb;

always #(CLOCK_PERIOD/2) clk_g = ~clk_g;

////////////////////////////////////////////////////////
/////////// Applying Stimulus on Inputs //////////////// 
////////////////////////////////////////////////////////

initial begin
    initialize();
    for (int i = 0; i < 1200; i++) begin
        
    end
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
        ctl_tb = 4'b0;      ctl_g = 4'b0;

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
		if (alu_tb !== alu_g || valid_out_tb !==valid_out_g || zero_tb !== zero_g) begin
			$display("Incorrect Result!, %t", $time);
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