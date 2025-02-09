package alu_pkg;

typedef enum bit [3:0] {SEL, INC, DEC, ADD, ADD_c, SUB, SUB_b, AND, OR, XOR, SHIFT_L, SHIFT_R, ROTATE_L, ROTATE_R} opcode_e;

    class random_class;
        rand bit rst, cin,  valid_in;
        rand bit [3:0] a,b;
        rand opcode_e ctl;
        bit carry, zero, valid_out;
        bit [3:0] alu;

        // constraint 1: Reset
        constraint rst_c {rst dist {0:/10, 1:/90};}
        
        // constraint 2: cin
        constraint cin_c {cin dist {0:/70, 1:/30};}
        
        // Constraint 3: Control signal distribution
        //constraint opcode_c {ctl dist {[SEL:XOR]:/90, [SHIFT_L:ROTATE_R]:/10};}
        constraint opcode_c {ctl dist {[SEL:XOR]};}

        // Constraint 4: Valid_in should be 1 only when valid inputs exist
        // "If all inputs are 0, the operation is invalid, so valid_in will be 0"
        constraint valid_in_c {
            valid_in == ((a != 4'b0000) || (b != 4'b0000));
        }
        
        // constraint 5
        constraint a_b_c {
            a dist {0:/10, [4'b0001:4'b1111]:/90};  // Allow 0 in 10% of cases
            b dist {0:/10, [4'b0001:4'b1111]:/90};  // Allow 0 in 10% of cases
        }

        // COVERGROUP
        covergroup alu_cvr;
            // Coverpoint for Reset
            rst_cp: coverpoint rst {
                bins asserted = {0};  // Reset active
                bins deasserted = {1}; // Reset inactive
            }
            
            // Coverpoint for Carry-in signal
            cin_cp: coverpoint cin {
                bins low = {0};
                bins high = {1};
            }

            // Coverpoint for Valid-in signal
            valid_in_cp: coverpoint valid_in {
                bins valid = {1};
                bins invalid = {0};
            }
            
            // Coverpoint for ALU control signal (ensure all operations are exercised)
            ctl_cp: coverpoint ctl {
                bins all_ops[] = {[SEL:XOR]}; // Cover all ALU operations
            }

            // Coverpoints for ALU input values (track different data patterns)
            a_cp: coverpoint a {
                bins zero = {4'b0000};          // Test zero input
                bins ones = {4'b1111};          // Test all ones
                bins mid = {[4'b0111:4'b1000]}; // Test middle range values
                bins random = default;          // Test other values
            }

            b_cp: coverpoint b {
                bins zero = {4'b0000};          // Test zero input
                bins ones = {4'b1111};          // Test all ones
                bins mid = {[4'b0111:4'b1000]}; // Test middle range values
                bins random = default;          // Test other values
            }
            
            // Coverpoint for Carry-out
            carry_cp: coverpoint carry {
                bins carry_0 = {0};
                bins carry_1 = {1};
            }

            // Coverpoint for Zero flag
            zero_cp: coverpoint zero {
                bins zero_set = {1};
                bins zero_unset = {0};
            }

            // Coverpoint for valid_out
            valid_out_cp: coverpoint valid_out {
                bins valid_cases = {1} iff(rst && valid_in && (a != 4'b0000) && (b != 4'b0000));
                bins invalid_cases = {0};
            }   

            // Cross Coverage
            
        endgroup

        function new();
            alu_cvr = new();
            ctl = SEL;
        endfunction
    endclass
endpackage