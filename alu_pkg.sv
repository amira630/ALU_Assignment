package alu_pkg;

typedef enum bit [3:0] {SEL, INC, DEC, ADD, ADD_c, SUB, SUB_b, AND, OR, XOR, SHIFT_L, SHIFT_R, ROTATE_L, ROTATE_R, invalid_1, invalid_2} opcode_e;

    class random_class;
        rand bit rst, cin,  valid_in;
        rand bit [3:0] a,b;
        randc opcode_e ctl;
        bit carry, zero, valid_out;
        bit [3:0] alu;

        // constraint 1: Reset
        constraint rst_c {
            rst dist {0:/1, 1:/99};  //ALU_1
        }
        
        // constraint 2: cin
        constraint cin_c {
            cin dist {0:/70, 1:/30};
        }
        
        // Constraint 3: Control signal distribution
        constraint opcode_c {
            ctl inside {[SEL:XOR], [invalid_1:invalid_2]};
        }

        //constraint opcode_c {ctl dist {[SEL:XOR]:/90, [SHIFT_L:ROTATE_R]:/10};}
        //constraint opcode_c {ctl dist {[SEL:XOR]:/90, [invalid_1:invalid_2]:/10};}

        // Constraint 4: Valid_in
        constraint valid_in_c {
            valid_in dist {0:/10, 1:/90};
        }
        
        // constraint 5
        constraint a_b_c {
            a dist {0:/10, [4'b0001:4'b1110]:/50, 4'b1111:/40};  // Allow 0 in 10% of cases   //ALU_2
            b dist {0:/10, [4'b0001:4'b1110]:/50, 4'b1111:/40};  // Allow 0 in 10% of cases   //ALU_2 ALU_3
        }

        // constraint 6
        constraint a_b_overflow {
            if(ctl == SUB_b && cin)
                a >= b + 1;
            else if (ctl == SUB || ctl == SUB_b)  
                a >= b;  
            else if(ctl == INC)
                b < 4'hF;
            else if(ctl == DEC)
                b > 4'b0;    
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
                bins valid_input = {1};
                bins invalid_input = {0};
            }
            
            // Coverpoint for ALU control signal (ensure all operations are exercised)
            ctl_cp: coverpoint ctl {
                bins all_ops[] = {[SEL:XOR]}; // Cover all ALU operations
                bins invalid_op[] = {[invalid_1:invalid_2]}; // Cover invalid operations
            }

            // Coverpoints for ALU input values (track different data patterns)
            a_cp: coverpoint a {
                bins a_zero = {4'b0000};          // Test zero input
                bins a_ones = {4'b1111};          // Test all ones
                bins a_mid = {[4'b0111:4'b1000]}; // Test middle range values
                bins a_walkingones[] = {4'b0001,4'b0010,4'b0100,4'b1000};
                bins a_default = default;          // Test other values
            }

            b_cp: coverpoint b {
                bins b_zero = {4'b0000};          // Test zero input
                bins b_ones = {4'b1111};          // Test all ones
                bins b_mid = {[4'b0111:4'b1000]}; // Test middle range values
                bins b_walkingones[] = {4'b0001, 4'b0010, 4'b0100, 4'b1000};
                bins b_default = default;          // Test other values
            }

            // Coverpoint for ALU Operations
            ALU_cp: coverpoint ctl {
                // bins Bins_shift[] = {[SHIFT_L:ROTATE_R]};
                bins Bins_arith[] = {[ADD:SUB_b]};
                bins Bins_B[] = {[SEL:DEC]};
                bins Bins_bitwise[] = {[AND:XOR]};
                illegal_bins Bins_invalid = {[invalid_1:invalid_2]};
                bins opcode_default = default;          // Test other values
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
                bins valid_cases = {1} iff(rst && valid_in && (ctl != invalid_1) && (ctl != invalid_1));
                bins invalid_cases = {0};
            }   

            // Cross Coverage
            a_b_arith: cross a_cp, b_cp, ALU_cp{
                bins abop  = ( (binsof(a_cp.a_ones) || binsof(a_cp.a_zero)) &&  (binsof(b_cp.b_ones) || binsof(b_cp.b_zero)) && binsof(ALU_cp.Bins_arith));
                option.cross_auto_bin_max = 0;
            }  
            a_b_arithwc: cross cin_cp, ALU_cp{
                bins abopwc  = (binsof(cin_cp.high) && binsof(ALU_cp.Bins_arith) intersect{ADD_c, SUB_b});
                option.cross_auto_bin_max = 0;
            }
            a_b_bitwise: cross a_cp, b_cp, ALU_cp{
                bins ab_bitab = (binsof(ALU_cp.Bins_bitwise) && binsof(a_cp.a_walkingones) && binsof(b_cp.b_walkingones));
                bins ab_bita = (binsof(ALU_cp.Bins_bitwise) && binsof(a_cp.a_walkingones));
                bins ab_bitb = (binsof(ALU_cp.Bins_bitwise) && binsof(b_cp.b_walkingones));
                option.cross_auto_bin_max = 0;
            }

        endgroup

        function new();
            alu_cvr = new();
            //ctl = SEL;
        endfunction
    endclass
endpackage