package alu_coverage_collector_pkg;
    import macro_pkg::*;
    import alu_trans_pkg::*;

    class alu_coverage_collector;
        alu_transaction trans;

        // COVERGROUP
        covergroup alu_cvr;
            // Coverpoint for Reset
            rst_cp: coverpoint trans.reset {
                bins asserted = {0};  // Reset active
                bins deasserted = {1}; // Reset inactive
            }
            
            // Coverpoint for Carry-in signal
            cin_cp: coverpoint trans.cin {
                bins low = {0};
                bins high = {1};
            }

            // Coverpoint for Valid-in signal
            valid_in_cp: coverpoint trans.valid_in {
                bins valid_input = {1};
                bins invalid_input = {0};
            }
            
            // Coverpoint for ALU control signal (ensure all operations are exercised)
            ctl_cp: coverpoint trans.ctl {
                bins all_ops[] = {[SEL:XOR]}; // Cover all ALU operations
                bins invalid_op[] = {[invalid_1:invalid_2]}; // Cover invalid operations
            }

            // Coverpoints for ALU input values (track different data patterns)
            a_cp: coverpoint trans.a {
                bins a_zero = {4'b0000};          // Test zero input
                bins a_ones = {4'b1111};          // Test all ones
                bins a_mid = {[4'b0111:4'b1000]}; // Test middle range values
                bins a_walkingones[] = {4'b0001,4'b0010,4'b0100,4'b1000};
                bins a_default = default;          // Test other values
            }

            b_cp: coverpoint trans.b {
                bins b_zero = {4'b0000};          // Test zero input
                bins b_ones = {4'b1111};          // Test all ones
                bins b_mid = {[4'b0111:4'b1000]}; // Test middle range values
                bins b_walkingones[] = {4'b0001, 4'b0010, 4'b0100, 4'b1000};
                bins b_default = default;          // Test other values
            }

            // Coverpoint for ALU Operations
            ALU_cp: coverpoint trans.ctl {
                // bins Bins_shift[] = {[SHIFT_L:ROTATE_R]};
                bins Bins_arith[] = {[ADD:SUB_b]};
                bins Bins_B[] = {[SEL:DEC]};
                bins Bins_bitwise[] = {[AND:XOR]};
                illegal_bins Bins_invalid = {[invalid_1:invalid_2]};
                bins opcode_default = default;          // Test other values
            }            
            
            // Coverpoint for Carry-out
            carry_cp: coverpoint trans.carry {
                bins carry_0 = {0};
                bins carry_1 = {1};
            }

            // Coverpoint for Zero flag
            zero_cp: coverpoint trans.zero {
                bins zero_set = {1};
                bins zero_unset = {0};
            }

            // Coverpoint for valid_out
            valid_out_cp: coverpoint trans.valid_out {
                bins valid_cases = {1} iff(trans.reset && trans.valid_in && (trans.ctl != invalid_1) && (trans.ctl != invalid_1));
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
            trans = new();
            //ctl = SEL;
        endfunction

        function void sample_data(input alu_transaction tr);
            trans = tr;
            alu_cvr.sample();
        endfunction
    endclass
endpackage