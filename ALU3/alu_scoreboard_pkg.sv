package alu_scoreboard_pkg;
    import macro_pkg::*;
    import alu_trans_pkg::*;

    class alu_scoreboard;
        function void check_result(input alu_transaction tr_dut, tr_ref);
            if (tr_dut.alu !== tr_ref.alu) begin
                $display("Incorrect alu!, %t", $time);
                incorrect_count = incorrect_count +1;
            end	
            else if (tr_dut.valid_out !== tr_ref.valid_out) begin
                $display("Incorrect valid_out!, %t", $time);
                incorrect_count = incorrect_count +1;
            end	
            else if (tr_dut.zero !== tr_ref.zero) begin
                $display("Incorrect zero flag!, %t", $time);
                incorrect_count = incorrect_count +1;
            end
            else begin
                $display("Correct result, %t", $time);	
                correct_count = correct_count +1;
            end      
        endfunction
    endclass
endpackage