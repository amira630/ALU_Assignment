package alu_monitor_pkg;
    import macro_pkg::*;
    import alu_trans_pkg::*;
    import alu_coverage_collector_pkg::*;
    import alu_scoreboard_pkg::*;

    class alu_monitor;
        virtual alu_interface.MONITOR vif;
        alu_transaction tr_dut, tr_ref;
        alu_scoreboard sb;
        alu_coverage_collector cov;
        mailbox #(alu_transaction) mon_mbx;

        function new(virtual alu_interface.MONITOR vif, mailbox #(alu_transaction) mon_mbx);
            this.vif = vif;
            this.mon_mbx = mon_mbx;
            tr_dut = new();
            tr_ref = new();
            sb = new();
            cov = new();
        endfunction

        task run();
            forever @(negedge vif.clk) begin
                // Sample DUT outputs
                tr_dut.reset = vif.reset;
                tr_dut.a = vif.a;
                tr_dut.b = vif.b;
                tr_dut.cin = vif.cin;
                tr_dut.ctl = vif.ctl;
                tr_dut.valid_in = vif.valid_in;
                tr_dut.valid_out = vif.valid_out;
                tr_dut.alu = vif.alu;
                tr_dut.carry = vif.carry;
                tr_dut.zero = vif.zero;

                // Sample reference model outputs
                tr_ref.reset = vif.reset;
                tr_ref.a = vif.a;
                tr_ref.b = vif.b;
                tr_ref.cin = vif.cin;
                tr_ref.ctl = vif.ctl;
                tr_ref.valid_in = vif.valid_in;
                tr_ref.valid_out = vif.valid_out_ref;
                tr_ref.alu = vif.alu_ref;
                tr_ref.carry = vif.carry_ref;
                tr_ref.zero = vif.zero_ref;
                
                fork
                    cov.sample_data(tr_dut);
                    sb.check_result(tr_dut, tr_ref);
                    mon_mbx.put(tr_dut);
                join_none
                
                if (test_finshed) break;
            end
        endtask
    endclass
endpackage