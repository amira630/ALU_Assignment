package alu_sequencer_pkg;
    import macro_pkg::*;
    import alu_trans_pkg::*;

    class alu_sequencer;
        mailbox #(alu_transaction) drv_mbx;
        int num_transactions;
        rand alu_transaction tr;
        
        function new(mailbox #(alu_transaction) drv_mbx, int num_transactions);
            this.drv_mbx = drv_mbx;
            this.num_transactions = num_transactions;
        endfunction

        task run();
            for (int i = 0; i < num_transactions; i++) begin
                tr = new();
                if (!tr.randomize()) begin
                    $fatal("Randomization failed for alu_transaction");
                end
                drv_mbx.put(tr);
            end
        endtask
    endclass
endpackage