package alu_sequence_pkg;
    import macro_pkg::*;
    import alu_trans_pkg::*;

    class alu_sequence;
        mailbox #(alu_transaction) seq_mbx;
        int num_transactions;
        alu_transaction tr;

        function new(mailbox #(alu_transaction) seq_mbx, int num_transactions = 300);
            this.seq_mbx = seq_mbx;
            this.num_transactions = num_transactions;
            tr = new();
        endfunction

        task run();
            repeat(num_transactions) begin
                assert(tr.randomize());
                seq_mbx.put(tr);
            end
        endtask
    endclass
endpackage