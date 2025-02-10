package alu_driver_pkg;
    import macro_pkg::*;
    import alu_trans_pkg::*;

    class alu_driver;
        virtual alu_interface.DRV vif;
        mailbox #(alu_transaction) drv_mbx;

        function new(virtual alu_interface.DRV vif, mailbox #(alu_transaction) drv_mbx);
            this.vif = vif;
            this.drv_mbx = drv_mbx;
        endfunction

        task run();
            alu_transaction tr;
            forever begin
                @(posedge vif.clk);
                drv_mbx.get(tr);
                vif.reset <= tr.reset;
                vif.a <= tr.a;
                vif.b <= tr.b;
                vif.cin <= tr.cin;
                vif.ctl <= tr.ctl;
                vif.valid_in <= tr.valid_in;
            end
        endtask
    endclass
endpackage