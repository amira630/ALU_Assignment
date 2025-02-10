package alu_agent_pkg;
    import alu_trans_pkg::*;
    import alu_driver_pkg::*;
    import alu_monitor_pkg::*;
    
    class alu_agent;
        alu_driver drv;
        alu_monitor mon;
        virtual alu_interface vif;  // Declare vif
        mailbox #(alu_transaction) drv_mbx;     // Declare mailbox
        mailbox #(alu_transaction) mon_mbx;

        int num_transactions;

        function new(virtual alu_interface vif, int num_transactions = 300);
            this.vif = vif;
            this.num_transactions = num_transactions;
            
            drv_mbx = new();
            mon_mbx = new();
            
            drv = new(vif, drv_mbx); // Pass the arguments to the driver
            mon = new(vif, mon_mbx);
        endfunction

        task run();
            fork
                drv.run();
                mon.run();
            join_none
        endtask
    endclass
endpackage