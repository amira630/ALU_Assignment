package alu_env_pkg;
    import macro_pkg::*;
    import alu_trans_pkg::*;
    import alu_agent_pkg::*;

    class alu_environment;
        alu_agent agent;
        virtual alu_interface vif;

        int num_transactions;

        function new(virtual alu_interface vif, int num_transactions = 300);
            this.vif = vif;
            this.num_transactions = num_transactions; 
            agent = new(vif, num_transactions); // Pass vif and drv_mbx to agent
        endfunction

        task run();
            agent.run();
        endtask
    endclass
endpackage