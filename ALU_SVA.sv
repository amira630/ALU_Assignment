package alu_assertions;

    `include "svunit_defines.svh"

    // Import necessary types
    import svunit_pkg::svunit_testcase;

    class alu_test;
        // Virtual interface to access the ALU
        virtual alu_if vif;

        function new(virtual alu_if vif);
            this.vif = vif;
        endfunction

        // Assertions to check ALU operations
        property p_select_data;
            @(posedge vif.clk) disable iff (vif.reset)
            vif.valid_in && vif.ctl == 4'b0000 |-> vif.alu == vif.b;
        endproperty
        a_select_data: assert property (p_select_data);

        property p_increment;
            @(posedge vif.clk) disable iff (vif.reset)
            vif.valid_in && vif.ctl == 4'b0001 |-> vif.alu == (vif.b + 1);
        endproperty
        a_increment: assert property (p_increment);

        property p_decrement;
            @(posedge vif.clk) disable iff (vif.reset)
            vif.valid_in && vif.ctl == 4'b0010 |-> vif.alu == (vif.b - 1);
        endproperty
        a_decrement: assert property (p_decrement);

        property p_add_without_carry;
            @(posedge vif.clk) disable iff (vif.reset)
            vif.valid_in && vif.ctl == 4'b0011 |-> vif.alu == (vif.a + vif.b);
        endproperty
        a_add_without_carry: assert property (p_add_without_carry);

        property p_add_with_carry;
            @(posedge vif.clk) disable iff (vif.reset)
            vif.valid_in && vif.ctl == 4'b0100 |-> vif.alu == (vif.a + vif.b + vif.cin);
        endproperty
        a_add_with_carry: assert property (p_add_with_carry);

        property p_sub_without_borrow;
            @(posedge vif.clk) disable iff (vif.reset)
            vif.valid_in && vif.ctl == 4'b0101 |-> vif.alu == (vif.a - vif.b);
        endproperty
        a_sub_without_borrow: assert property (p_sub_without_borrow);

        property p_sub_with_borrow;
            @(posedge vif.clk) disable iff (vif.reset)
            vif.valid_in && vif.ctl == 4'b0110 |-> vif.alu == (vif.a - vif.b - vif.cin);
        endproperty
        a_sub_with_borrow: assert property (p_sub_with_borrow);

        property p_and;
            @(posedge vif.clk) disable iff (vif.reset)
            vif.valid_in && vif.ctl == 4'b0111 |-> vif.alu == (vif.a & vif.b);
        endproperty
        a_and: assert property (p_and);

        property p_or;
            @(posedge vif.clk) disable iff (vif.reset)
            vif.valid_in && vif.ctl == 4'b1000 |-> vif.alu == (vif.a | vif.b);
        endproperty
        a_or: assert property (p_or);

        property p_xor;
            @(posedge vif.clk) disable iff (vif.reset)
            vif.valid_in && vif.ctl == 4'b1001 |-> vif.alu == (vif.a ^ vif.b);
        endproperty
        a_xor: assert property (p_xor);

        property p_shift_left;
            @(posedge vif.clk) disable iff (vif.reset)
            vif.valid_in && vif.ctl == 4'b1010 |-> vif.alu == (vif.a << 1);
        endproperty
        a_shift_left: assert property (p_shift_left);

        property p_shift_right;
            @(posedge vif.clk) disable iff (vif.reset)
            vif.valid_in && vif.ctl == 4'b1011 |-> vif.alu == (vif.a >> 1);
        endproperty
        a_shift_right: assert property (p_shift_right);

        property p_rotate_left;
            @(posedge vif.clk) disable iff (vif.reset)
            vif.valid_in && vif.ctl == 4'b1100 |-> vif.alu == {vif.a[2:0], vif.a[3]};
        endproperty
        a_rotate_left: assert property (p_rotate_left);

        property p_rotate_right;
            @(posedge vif.clk) disable iff (vif.reset)
            vif.valid_in && vif.ctl == 4'b1101 |-> vif.alu == {vif.a[0], vif.a[3:1]};
        endproperty
        a_rotate_right: assert property (p_rotate_right);

    endclass

endpackage
