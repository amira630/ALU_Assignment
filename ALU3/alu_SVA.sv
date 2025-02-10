import macro_pkg::*;
module alu_SVA (alu_interface.DUT intf);

    logic clk, reset, valid_in, cin, valid_out, carry, zero;    
    logic [3:0] a, b, ctl, alu;

    assign clk = intf.clk;
    assign reset = intf.reset; 
    assign a = intf.a;
    assign b = intf.b;
    assign cin = intf.cin;
    assign ctl = intf.ctl;
    assign valid_in = intf.valid_in;

    assign valid_out = intf.valid_out; 
    assign alu = intf.alu; 
    assign carry = intf.carry; 
    assign zero = intf.zero;

    ////////////////////////////////////////////////////////
    ////////////////////// Assertions //////////////////////
    ////////////////////////////////////////////////////////

    property p_SEL;
        @(posedge clk) disable iff (!reset)
        valid_in && ctl == SEL |=> (alu == $past(b));
    endproperty
    assert property (p_SEL);
    cover property (p_SEL);

    property p_INC;
        @(posedge clk) disable iff (!reset)
        valid_in && ctl == INC |=> (alu == ($past(b) + 1)) ;
    endproperty
    assert property (p_INC);
    cover property (p_INC);

    property p_DEC;
        @(posedge clk) disable iff (!reset)
        valid_in && ctl == DEC |=> (alu == ($past(b) - 1)) ;
    endproperty
    assert property (p_DEC);
    cover property (p_DEC);

    property p_ADD;
        @(posedge clk) disable iff (!reset)
        valid_in && ctl == ADD |=> (alu == ($past(a) + $past(b))) ;
    endproperty
    assert property (p_ADD);
    cover property (p_ADD);

    property p_ADD_c;
        @(posedge clk) disable iff (!reset)
        valid_in && ctl == ADD_c |=> (alu == ($past(a) + $past(b) + $past(cin))) ;
    endproperty
    assert property (p_ADD_c);
    cover property (p_ADD_c);

    property p_SUB;
        @(posedge clk) disable iff (!reset)
        valid_in && ctl == SUB |=> (alu == ($past(a) - $past(b))) ;
    endproperty
    assert property (p_SUB);
    cover property (p_SUB);

    property p_SUB_b;
        @(posedge clk) disable iff (!reset)
        valid_in && ctl == SUB_b |=> (alu == ($past(a) - $past(b) - $past(cin))) ;
    endproperty
    assert property (p_SUB_b);
    cover property (p_SUB_b);

    property p_AND;
        @(posedge clk) disable iff (!reset)
        valid_in && ctl == AND |=> (alu == ($past(a) & $past(b))) ;
    endproperty
    assert property (p_AND);
    cover property (p_AND);

    property p_OR;
        @(posedge clk) disable iff (!reset)
        valid_in && ctl == OR |=> (alu == ($past(a) | $past(b))) ;
    endproperty
    assert property (p_OR);
    cover property (p_OR);

    property p_XOR;
        @(posedge clk) disable iff (!reset)
        valid_in && ctl == XOR |=> (alu == ($past(a) ^ $past(b))) ;
    endproperty
    assert property (p_XOR);
    cover property (p_XOR);

    // property p_SHIFT_L;
    //     @(posedge clk) disable iff (!reset)
    //     valid_in && ctl == SHIFT_L |=> (alu == ($past(a) << 1)) && valid_out;
    // endproperty
    // assert property (p_SHIFT_L);
    // cover property (p_SHIFT_L);

    // property p_SHIFT_R;
    //     @(posedge clk) disable iff (!reset)
    //     valid_in && ctl == SHIFT_R |=> (alu == ($past(a) >> 1)) && valid_out;
    // endproperty
    // assert property (p_SHIFT_R);
    // cover property (p_SHIFT_R);

    // property p_ROTATE_L;
    //     @(posedge clk) disable iff (!reset)
    //     valid_in && ctl == ROTATE_L |=> (alu == {$past(a[2:0]), $past(a[3])}) && valid_out;
    // endproperty
    // assert property (p_ROTATE_L);
    // cover property (p_ROTATE_L);

    // property p_ROTATE_R;
    //     @(posedge clk) disable iff (!reset)
    //     valid_in && ctl == ROTATE_R |=> (alu == {$past(a[0]), $past(a[3:1])}) && valid_out;
    // endproperty
    // assert property (p_ROTATE_R);
    // cover property (p_ROTATE_R);

    // property p_CARRY;
    //     @(posedge clk) disable iff (!reset)
    //     valid_in && (ctl inside {ADD, ADD_c, SUB, SUB_b}) |=> 
    //     (carry == ((ctl == ADD || ctl == ADD_c) ? 
    //                   (a + b + (ctl == ADD_c ? cin : 0)) >> $bits(alu) :
    //                   (a < (b + (ctl == SUB_b ? cin : 0)))) &&
    //      valid_out);
    // endproperty

    property p_CARRY;
        @(posedge clk) disable iff (!reset)
        valid_in && !(ctl inside {ADD, ADD_c, SUB, SUB_b, invalid_1, invalid_2}) |=> ~carry;
    endproperty
    assert property (p_CARRY);
    cover property (p_CARRY);

    property p_ZERO;
        @(posedge clk) disable iff (!reset)
        valid_in |=> zero == (alu == 4'b0);
    endproperty
    assert property (p_ZERO);
    cover property (p_ZERO);

    property p_Valid_out_off;
        @(posedge clk) disable iff (!reset)
        ~valid_in || ((ctl == invalid_1 || ctl == invalid_2) && valid_in) |=> ~valid_out; 
    endproperty
    assert property (p_Valid_out_off);
    cover property (p_Valid_out_off);

    property p_Valid_out_on;
        @(posedge clk) disable iff (!reset)
        valid_in && (ctl != invalid_1 && ctl != invalid_2) |=> valid_out; 
    endproperty
    assert property (p_Valid_out_on);
    cover property (p_Valid_out_on);

    property p_Valid_in_off;
        @(posedge clk) disable iff (!reset)
        ~valid_in |=> ($past(alu) == $past(alu,1) && $past(carry) == $past(carry,1) && ~valid_out);
    endproperty

    
endmodule