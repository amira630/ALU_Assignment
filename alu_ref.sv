typedef enum bit [3:0] {SEL, INC, DEC, ADD, ADD_c, SUB, SUB_b, AND, OR, XOR, SHIFT_L, SHIFT_R, ROTATE_L, ROTATE_R, invalid_1, invalid_2} opcode_e;

module alu_ref(
    input            clk,
    input            reset,
    input            valid_in,    //validate input signals
    input [3:0]      a,           //port A
    input [3:0]      b,           //port B 
    input            cin,         //carry input from carry flag register 
    input [3:0]      ctl,         //functionality control for ALU 
    //Output signals
    output reg       valid_out,   //validate output signals
    output reg [3:0] alu,         //the result 
    output reg       carry,       //carry output 
    output reg       zero         //zero output 
);

opcode_e opcode;
reg [4:0] out_r;
reg valid_r, zero_r;

assign opcode = opcode_e'(ctl);

always @(posedge clk or negedge reset) begin
    if(~reset) begin
        valid_out <= 1'b0;
        alu <= 4'b0;
        carry <= 1'b0;
        zero <= 1'b0;
    end
    else begin 
        valid_out <= valid_r;
        if(valid_in) begin
            alu   <= out_r[3:0];
            carry <= out_r[4];
            zero  <= zero_r;
        end
    end
end

always @(*) begin
    valid_r = valid_in;
    case (opcode)
        SEL:      out_r = b;
        INC: begin 
            if (b < 4'hf) 
                out_r = b + 1; 
            else 
                out_r = b; 
        end
        DEC: begin 
            if (b > 0) 
                out_r = b - 1; 
            else 
                out_r = b; 
        end
        ADD:      out_r = a + b;
        ADD_c:    out_r = a + b + cin;
        SUB:      out_r = a - b;
        SUB_b:    out_r = a - b - cin;
        AND:      out_r = a & b; 
        OR:       out_r = a | b;
        XOR:      out_r = a ^ b;
        SHIFT_L:  out_r = {out_r[3:0], 1'b0};
        SHIFT_R:  out_r = {1'b0, out_r[4:1]};
        ROTATE_L: out_r = {out_r[3:0], out_r[4]};
        ROTATE_R: out_r = {out_r[0], out_r[4:1]};
        default:  valid_r = 1'b0;
    endcase
    if (~&out_r[3:0]) 
        zero_r = 1'b1;
    else
        zero_r = 1'b0;
end
endmodule