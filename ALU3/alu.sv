module alu(alu_interface.DUT intf);

logic clk, reset, valid_in, cin, valid_out, carry, zero;    
logic [3:0] a, b, ctl, alu;

assign clk = intf.clk;
assign reset = intf.reset; 
assign a = intf.a;
assign b = intf.b;
assign cin = intf.cin;
assign ctl = intf.ctl;
assign valid_in = intf.valid_in;


assign intf.valid_out = valid_out; 
assign intf.alu = alu; 
assign intf.carry = carry; 
assign intf.zero = zero; 


wire [4:0] result; 
wire       zero_result;
reg valid_out_R;

assign result = alu_out(a,b,cin,ctl); 
assign zero_result = z_flag(result); 

always@(posedge clk, negedge reset) begin
if(reset == 0) begin
valid_out_R <= 0;
valid_out   <= 0;
alu         <= 0;
carry       <= 0; 
zero        <= 0;
end
else begin
valid_out_R <= valid_in;
if(ctl == 4'b1001) begin       
valid_out <= ~valid_in;
end
else if(ctl == 4'b0110) begin  
valid_out <= valid_out_R;
end
else begin
valid_out <= valid_in;
end
if(valid_in) begin
alu   <= result[3:0]; 
carry <= result[4]; 
zero  <= zero_result; 
end
end
end
function [4:0] alu_out; 
input [3:0] a,b ; 
input cin ; 
input [3:0] ctl ; 
case ( ctl ) 
4'b0000: alu_out=a;                                
4'b0001: alu_out=b+4'b0001 ;                        
4'b0010: alu_out=b-4'b0001 ;                        
4'b0011: alu_out=a+b;                              
4'b0100: alu_out=a+b+cin;                           
4'b0101: alu_out=a-b+1 ;                            
4'b0110: alu_out=a-b+(~cin);                       
4'b0111: alu_out=a&b;                              
4'b1000: alu_out=a|b;                              
4'b1001: alu_out=a^b;                              
4'b1010: alu_out={b[3:0],1'b1};                    
4'b1011: alu_out={b[0],1'b0,b[3:1]};                
4'b1100: alu_out={b[3:0],cin};                     
4'b1101: alu_out={b[0],cin,b[3:1]};                
default : begin 
alu_out=9'bxxxxxxxxx; 
$display("Illegal CTL detected!!"); 
end 
endcase 
endfunction  
function z_flag ; 
input [4:0] a4 ; 
begin 
z_flag = ^(a4[0]|a4[1]|a4[2]|a4[3]) ; 
end 
endfunction 
endmodule
