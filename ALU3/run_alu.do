vlib work

vlog -f src_files.list +cover -covercells

vsim -voptargs=+acc work.alu_top -cover

# Configure wave window properties
configure wave -namecolwidth 200
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -timelineunits ns

# Add wave groups and signals
add wave -divider "CLOCK AND RESET"
add wave -noupdate -format Logic /alu_top/clk
add wave -noupdate -format Logic /alu_top/intf/reset

add wave -divider "INPUTS"
add wave -noupdate -format Logic /alu_top/intf/valid_in
add wave -noupdate -format Literal -radix hexadecimal /alu_top/intf/a
add wave -noupdate -format Literal -radix hexadecimal /alu_top/intf/b
add wave -noupdate -format Logic /alu_top/intf/cin
add wave -noupdate -format Literal -radix hexadecimal /alu_top/intf/ctl

add wave -divider "DUT OUTPUTS"
add wave -noupdate -format Logic /alu_top/intf/valid_out
add wave -noupdate -format Literal -radix hexadecimal /alu_top/intf/alu
add wave -noupdate -format Logic /alu_top/intf/carry
add wave -noupdate -format Logic /alu_top/intf/zero

add wave -divider "REFERENCE MODEL OUTPUTS"
add wave -noupdate -format Logic /alu_top/intf/valid_out_ref
add wave -noupdate -format Literal -radix hexadecimal /alu_top/intf/alu_ref
add wave -noupdate -format Logic /alu_top/intf/carry_ref
add wave -noupdate -format Logic /alu_top/intf/zero_ref

# Configure wave window zoom level
wave zoom full

coverage save alu_tb.ucdb -onexit

vcover report alu_tb.ucdb -details -annotate -all -output alu_cvr_rpt.txt

run -all
