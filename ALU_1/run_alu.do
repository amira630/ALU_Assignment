vlib work
vlog alu.v alu_ref.sv alu_pkg.sv alu_tb.sv +cover -covercells
vsim -voptargs=+acc work.alu_tb -cover
add wave *
coverage save alu_tb.ucdb -onexit
vcover report alu_tb.ucdb -details -annotate -all -output alu_cvr_rpt.txt
run -all
