vlib work
vlog -f src_files.list +cover -covercells
vsim -voptargs=+acc work.alu_top -cover
add wave *
coverage save alu_tb.ucdb -onexit
vcover report alu_tb.ucdb -details -annotate -all -output alu_cvr_rpt.txt
run -all
