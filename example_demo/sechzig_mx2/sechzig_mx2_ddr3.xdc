################################################################################
# IO constraints
################################################################################
# clk48:0
set_property LOC F5 [get_ports {clk48}]
set_property IOSTANDARD LVCMOS33 [get_ports {clk48}]

# clk50:0
set_property LOC D4 [get_ports {clk50}]
set_property IOSTANDARD LVCMOS33 [get_ports {clk50}]

# led
set_property LOC R16 [get_ports {led}]
set_property IOSTANDARD LVCMOS33 [get_ports {led}]

# led (n/c)
set_property LOC T14 [get_ports {led[1]}]
set_property IOSTANDARD LVCMOS33 [get_ports {led[1]}]

# serial:0.tx
set_property LOC L2 [get_ports {tx}]
set_property IOSTANDARD LVCMOS33 [get_ports {tx}]

# serial:0.rx
set_property LOC L3 [get_ports {rx}]
set_property IOSTANDARD LVCMOS33 [get_ports {rx}]

# ddr3:0.a
set_property LOC F12 [get_ports {ddr3_addr[0]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_addr[0]}]

# ddr3:0.a
set_property LOC D15 [get_ports {ddr3_addr[1]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_addr[1]}]

# ddr3:0.a
set_property LOC J15 [get_ports {ddr3_addr[2]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_addr[2]}]

# ddr3:0.a
set_property LOC E16 [get_ports {ddr3_addr[3]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_addr[3]}]

# ddr3:0.a
set_property LOC G11 [get_ports {ddr3_addr[4]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_addr[4]}]

# ddr3:0.a
set_property LOC F15 [get_ports {ddr3_addr[5]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_addr[5]}]

# ddr3:0.a
set_property LOC H13 [get_ports {ddr3_addr[6]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_addr[6]}]

# ddr3:0.a
set_property LOC G15 [get_ports {ddr3_addr[7]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_addr[7]}]

# ddr3:0.a
set_property LOC H12 [get_ports {ddr3_addr[8]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_addr[8]}]

# ddr3:0.a
set_property LOC H16 [get_ports {ddr3_addr[9]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_addr[9]}]

# ddr3:0.a
set_property LOC H11 [get_ports {ddr3_addr[10]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_addr[10]}]

# ddr3:0.a
set_property LOC H14 [get_ports {ddr3_addr[11]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_addr[11]}]

# ddr3:0.a
set_property LOC E12 [get_ports {ddr3_addr[12]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_addr[12]}]

# ddr3:0.a
set_property LOC G16 [get_ports {ddr3_addr[13]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_addr[13]}]

# ddr3:0.a
set_property LOC J16 [get_ports {ddr3_addr[14]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_addr[14]}]

# ddr3:0.ba
set_property LOC E15 [get_ports {ddr3_ba[0]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_ba[0]}]

# ddr3:0.ba
set_property LOC D11 [get_ports {ddr3_ba[1]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_ba[1]}]

# ddr3:0.ba
set_property LOC F13 [get_ports {ddr3_ba[2]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_ba[2]}]

# ddr3:0.ras_n
set_property LOC D14 [get_ports {ddr3_ras_n}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_ras_n}]

# ddr3:0.cas_n
set_property LOC E13 [get_ports {ddr3_cas_n}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_cas_n}]

# ddr3:0.we_n
set_property LOC G12 [get_ports {ddr3_we_n}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_we_n}]

# ddr3:0.dm
set_property LOC A13 [get_ports {ddr3_dm[0]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_dm[0]}]

# ddr3:0.dm
set_property LOC D9 [get_ports {ddr3_dm[1]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_dm[1]}]

# ddr3:0.dq
set_property LOC A14 [get_ports {ddr3_dq[0]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_dq[0]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dq[0]}]

# ddr3:0.dq
set_property LOC C12 [get_ports {ddr3_dq[1]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_dq[1]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dq[1]}]

# ddr3:0.dq
set_property LOC B14 [get_ports {ddr3_dq[2]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_dq[2]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dq[2]}]

# ddr3:0.dq
set_property LOC D13 [get_ports {ddr3_dq[3]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_dq[3]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dq[3]}]

# ddr3:0.dq
set_property LOC B16 [get_ports {ddr3_dq[4]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_dq[4]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dq[4]}]

# ddr3:0.dq
set_property LOC C11 [get_ports {ddr3_dq[5]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_dq[5]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dq[5]}]

# ddr3:0.dq
set_property LOC C16 [get_ports {ddr3_dq[6]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_dq[6]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dq[6]}]

# ddr3:0.dq
set_property LOC C14 [get_ports {ddr3_dq[7]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_dq[7]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dq[7]}]

# ddr3:0.dq
set_property LOC A9 [get_ports {ddr3_dq[8]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_dq[8]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dq[8]}]

# ddr3:0.dq
set_property LOC B10 [get_ports {ddr3_dq[9]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_dq[9]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dq[9]}]

# ddr3:0.dq
set_property LOC C8 [get_ports {ddr3_dq[10]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_dq[10]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dq[10]}]

# ddr3:0.dq
set_property LOC B12 [get_ports {ddr3_dq[11]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_dq[11]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dq[11]}]

# ddr3:0.dq
set_property LOC A8 [get_ports {ddr3_dq[12]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_dq[12]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dq[12]}]

# ddr3:0.dq
set_property LOC A12 [get_ports {ddr3_dq[13]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_dq[13]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dq[13]}]

# ddr3:0.dq
set_property LOC C9 [get_ports {ddr3_dq[14]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_dq[14]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dq[14]}]

# ddr3:0.dq
set_property LOC B11 [get_ports {ddr3_dq[15]}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_dq[15]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dq[15]}]

# ddr3:0.dqs_p
set_property LOC B15 [get_ports {ddr3_dqs_p[0]}]
set_property IOSTANDARD DIFF_SSTL135 [get_ports {ddr3_dqs_p[0]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dqs_p[0]}]

# ddr3:0.dqs_p
set_property LOC B9 [get_ports {ddr3_dqs_p[1]}]
set_property IOSTANDARD DIFF_SSTL135 [get_ports {ddr3_dqs_p[1]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dqs_p[1]}]

# ddr3:0.dqs_n
set_property LOC A15 [get_ports {ddr3_dqs_n[0]}]
set_property IOSTANDARD DIFF_SSTL135 [get_ports {ddr3_dqs_n[0]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dqs_n[0]}]

# ddr3:0.dqs_n
set_property LOC A10 [get_ports {ddr3_dqs_n[1]}]
set_property IOSTANDARD DIFF_SSTL135 [get_ports {ddr3_dqs_n[1]}]
set_property IN_TERM UNTUNED_SPLIT_60 [get_ports {ddr3_dqs_n[1]}]

# ddr3:0.clk_p
set_property LOC G14 [get_ports {ddr3_clk_p}]
set_property IOSTANDARD DIFF_SSTL135 [get_ports {ddr3_clk_p}]

# ddr3:0.clk_n
set_property LOC F14 [get_ports {ddr3_clk_n}]
set_property IOSTANDARD DIFF_SSTL135 [get_ports {ddr3_clk_n}]

# ddr3:0.cke
set_property LOC E11 [get_ports {ddr3_cke}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_cke}]

# ddr3:0.odt
set_property LOC D16 [get_ports {ddr3_odt}]
set_property IOSTANDARD SSTL135 [get_ports {ddr3_odt}]

# ddr3:0.reset_n
set_property LOC M16 [get_ports {ddr3_reset_n}]
set_property IOSTANDARD LVCMOS33 [get_ports {ddr3_reset_n}]

################################################################################
# Design constraints
################################################################################

# set_property INTERNAL_VREF 0.675 [get_iobanks 34]

# set_property INTERNAL_VREF 0.675 [get_iobanks 15]

################################################################################
# Clock constraints
################################################################################


# create_clock -name clk48 -period 20.833 [get_ports clk48]

# create_clock -name clk50 -period 20.0 [get_ports clk50]

# create_clock -name eth_rx_clk -period 20.0 [get_nets eth_rx_clk]

# create_clock -name eth_tx_clk -period 20.0 [get_nets eth_tx_clk]

# set_clock_groups -group [get_clocks -include_generated_clocks -of [get_nets sys_clk]] -group [get_clocks -include_generated_clocks -of [get_nets eth_rx_clk]] -asynchronous

# set_clock_groups -group [get_clocks -include_generated_clocks -of [get_nets sys_clk]] -group [get_clocks -include_generated_clocks -of [get_nets eth_tx_clk]] -asynchronous

# set_clock_groups -group [get_clocks -include_generated_clocks -of [get_nets eth_rx_clk]] -group [get_clocks -include_generated_clocks -of [get_nets eth_tx_clk]] -asynchronous

# ################################################################################
# # False path constraints
# ################################################################################


# set_false_path -quiet -through [get_nets -hierarchical -filter {mr_ff == TRUE}]

# set_false_path -quiet -to [get_pins -filter {REF_PIN_NAME == PRE} -of_objects [get_cells -hierarchical -filter {ars_ff1 == TRUE || ars_ff2 == TRUE}]]

# set_max_delay 2 -quiet -from [get_pins -filter {REF_PIN_NAME == C} -of_objects [get_cells -hierarchical -filter {ars_ff1 == TRUE}]] -to [get_pins -filter {REF_PIN_NAME == D} -of_objects [get_cells -hierarchical -filter {ars_ff2 == TRUE}]]
