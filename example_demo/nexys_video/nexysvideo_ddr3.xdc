set_property -dict {PACKAGE_PIN R4 IOSTANDARD LVCMOS33} [get_ports i_clk]
create_clock -period 10.000 -name sys_clk_pin -waveform {0.000 5.000} -add [get_ports i_clk]

set_property -dict {PACKAGE_PIN T14 IOSTANDARD LVCMOS33} [get_ports {led[0]}]
set_property -dict {PACKAGE_PIN T15 IOSTANDARD LVCMOS33} [get_ports {led[1]}]
set_property -dict {PACKAGE_PIN T16 IOSTANDARD LVCMOS33} [get_ports {led[2]}]
set_property -dict {PACKAGE_PIN U16 IOSTANDARD LVCMOS33} [get_ports {led[3]}]
set_property -dict {PACKAGE_PIN V15 IOSTANDARD LVCMOS33} [get_ports {led[4]}]
set_property -dict {PACKAGE_PIN W16 IOSTANDARD LVCMOS33} [get_ports {led[5]}]
set_property -dict {PACKAGE_PIN W15 IOSTANDARD LVCMOS33} [get_ports {led[6]}]
set_property -dict {PACKAGE_PIN Y13 IOSTANDARD LVCMOS33} [get_ports {led[7]}]

set_property -dict {PACKAGE_PIN B22 IOSTANDARD LVCMOS33} [get_ports i_rst]
set_property -dict {PACKAGE_PIN D22 IOSTANDARD LVCMOS33} [get_ports {btn[0]}]
set_property -dict {PACKAGE_PIN C22 IOSTANDARD LVCMOS33} [get_ports {btn[1]}]
set_property -dict {PACKAGE_PIN D14 IOSTANDARD LVCMOS33} [get_ports {btn[2]}]
set_property -dict {PACKAGE_PIN F15 IOSTANDARD LVCMOS33} [get_ports {btn[3]}]

set_property -dict {PACKAGE_PIN AA19 IOSTANDARD LVCMOS33} [get_ports tx]
set_property -dict {PACKAGE_PIN V18 IOSTANDARD LVCMOS33} [get_ports rx]

set_property SLEW FAST [get_ports {ddr3_dq[0]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[0]}]
set_property PACKAGE_PIN G2 [get_ports {ddr3_dq[0]}]

set_property SLEW FAST [get_ports {ddr3_dq[1]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[1]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[1]}]
set_property PACKAGE_PIN H4 [get_ports {ddr3_dq[1]}]

set_property SLEW FAST [get_ports {ddr3_dq[2]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[2]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[2]}]
set_property PACKAGE_PIN H5 [get_ports {ddr3_dq[2]}]

set_property SLEW FAST [get_ports {ddr3_dq[3]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[3]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[3]}]
set_property PACKAGE_PIN J1 [get_ports {ddr3_dq[3]}]

set_property SLEW FAST [get_ports {ddr3_dq[4]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[4]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[4]}]
set_property PACKAGE_PIN K1 [get_ports {ddr3_dq[4]}]

set_property SLEW FAST [get_ports {ddr3_dq[5]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[5]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[5]}]
set_property PACKAGE_PIN H3 [get_ports {ddr3_dq[5]}]

set_property SLEW FAST [get_ports {ddr3_dq[6]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[6]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[6]}]
set_property PACKAGE_PIN H2 [get_ports {ddr3_dq[6]}]

set_property SLEW FAST [get_ports {ddr3_dq[7]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[7]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[7]}]
set_property PACKAGE_PIN J5 [get_ports {ddr3_dq[7]}]

set_property SLEW FAST [get_ports {ddr3_dq[8]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[8]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[8]}]
set_property PACKAGE_PIN E3 [get_ports {ddr3_dq[8]}]

set_property SLEW FAST [get_ports {ddr3_dq[9]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[9]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[9]}]
set_property PACKAGE_PIN B2 [get_ports {ddr3_dq[9]}]

set_property SLEW FAST [get_ports {ddr3_dq[10]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[10]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[10]}]
set_property PACKAGE_PIN F3 [get_ports {ddr3_dq[10]}]

set_property SLEW FAST [get_ports {ddr3_dq[11]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[11]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[11]}]
set_property PACKAGE_PIN D2 [get_ports {ddr3_dq[11]}]

set_property SLEW FAST [get_ports {ddr3_dq[12]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[12]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[12]}]
set_property PACKAGE_PIN C2 [get_ports {ddr3_dq[12]}]

set_property SLEW FAST [get_ports {ddr3_dq[13]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[13]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[13]}]
set_property PACKAGE_PIN A1 [get_ports {ddr3_dq[13]}]

set_property SLEW FAST [get_ports {ddr3_dq[14]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[14]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[14]}]
set_property PACKAGE_PIN E2 [get_ports {ddr3_dq[14]}]

set_property SLEW FAST [get_ports {ddr3_dq[15]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[15]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[15]}]
set_property PACKAGE_PIN B1 [get_ports {ddr3_dq[15]}]

set_property SLEW FAST [get_ports {ddr3_addr[14]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[14]}]
set_property PACKAGE_PIN P6 [get_ports {ddr3_addr[14]}]

set_property SLEW FAST [get_ports {ddr3_addr[13]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[13]}]
set_property PACKAGE_PIN P2 [get_ports {ddr3_addr[13]}]

set_property SLEW FAST [get_ports {ddr3_addr[12]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[12]}]
set_property PACKAGE_PIN N4 [get_ports {ddr3_addr[12]}]

set_property SLEW FAST [get_ports {ddr3_addr[11]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[11]}]
set_property PACKAGE_PIN N5 [get_ports {ddr3_addr[11]}]

set_property SLEW FAST [get_ports {ddr3_addr[10]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[10]}]
set_property PACKAGE_PIN L5 [get_ports {ddr3_addr[10]}]

set_property SLEW FAST [get_ports {ddr3_addr[9]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[9]}]
set_property PACKAGE_PIN R1 [get_ports {ddr3_addr[9]}]

set_property SLEW FAST [get_ports {ddr3_addr[8]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[8]}]
set_property PACKAGE_PIN M6 [get_ports {ddr3_addr[8]}]

set_property SLEW FAST [get_ports {ddr3_addr[7]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[7]}]
set_property PACKAGE_PIN N2 [get_ports {ddr3_addr[7]}]

set_property SLEW FAST [get_ports {ddr3_addr[6]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[6]}]
set_property PACKAGE_PIN N3 [get_ports {ddr3_addr[6]}]

set_property SLEW FAST [get_ports {ddr3_addr[5]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[5]}]
set_property PACKAGE_PIN P1 [get_ports {ddr3_addr[5]}]

set_property SLEW FAST [get_ports {ddr3_addr[4]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[4]}]
set_property PACKAGE_PIN L6 [get_ports {ddr3_addr[4]}]

set_property SLEW FAST [get_ports {ddr3_addr[3]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[3]}]
set_property PACKAGE_PIN M1 [get_ports {ddr3_addr[3]}]

set_property SLEW FAST [get_ports {ddr3_addr[2]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[2]}]
set_property PACKAGE_PIN M3 [get_ports {ddr3_addr[2]}]

set_property SLEW FAST [get_ports {ddr3_addr[1]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[1]}]
set_property PACKAGE_PIN M5 [get_ports {ddr3_addr[1]}]

set_property SLEW FAST [get_ports {ddr3_addr[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[0]}]
set_property PACKAGE_PIN M2 [get_ports {ddr3_addr[0]}]

set_property SLEW FAST [get_ports {ddr3_ba[2]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_ba[2]}]
set_property PACKAGE_PIN L4 [get_ports {ddr3_ba[2]}]

set_property SLEW FAST [get_ports {ddr3_ba[1]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_ba[1]}]
set_property PACKAGE_PIN K6 [get_ports {ddr3_ba[1]}]

set_property SLEW FAST [get_ports {ddr3_ba[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_ba[0]}]
set_property PACKAGE_PIN L3 [get_ports {ddr3_ba[0]}]

set_property SLEW FAST [get_ports ddr3_ras_n]
set_property IOSTANDARD SSTL15 [get_ports ddr3_ras_n]
set_property PACKAGE_PIN J4 [get_ports ddr3_ras_n]

set_property SLEW FAST [get_ports ddr3_cas_n]
set_property IOSTANDARD SSTL15 [get_ports ddr3_cas_n]
set_property PACKAGE_PIN K3 [get_ports ddr3_cas_n]

set_property SLEW FAST [get_ports ddr3_we_n]
set_property IOSTANDARD SSTL15 [get_ports ddr3_we_n]
set_property PACKAGE_PIN L1 [get_ports ddr3_we_n]

set_property SLEW FAST [get_ports ddr3_reset_n]
set_property IOSTANDARD SSTL15 [get_ports ddr3_reset_n]
set_property PACKAGE_PIN G1 [get_ports ddr3_reset_n]

set_property SLEW FAST [get_ports ddr3_cke]
set_property IOSTANDARD SSTL15 [get_ports ddr3_cke]
set_property PACKAGE_PIN J6 [get_ports ddr3_cke]

set_property SLEW FAST [get_ports ddr3_odt]
set_property IOSTANDARD SSTL15 [get_ports ddr3_odt]
set_property PACKAGE_PIN K4 [get_ports ddr3_odt]

set_property SLEW FAST [get_ports ddr3_cs_n]
set_property IOSTANDARD LVCMOS33 [get_ports ddr3_cs_n]
set_property PACKAGE_PIN R3 [get_ports ddr3_cs_n]

set_property SLEW FAST [get_ports {ddr3_dm[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dm[0]}]
set_property PACKAGE_PIN G3 [get_ports {ddr3_dm[0]}]

set_property SLEW FAST [get_ports {ddr3_dm[1]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dm[1]}]
set_property PACKAGE_PIN F1 [get_ports {ddr3_dm[1]}]


set_property SLEW FAST [get_ports {ddr3_dqs_p}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dqs_p}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_p}]

set_property SLEW FAST [get_ports {ddr3_dqs_n}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dqs_n}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_n}]
set_property PACKAGE_PIN K2 [get_ports {ddr3_dqs_p}]
set_property PACKAGE_PIN J2 [get_ports {ddr3_dqs_n}]

#set_property SLEW FAST [get_ports {ddr3_dqs_p[1]}]
#set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dqs_p[1]}]
#set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_p[1]}]

#set_property SLEW FAST [get_ports {ddr3_dqs_n[1]}]
#set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dqs_n[1]}]
#set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_n[1]}]
#set_property PACKAGE_PIN E1 [get_ports {ddr3_dqs_p[1]}]
#set_property PACKAGE_PIN D1 [get_ports {ddr3_dqs_n[1]}]

set_property SLEW FAST [get_ports ddr3_clk_p]
set_property IOSTANDARD DIFF_SSTL15 [get_ports ddr3_clk_p]

set_property SLEW FAST [get_ports ddr3_clk_n]
set_property IOSTANDARD DIFF_SSTL15 [get_ports ddr3_clk_n]
set_property PACKAGE_PIN P5 [get_ports ddr3_clk_p]
set_property PACKAGE_PIN P4 [get_ports ddr3_clk_n]

#set_property INTERNAL_VREF 0.75 [get_iobanks 35]
#set_property CONFIG_VOLTAGE 3.3 [current_design]
#set_property CFGBVS VCCO [current_design]

