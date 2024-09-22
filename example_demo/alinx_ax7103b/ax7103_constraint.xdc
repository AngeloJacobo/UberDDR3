############## NET - IOSTANDARD #####################
set_property CFGBVS VCCO [current_design]
set_property CONFIG_VOLTAGE 3.3 [current_design]
#############SPI Configurate Setting##################
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design] 
set_property CONFIG_MODE SPIx4 [current_design] 
set_property BITSTREAM.CONFIG.CONFIGRATE 50 [current_design] 
############## clock define###########################
create_clock -period 5 [get_ports sys_clk_p]
set_property PACKAGE_PIN R4 [get_ports sys_clk_p]
set_property IOSTANDARD DIFF_SSTL15 [get_ports sys_clk_p]
##############reset key define########################
set_property PACKAGE_PIN J21 [get_ports i_rst_n] 
set_property IOSTANDARD LVCMOS33 [get_ports i_rst_n]


##############LED define##########################
set_property PACKAGE_PIN B13 [get_ports {led[0]}]
set_property IOSTANDARD LVCMOS33 [get_ports {led[0]}]

set_property PACKAGE_PIN C13 [get_ports {led[1]}]
set_property IOSTANDARD LVCMOS33 [get_ports {led[1]}]

set_property PACKAGE_PIN D14 [get_ports {led[2]}]
set_property IOSTANDARD LVCMOS33 [get_ports {led[2]}]

set_property PACKAGE_PIN D15 [get_ports {led[3]}]
set_property IOSTANDARD LVCMOS33 [get_ports {led[3]}]


##############UART define##########################
set_property PACKAGE_PIN P20 [get_ports {rx}]
set_property IOSTANDARD LVCMOS33 [get_ports {rx}]

set_property PACKAGE_PIN N15 [get_ports {tx}]
set_property IOSTANDARD LVCMOS33 [get_ports {tx}]

############## NET - IOSTANDARD ##################


# PadFunction: IO_L2P_T0_AD12P_35 
set_property SLEW FAST [get_ports {ddr3_dq[0]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[0]}]
set_property PACKAGE_PIN C2 [get_ports {ddr3_dq[0]}]

# PadFunction: IO_L5P_T0_AD13P_35 
set_property SLEW FAST [get_ports {ddr3_dq[1]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[1]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[1]}]
set_property PACKAGE_PIN G1 [get_ports {ddr3_dq[1]}]

# PadFunction: IO_L1N_T0_AD4N_35 
set_property SLEW FAST [get_ports {ddr3_dq[2]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[2]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[2]}]
set_property PACKAGE_PIN A1 [get_ports {ddr3_dq[2]}]

# PadFunction: IO_L6P_T0_35 
set_property SLEW FAST [get_ports {ddr3_dq[3]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[3]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[3]}]
set_property PACKAGE_PIN F3 [get_ports {ddr3_dq[3]}]

# PadFunction: IO_L2N_T0_AD12N_35 
set_property SLEW FAST [get_ports {ddr3_dq[4]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[4]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[4]}]
set_property PACKAGE_PIN B2 [get_ports {ddr3_dq[4]}]

# PadFunction: IO_L5N_T0_AD13N_35 
set_property SLEW FAST [get_ports {ddr3_dq[5]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[5]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[5]}]
set_property PACKAGE_PIN F1 [get_ports {ddr3_dq[5]}]

# PadFunction: IO_L1P_T0_AD4P_35 
set_property SLEW FAST [get_ports {ddr3_dq[6]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[6]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[6]}]
set_property PACKAGE_PIN B1 [get_ports {ddr3_dq[6]}]

# PadFunction: IO_L4P_T0_35 
set_property SLEW FAST [get_ports {ddr3_dq[7]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[7]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[7]}]
set_property PACKAGE_PIN E2 [get_ports {ddr3_dq[7]}]

# PadFunction: IO_L11P_T1_SRCC_35 
set_property SLEW FAST [get_ports {ddr3_dq[8]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[8]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[8]}]
set_property PACKAGE_PIN H3 [get_ports {ddr3_dq[8]}]

# PadFunction: IO_L11N_T1_SRCC_35 
set_property SLEW FAST [get_ports {ddr3_dq[9]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[9]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[9]}]
set_property PACKAGE_PIN G3 [get_ports {ddr3_dq[9]}]

# PadFunction: IO_L8P_T1_AD14P_35 
set_property SLEW FAST [get_ports {ddr3_dq[10]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[10]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[10]}]
set_property PACKAGE_PIN H2 [get_ports {ddr3_dq[10]}]

# PadFunction: IO_L10N_T1_AD15N_35 
set_property SLEW FAST [get_ports {ddr3_dq[11]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[11]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[11]}]
set_property PACKAGE_PIN H5 [get_ports {ddr3_dq[11]}]

# PadFunction: IO_L7N_T1_AD6N_35 
set_property SLEW FAST [get_ports {ddr3_dq[12]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[12]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[12]}]
set_property PACKAGE_PIN J1 [get_ports {ddr3_dq[12]}]

# PadFunction: IO_L10P_T1_AD15P_35 
set_property SLEW FAST [get_ports {ddr3_dq[13]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[13]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[13]}]
set_property PACKAGE_PIN J5 [get_ports {ddr3_dq[13]}]

# PadFunction: IO_L7P_T1_AD6P_35 
set_property SLEW FAST [get_ports {ddr3_dq[14]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[14]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[14]}]
set_property PACKAGE_PIN K1 [get_ports {ddr3_dq[14]}]

# PadFunction: IO_L12P_T1_MRCC_35 
set_property SLEW FAST [get_ports {ddr3_dq[15]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[15]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[15]}]
set_property PACKAGE_PIN H4 [get_ports {ddr3_dq[15]}]

# PadFunction: IO_L18N_T2_35 
set_property SLEW FAST [get_ports {ddr3_dq[16]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[16]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[16]}]
set_property PACKAGE_PIN L4 [get_ports {ddr3_dq[16]}]

# PadFunction: IO_L16P_T2_35 
set_property SLEW FAST [get_ports {ddr3_dq[17]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[17]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[17]}]
set_property PACKAGE_PIN M3 [get_ports {ddr3_dq[17]}]

# PadFunction: IO_L14P_T2_SRCC_35 
set_property SLEW FAST [get_ports {ddr3_dq[18]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[18]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[18]}]
set_property PACKAGE_PIN L3 [get_ports {ddr3_dq[18]}]

# PadFunction: IO_L17N_T2_35 
set_property SLEW FAST [get_ports {ddr3_dq[19]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[19]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[19]}]
set_property PACKAGE_PIN J6 [get_ports {ddr3_dq[19]}]

# PadFunction: IO_L14N_T2_SRCC_35 
set_property SLEW FAST [get_ports {ddr3_dq[20]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[20]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[20]}]
set_property PACKAGE_PIN K3 [get_ports {ddr3_dq[20]}]

# PadFunction: IO_L17P_T2_35 
set_property SLEW FAST [get_ports {ddr3_dq[21]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[21]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[21]}]
set_property PACKAGE_PIN K6 [get_ports {ddr3_dq[21]}]

# PadFunction: IO_L13N_T2_MRCC_35 
set_property SLEW FAST [get_ports {ddr3_dq[22]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[22]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[22]}]
set_property PACKAGE_PIN J4 [get_ports {ddr3_dq[22]}]

# PadFunction: IO_L18P_T2_35 
set_property SLEW FAST [get_ports {ddr3_dq[23]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[23]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[23]}]
set_property PACKAGE_PIN L5 [get_ports {ddr3_dq[23]}]

# PadFunction: IO_L20N_T3_35 
set_property SLEW FAST [get_ports {ddr3_dq[24]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[24]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[24]}]
set_property PACKAGE_PIN P1 [get_ports {ddr3_dq[24]}]

# PadFunction: IO_L19P_T3_35 
set_property SLEW FAST [get_ports {ddr3_dq[25]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[25]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[25]}]
set_property PACKAGE_PIN N4 [get_ports {ddr3_dq[25]}]

# PadFunction: IO_L20P_T3_35 
set_property SLEW FAST [get_ports {ddr3_dq[26]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[26]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[26]}]
set_property PACKAGE_PIN R1 [get_ports {ddr3_dq[26]}]

# PadFunction: IO_L22N_T3_35 
set_property SLEW FAST [get_ports {ddr3_dq[27]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[27]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[27]}]
set_property PACKAGE_PIN N2 [get_ports {ddr3_dq[27]}]

# PadFunction: IO_L23P_T3_35 
set_property SLEW FAST [get_ports {ddr3_dq[28]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[28]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[28]}]
set_property PACKAGE_PIN M6 [get_ports {ddr3_dq[28]}]

# PadFunction: IO_L24N_T3_35 
set_property SLEW FAST [get_ports {ddr3_dq[29]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[29]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[29]}]
set_property PACKAGE_PIN N5 [get_ports {ddr3_dq[29]}]

# PadFunction: IO_L24P_T3_35 
set_property SLEW FAST [get_ports {ddr3_dq[30]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[30]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[30]}]
set_property PACKAGE_PIN P6 [get_ports {ddr3_dq[30]}]

# PadFunction: IO_L22P_T3_35 
set_property SLEW FAST [get_ports {ddr3_dq[31]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dq[31]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[31]}]
set_property PACKAGE_PIN P2 [get_ports {ddr3_dq[31]}]

# PadFunction: IO_L6N_T0_VREF_34 
set_property SLEW FAST [get_ports {ddr3_addr[14]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[14]}]
set_property PACKAGE_PIN V3 [get_ports {ddr3_addr[14]}]

# PadFunction: IO_L1N_T0_34 
set_property SLEW FAST [get_ports {ddr3_addr[13]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[13]}]
set_property PACKAGE_PIN U1 [get_ports {ddr3_addr[13]}]

# PadFunction: IO_L4N_T0_34 
set_property SLEW FAST [get_ports {ddr3_addr[12]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[12]}]
set_property PACKAGE_PIN Y2 [get_ports {ddr3_addr[12]}]

# PadFunction: IO_L4P_T0_34 
set_property SLEW FAST [get_ports {ddr3_addr[11]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[11]}]
set_property PACKAGE_PIN W2 [get_ports {ddr3_addr[11]}]

# PadFunction: IO_L5N_T0_34 
set_property SLEW FAST [get_ports {ddr3_addr[10]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[10]}]
set_property PACKAGE_PIN Y1 [get_ports {ddr3_addr[10]}]

# PadFunction: IO_L2P_T0_34 
set_property SLEW FAST [get_ports {ddr3_addr[9]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[9]}]
set_property PACKAGE_PIN U2 [get_ports {ddr3_addr[9]}]

# PadFunction: IO_L2N_T0_34 
set_property SLEW FAST [get_ports {ddr3_addr[8]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[8]}]
set_property PACKAGE_PIN V2 [get_ports {ddr3_addr[8]}]

# PadFunction: IO_L1P_T0_34 
set_property SLEW FAST [get_ports {ddr3_addr[7]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[7]}]
set_property PACKAGE_PIN T1 [get_ports {ddr3_addr[7]}]

# PadFunction: IO_L5P_T0_34 
set_property SLEW FAST [get_ports {ddr3_addr[6]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[6]}]
set_property PACKAGE_PIN W1 [get_ports {ddr3_addr[6]}]

# PadFunction: IO_L6P_T0_34 
set_property SLEW FAST [get_ports {ddr3_addr[5]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[5]}]
set_property PACKAGE_PIN U3 [get_ports {ddr3_addr[5]}]

# PadFunction: IO_L7N_T1_34 
set_property SLEW FAST [get_ports {ddr3_addr[4]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[4]}]
set_property PACKAGE_PIN AB1 [get_ports {ddr3_addr[4]}]

# PadFunction: IO_L10N_T1_34 
set_property SLEW FAST [get_ports {ddr3_addr[3]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[3]}]
set_property PACKAGE_PIN AB5 [get_ports {ddr3_addr[3]}]

# PadFunction: IO_L10P_T1_34 
set_property SLEW FAST [get_ports {ddr3_addr[2]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[2]}]
set_property PACKAGE_PIN AA5 [get_ports {ddr3_addr[2]}]

# PadFunction: IO_L8N_T1_34 
set_property SLEW FAST [get_ports {ddr3_addr[1]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[1]}]
set_property PACKAGE_PIN AB2 [get_ports {ddr3_addr[1]}]

# PadFunction: IO_L11N_T1_SRCC_34 
set_property SLEW FAST [get_ports {ddr3_addr[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[0]}]
set_property PACKAGE_PIN AA4 [get_ports {ddr3_addr[0]}]

# PadFunction: IO_L11P_T1_SRCC_34 
set_property SLEW FAST [get_ports {ddr3_ba[2]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_ba[2]}]
set_property PACKAGE_PIN Y4 [get_ports {ddr3_ba[2]}]

# PadFunction: IO_L9P_T1_DQS_34 
set_property SLEW FAST [get_ports {ddr3_ba[1]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_ba[1]}]
set_property PACKAGE_PIN Y3 [get_ports {ddr3_ba[1]}]

# PadFunction: IO_L9N_T1_DQS_34 
set_property SLEW FAST [get_ports {ddr3_ba[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_ba[0]}]
set_property PACKAGE_PIN AA3 [get_ports {ddr3_ba[0]}]

# PadFunction: IO_L12P_T1_MRCC_34 
set_property SLEW FAST [get_ports {ddr3_ras_n}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_ras_n}]
set_property PACKAGE_PIN V4 [get_ports {ddr3_ras_n}]

# PadFunction: IO_L12N_T1_MRCC_34 
set_property SLEW FAST [get_ports {ddr3_cas_n}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_cas_n}]
set_property PACKAGE_PIN W4 [get_ports {ddr3_cas_n}]

# PadFunction: IO_L7P_T1_34 
set_property SLEW FAST [get_ports {ddr3_we_n}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_we_n}]
set_property PACKAGE_PIN AA1 [get_ports {ddr3_we_n}]

# PadFunction: IO_L15P_T2_DQS_34 
set_property SLEW FAST [get_ports {ddr3_reset_n}]
set_property IOSTANDARD LVCMOS15 [get_ports {ddr3_reset_n}]
set_property PACKAGE_PIN W6 [get_ports {ddr3_reset_n}]

# PadFunction: IO_L14P_T2_SRCC_34 
set_property SLEW FAST [get_ports {ddr3_cke[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_cke[0]}]
set_property PACKAGE_PIN T5 [get_ports {ddr3_cke[0]}]

# PadFunction: IO_L14N_T2_SRCC_34 
set_property SLEW FAST [get_ports {ddr3_odt[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_odt[0]}]
set_property PACKAGE_PIN U5 [get_ports {ddr3_odt[0]}]

# PadFunction: IO_L8P_T1_34 
set_property SLEW FAST [get_ports {ddr3_cs_n[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_cs_n[0]}]
set_property PACKAGE_PIN AB3 [get_ports {ddr3_cs_n[0]}]

# PadFunction: IO_L4N_T0_35 
set_property SLEW FAST [get_ports {ddr3_dm[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dm[0]}]
set_property PACKAGE_PIN D2 [get_ports {ddr3_dm[0]}]

# PadFunction: IO_L8N_T1_AD14N_35 
set_property SLEW FAST [get_ports {ddr3_dm[1]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dm[1]}]
set_property PACKAGE_PIN G2 [get_ports {ddr3_dm[1]}]

# PadFunction: IO_L16N_T2_35 
set_property SLEW FAST [get_ports {ddr3_dm[2]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dm[2]}]
set_property PACKAGE_PIN M2 [get_ports {ddr3_dm[2]}]

# PadFunction: IO_L23N_T3_35 
set_property SLEW FAST [get_ports {ddr3_dm[3]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dm[3]}]
set_property PACKAGE_PIN M5 [get_ports {ddr3_dm[3]}]

# PadFunction: IO_L3P_T0_DQS_AD5P_35 
set_property SLEW FAST [get_ports {ddr3_dqs_p[0]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dqs_p[0]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_p[0]}]
set_property PACKAGE_PIN E1 [get_ports {ddr3_dqs_p[0]}]

# PadFunction: IO_L3N_T0_DQS_AD5N_35 
set_property SLEW FAST [get_ports {ddr3_dqs_n[0]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dqs_n[0]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_n[0]}]
set_property PACKAGE_PIN D1 [get_ports {ddr3_dqs_n[0]}]

# PadFunction: IO_L9P_T1_DQS_AD7P_35 
set_property SLEW FAST [get_ports {ddr3_dqs_p[1]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dqs_p[1]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_p[1]}]
set_property PACKAGE_PIN K2 [get_ports {ddr3_dqs_p[1]}]

# PadFunction: IO_L9N_T1_DQS_AD7N_35 
set_property SLEW FAST [get_ports {ddr3_dqs_n[1]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dqs_n[1]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_n[1]}]
set_property PACKAGE_PIN J2 [get_ports {ddr3_dqs_n[1]}]

# PadFunction: IO_L15P_T2_DQS_35 
set_property SLEW FAST [get_ports {ddr3_dqs_p[2]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dqs_p[2]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_p[2]}]
set_property PACKAGE_PIN M1 [get_ports {ddr3_dqs_p[2]}]

# PadFunction: IO_L15N_T2_DQS_35 
set_property SLEW FAST [get_ports {ddr3_dqs_n[2]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dqs_n[2]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_n[2]}]
set_property PACKAGE_PIN L1 [get_ports {ddr3_dqs_n[2]}]

# PadFunction: IO_L21P_T3_DQS_35 
set_property SLEW FAST [get_ports {ddr3_dqs_p[3]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dqs_p[3]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_p[3]}]
set_property PACKAGE_PIN P5 [get_ports {ddr3_dqs_p[3]}]

# PadFunction: IO_L21N_T3_DQS_35 
set_property SLEW FAST [get_ports {ddr3_dqs_n[3]}]
set_property IN_TERM UNTUNED_SPLIT_50 [get_ports {ddr3_dqs_n[3]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_n[3]}]
set_property PACKAGE_PIN P4 [get_ports {ddr3_dqs_n[3]}]

# PadFunction: IO_L3P_T0_DQS_34 
set_property SLEW FAST [get_ports {ddr3_ck_p[0]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_ck_p[0]}]
set_property PACKAGE_PIN R3 [get_ports {ddr3_ck_p[0]}]

# PadFunction: IO_L3N_T0_DQS_34 
set_property SLEW FAST [get_ports {ddr3_ck_n[0]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_ck_n[0]}]
set_property PACKAGE_PIN R2 [get_ports {ddr3_ck_n[0]}]





