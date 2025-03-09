## Clock Signals
set_property -dict {PACKAGE_PIN F22 IOSTANDARD LVCMOS33} [get_ports i_clk]
create_clock -period 20.000 -name sys_clk_pin -waveform {0.000 10.000} -add [get_ports i_clk]

## Reset
set_property -dict {PACKAGE_PIN U26 IOSTANDARD LVCMOS33} [get_ports i_rst_n]

## LEDs
set_property -dict {PACKAGE_PIN R26 IOSTANDARD LVCMOS33} [get_ports {led[0]}]
set_property -dict {PACKAGE_PIN P26 IOSTANDARD LVCMOS33} [get_ports {led[1]}]
set_property -dict {PACKAGE_PIN N26 IOSTANDARD LVCMOS33} [get_ports {led[2]}]

## DDR3

# PadFunction: IO_L10P_T1_34 
set_property SLEW FAST [get_ports {ddr3_dq[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[0]}]
set_property PACKAGE_PIN W1 [get_ports {ddr3_dq[0]}]

# PadFunction: IO_L8P_T1_34 
set_property SLEW FAST [get_ports {ddr3_dq[1]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[1]}]
set_property PACKAGE_PIN V2 [get_ports {ddr3_dq[1]}]

# PadFunction: IO_L10N_T1_34 
set_property SLEW FAST [get_ports {ddr3_dq[2]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[2]}]
set_property PACKAGE_PIN Y1 [get_ports {ddr3_dq[2]}]

# PadFunction: IO_L7P_T1_34 
set_property SLEW FAST [get_ports {ddr3_dq[3]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[3]}]
set_property PACKAGE_PIN Y3 [get_ports {ddr3_dq[3]}]

# PadFunction: IO_L11N_T1_SRCC_34 
set_property SLEW FAST [get_ports {ddr3_dq[4]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[4]}]
set_property PACKAGE_PIN AC2 [get_ports {ddr3_dq[4]}]

# PadFunction: IO_L7N_T1_34 
set_property SLEW FAST [get_ports {ddr3_dq[5]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[5]}]
set_property PACKAGE_PIN Y2 [get_ports {ddr3_dq[5]}]

# PadFunction: IO_L11P_T1_SRCC_34 
set_property SLEW FAST [get_ports {ddr3_dq[6]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[6]}]
set_property PACKAGE_PIN AB2 [get_ports {ddr3_dq[6]}]

# PadFunction: IO_L12P_T1_MRCC_34 
set_property SLEW FAST [get_ports {ddr3_dq[7]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[7]}]
set_property PACKAGE_PIN AA3 [get_ports {ddr3_dq[7]}]

# PadFunction: IO_L2N_T0_34 
set_property SLEW FAST [get_ports {ddr3_dq[8]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[8]}]
set_property PACKAGE_PIN U1 [get_ports {ddr3_dq[8]}]

# PadFunction: IO_L6P_T0_34 
set_property SLEW FAST [get_ports {ddr3_dq[9]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[9]}]
set_property PACKAGE_PIN V4 [get_ports {ddr3_dq[9]}]

# PadFunction: IO_L1P_T0_34 
set_property SLEW FAST [get_ports {ddr3_dq[10]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[10]}]
set_property PACKAGE_PIN U6 [get_ports {ddr3_dq[10]}]

# PadFunction: IO_L4N_T0_34 
set_property SLEW FAST [get_ports {ddr3_dq[11]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[11]}]
set_property PACKAGE_PIN W3 [get_ports {ddr3_dq[11]}]

# PadFunction: IO_L5N_T0_34 
set_property SLEW FAST [get_ports {ddr3_dq[12]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[12]}]
set_property PACKAGE_PIN V6 [get_ports {ddr3_dq[12]}]

# PadFunction: IO_L2P_T0_34 
set_property SLEW FAST [get_ports {ddr3_dq[13]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[13]}]
set_property PACKAGE_PIN U2 [get_ports {ddr3_dq[13]}]

# PadFunction: IO_L5P_T0_34 
set_property SLEW FAST [get_ports {ddr3_dq[14]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[14]}]
set_property PACKAGE_PIN U7 [get_ports {ddr3_dq[14]}]

# PadFunction: IO_L1N_T0_34 
set_property SLEW FAST [get_ports {ddr3_dq[15]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[15]}]
set_property PACKAGE_PIN U5 [get_ports {ddr3_dq[15]}]

# PadFunction: IO_L17P_T2_34 
set_property SLEW FAST [get_ports {ddr3_addr[13]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[13]}]
set_property PACKAGE_PIN Y6 [get_ports {ddr3_addr[13]}]

# PadFunction: IO_L13N_T2_MRCC_34 
set_property SLEW FAST [get_ports {ddr3_addr[12]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[12]}]
set_property PACKAGE_PIN AB4 [get_ports {ddr3_addr[12]}]

# PadFunction: IO_L18N_T2_34 
set_property SLEW FAST [get_ports {ddr3_addr[11]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[11]}]
set_property PACKAGE_PIN AD5 [get_ports {ddr3_addr[11]}]

# PadFunction: IO_L22P_T3_34 
set_property SLEW FAST [get_ports {ddr3_addr[10]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[10]}]
set_property PACKAGE_PIN AE3 [get_ports {ddr3_addr[10]}]

# PadFunction: IO_L23P_T3_34 
set_property SLEW FAST [get_ports {ddr3_addr[9]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[9]}]
set_property PACKAGE_PIN AE6 [get_ports {ddr3_addr[9]}]

# PadFunction: IO_L13P_T2_MRCC_34 
set_property SLEW FAST [get_ports {ddr3_addr[8]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[8]}]
set_property PACKAGE_PIN AA4 [get_ports {ddr3_addr[8]}]

# PadFunction: IO_L17N_T2_34 
set_property SLEW FAST [get_ports {ddr3_addr[7]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[7]}]
set_property PACKAGE_PIN Y5 [get_ports {ddr3_addr[7]}]

# PadFunction: IO_L22N_T3_34 
set_property SLEW FAST [get_ports {ddr3_addr[6]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[6]}]
set_property PACKAGE_PIN AE2 [get_ports {ddr3_addr[6]}]

# PadFunction: IO_L16P_T2_34 
set_property SLEW FAST [get_ports {ddr3_addr[5]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[5]}]
set_property PACKAGE_PIN AB6 [get_ports {ddr3_addr[5]}]

# PadFunction: IO_L19P_T3_34 
set_property SLEW FAST [get_ports {ddr3_addr[4]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[4]}]
set_property PACKAGE_PIN AD4 [get_ports {ddr3_addr[4]}]

# PadFunction: IO_L16N_T2_34 
set_property SLEW FAST [get_ports {ddr3_addr[3]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[3]}]
set_property PACKAGE_PIN AC6 [get_ports {ddr3_addr[3]}]

# PadFunction: IO_L18P_T2_34 
set_property SLEW FAST [get_ports {ddr3_addr[2]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[2]}]
set_property PACKAGE_PIN AD6 [get_ports {ddr3_addr[2]}]

# PadFunction: IO_L24N_T3_34 
set_property SLEW FAST [get_ports {ddr3_addr[1]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[1]}]
set_property PACKAGE_PIN AF2 [get_ports {ddr3_addr[1]}]

# PadFunction: IO_L21P_T3_DQS_34 
set_property SLEW FAST [get_ports {ddr3_addr[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[0]}]
set_property PACKAGE_PIN AF5 [get_ports {ddr3_addr[0]}]

# PadFunction: IO_L23N_T3_34 
set_property SLEW FAST [get_ports {ddr3_ba[2]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_ba[2]}]
set_property PACKAGE_PIN AE5 [get_ports {ddr3_ba[2]}]

# PadFunction: IO_L20N_T3_34 
set_property SLEW FAST [get_ports {ddr3_ba[1]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_ba[1]}]
set_property PACKAGE_PIN AE1 [get_ports {ddr3_ba[1]}]

# PadFunction: IO_L19N_T3_VREF_34 
set_property SLEW FAST [get_ports {ddr3_ba[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_ba[0]}]
set_property PACKAGE_PIN AD3 [get_ports {ddr3_ba[0]}]

# PadFunction: IO_L14N_T2_SRCC_34 
set_property SLEW FAST [get_ports {ddr3_ras_n}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_ras_n}]
set_property PACKAGE_PIN AC3 [get_ports {ddr3_ras_n}]

# PadFunction: IO_L14P_T2_SRCC_34 
set_property SLEW FAST [get_ports {ddr3_cas_n}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_cas_n}]
set_property PACKAGE_PIN AC4 [get_ports {ddr3_cas_n}]

# PadFunction: IO_L21N_T3_DQS_34 
set_property SLEW FAST [get_ports {ddr3_we_n}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_we_n}]
set_property PACKAGE_PIN AF4 [get_ports {ddr3_we_n}]

# PadFunction: IO_L6N_T0_VREF_34 
set_property SLEW FAST [get_ports {ddr3_reset_n}]
set_property IOSTANDARD LVCMOS15 [get_ports {ddr3_reset_n}]
set_property PACKAGE_PIN W4 [get_ports {ddr3_reset_n}]

# PadFunction: IO_L20P_T3_34 
set_property SLEW FAST [get_ports {ddr3_cke}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_cke}]
set_property PACKAGE_PIN AD1 [get_ports {ddr3_cke}]

# PadFunction: IO_L24P_T3_34 
set_property SLEW FAST [get_ports {ddr3_odt}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_odt}]
set_property PACKAGE_PIN AF3 [get_ports {ddr3_odt}]

# PadFunction: IO_L8N_T1_34 
set_property SLEW FAST [get_ports {ddr3_dm[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dm[0]}]
set_property PACKAGE_PIN V1 [get_ports {ddr3_dm[0]}]

# PadFunction: IO_L4P_T0_34 
set_property SLEW FAST [get_ports {ddr3_dm[1]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dm[1]}]
set_property PACKAGE_PIN V3 [get_ports {ddr3_dm[1]}]

# PadFunction: IO_L9P_T1_DQS_34 
set_property SLEW FAST [get_ports {ddr3_dqs_p[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dqs_p[0]}]
set_property PACKAGE_PIN AB1 [get_ports {ddr3_dqs_p[0]}]

# PadFunction: IO_L9N_T1_DQS_34 
set_property SLEW FAST [get_ports {ddr3_dqs_n[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dqs_n[0]}]
set_property PACKAGE_PIN AC1 [get_ports {ddr3_dqs_n[0]}]

# PadFunction: IO_L3P_T0_DQS_34 
set_property SLEW FAST [get_ports {ddr3_dqs_p[1]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dqs_p[1]}]
set_property PACKAGE_PIN W6 [get_ports {ddr3_dqs_p[1]}]

# PadFunction: IO_L3N_T0_DQS_34 
set_property SLEW FAST [get_ports {ddr3_dqs_n[1]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dqs_n[1]}]
set_property PACKAGE_PIN W5 [get_ports {ddr3_dqs_n[1]}]

# PadFunction: IO_L15P_T2_DQS_34 
set_property SLEW FAST [get_ports {ddr3_ck_p}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_ck_p}]
set_property PACKAGE_PIN AA5 [get_ports {ddr3_ck_p}]

# PadFunction: IO_L15N_T2_DQS_34 
set_property SLEW FAST [get_ports {ddr3_ck_n}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_ck_n}]
set_property PACKAGE_PIN AB5 [get_ports {ddr3_ck_n}]


