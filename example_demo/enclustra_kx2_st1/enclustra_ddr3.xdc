################################################################################
# IO constraints
################################################################################
# cpu_reset_n:0
set_property LOC C22 [get_ports {i_rst_n}]
set_property IOSTANDARD LVCMOS18 [get_ports {i_rst_n}]

# clk200:0.p
set_property LOC AB11 [get_ports {i_clk200_p}]
set_property IOSTANDARD LVDS [get_ports {i_clk200_p}]

# clk200:0.n
set_property LOC AC11 [get_ports {i_clk200_n}]
set_property IOSTANDARD LVDS [get_ports {i_clk200_n}]

# serial:0.tx
set_property LOC A20 [get_ports {tx}]
set_property IOSTANDARD LVCMOS18 [get_ports {tx}]

# serial:0.rx
set_property LOC B20 [get_ports {rx}]
set_property IOSTANDARD LVCMOS18 [get_ports {rx}]

# ddram:0.a
set_property LOC AE11 [get_ports {ddr3_addr[0]}]
set_property SLEW FAST [get_ports {ddr3_addr[0]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_addr[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[0]}]

# ddram:0.a
set_property LOC AF9 [get_ports {ddr3_addr[1]}]
set_property SLEW FAST [get_ports {ddr3_addr[1]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_addr[1]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[1]}]

# ddram:0.a
set_property LOC AD10 [get_ports {ddr3_addr[2]}]
set_property SLEW FAST [get_ports {ddr3_addr[2]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_addr[2]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[2]}]

# ddram:0.a
set_property LOC AB10 [get_ports {ddr3_addr[3]}]
set_property SLEW FAST [get_ports {ddr3_addr[3]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_addr[3]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[3]}]

# ddram:0.a
set_property LOC AA9 [get_ports {ddr3_addr[4]}]
set_property SLEW FAST [get_ports {ddr3_addr[4]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_addr[4]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[4]}]

# ddram:0.a
set_property LOC AB9 [get_ports {ddr3_addr[5]}]
set_property SLEW FAST [get_ports {ddr3_addr[5]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_addr[5]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[5]}]

# ddram:0.a
set_property LOC AA8 [get_ports {ddr3_addr[6]}]
set_property SLEW FAST [get_ports {ddr3_addr[6]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_addr[6]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[6]}]

# ddram:0.a
set_property LOC AC8 [get_ports {ddr3_addr[7]}]
set_property SLEW FAST [get_ports {ddr3_addr[7]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_addr[7]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[7]}]

# ddram:0.a
set_property LOC AA7 [get_ports {ddr3_addr[8]}]
set_property SLEW FAST [get_ports {ddr3_addr[8]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_addr[8]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[8]}]

# ddram:0.a
set_property LOC AE8 [get_ports {ddr3_addr[9]}]
set_property SLEW FAST [get_ports {ddr3_addr[9]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_addr[9]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[9]}]

# ddram:0.a
set_property LOC AF10 [get_ports {ddr3_addr[10]}]
set_property SLEW FAST [get_ports {ddr3_addr[10]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_addr[10]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[10]}]

# ddram:0.a
set_property LOC AD8 [get_ports {ddr3_addr[11]}]
set_property SLEW FAST [get_ports {ddr3_addr[11]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_addr[11]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[11]}]

# ddram:0.a
set_property LOC AE10 [get_ports {ddr3_addr[12]}]
set_property SLEW FAST [get_ports {ddr3_addr[12]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_addr[12]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[12]}]

# ddram:0.a
set_property LOC AF8 [get_ports {ddr3_addr[13]}]
set_property SLEW FAST [get_ports {ddr3_addr[13]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_addr[13]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[13]}]

# ddram:0.a
set_property LOC AC7 [get_ports {ddr3_addr[14]}]
set_property SLEW FAST [get_ports {ddr3_addr[14]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_addr[14]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_addr[14]}]

# ddram:0.ba
set_property LOC AD11 [get_ports {ddr3_ba[0]}]
set_property SLEW FAST [get_ports {ddr3_ba[0]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_ba[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_ba[0]}]

# ddram:0.ba
set_property LOC AA10 [get_ports {ddr3_ba[1]}]
set_property SLEW FAST [get_ports {ddr3_ba[1]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_ba[1]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_ba[1]}]

# ddram:0.ba
set_property LOC AF12 [get_ports {ddr3_ba[2]}]
set_property SLEW FAST [get_ports {ddr3_ba[2]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_ba[2]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_ba[2]}]

# ddram:0.ras_n
set_property LOC AE13 [get_ports {ddr3_ras_n}]
set_property SLEW FAST [get_ports {ddr3_ras_n}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_ras_n}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_ras_n}]

# ddram:0.cas_n
set_property LOC AE12 [get_ports {ddr3_cas_n}]
set_property SLEW FAST [get_ports {ddr3_cas_n}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_cas_n}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_cas_n}]

# ddram:0.we_n
set_property LOC AA12 [get_ports {ddr3_we_n}]
set_property SLEW FAST [get_ports {ddr3_we_n}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_we_n}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_we_n}]

# ddram:0.cs_n
set_property LOC Y12 [get_ports {ddr3_cs_n}]
set_property SLEW FAST [get_ports {ddr3_cs_n}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_cs_n}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_cs_n}]

# ddram:0.dm
set_property LOC Y3 [get_ports {ddr3_dm[0]}]
set_property SLEW FAST [get_ports {ddr3_dm[0]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dm[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dm[0]}]

# ddram:0.dm
set_property LOC U5 [get_ports {ddr3_dm[1]}]
set_property SLEW FAST [get_ports {ddr3_dm[1]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dm[1]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dm[1]}]

# ddram:0.dm
set_property LOC AD4 [get_ports {ddr3_dm[2]}]
set_property SLEW FAST [get_ports {ddr3_dm[2]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dm[2]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dm[2]}]

# ddram:0.dm
set_property LOC AC4 [get_ports {ddr3_dm[3]}]
set_property SLEW FAST [get_ports {ddr3_dm[3]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dm[3]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dm[3]}]

# ddram:0.dm
set_property LOC AF19 [get_ports {ddr3_dm[4]}]
set_property SLEW FAST [get_ports {ddr3_dm[4]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dm[4]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dm[4]}]

# ddram:0.dm
set_property LOC AC16 [get_ports {ddr3_dm[5]}]
set_property SLEW FAST [get_ports {ddr3_dm[5]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dm[5]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dm[5]}]

# ddram:0.dm
set_property LOC AB19 [get_ports {ddr3_dm[6]}]
set_property SLEW FAST [get_ports {ddr3_dm[6]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dm[6]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dm[6]}]

# ddram:0.dm
set_property LOC V14 [get_ports {ddr3_dm[7]}]
set_property SLEW FAST [get_ports {ddr3_dm[7]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dm[7]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dm[7]}]

# ddram:0.dq
set_property LOC AA2 [get_ports {ddr3_dq[0]}]
set_property SLEW FAST [get_ports {ddr3_dq[0]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[0]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[0]}]

# ddram:0.dq
set_property LOC Y2 [get_ports {ddr3_dq[1]}]
set_property SLEW FAST [get_ports {ddr3_dq[1]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[1]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[1]}]

# ddram:0.dq
set_property LOC AB2 [get_ports {ddr3_dq[2]}]
set_property SLEW FAST [get_ports {ddr3_dq[2]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[2]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[2]}]

# ddram:0.dq
set_property LOC V1 [get_ports {ddr3_dq[3]}]
set_property SLEW FAST [get_ports {ddr3_dq[3]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[3]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[3]}]

# ddram:0.dq
set_property LOC Y1 [get_ports {ddr3_dq[4]}]
set_property SLEW FAST [get_ports {ddr3_dq[4]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[4]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[4]}]

# ddram:0.dq
set_property LOC W1 [get_ports {ddr3_dq[5]}]
set_property SLEW FAST [get_ports {ddr3_dq[5]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[5]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[5]}]

# ddram:0.dq
set_property LOC AC2 [get_ports {ddr3_dq[6]}]
set_property SLEW FAST [get_ports {ddr3_dq[6]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[6]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[6]}]

# ddram:0.dq
set_property LOC V2 [get_ports {ddr3_dq[7]}]
set_property SLEW FAST [get_ports {ddr3_dq[7]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[7]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[7]}]

# ddram:0.dq
set_property LOC W3 [get_ports {ddr3_dq[8]}]
set_property SLEW FAST [get_ports {ddr3_dq[8]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[8]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[8]}]

# ddram:0.dq
set_property LOC V3 [get_ports {ddr3_dq[9]}]
set_property SLEW FAST [get_ports {ddr3_dq[9]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[9]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[9]}]

# ddram:0.dq
set_property LOC U1 [get_ports {ddr3_dq[10]}]
set_property SLEW FAST [get_ports {ddr3_dq[10]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[10]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[10]}]

# ddram:0.dq
set_property LOC U7 [get_ports {ddr3_dq[11]}]
set_property SLEW FAST [get_ports {ddr3_dq[11]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[11]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[11]}]

# ddram:0.dq
set_property LOC U6 [get_ports {ddr3_dq[12]}]
set_property SLEW FAST [get_ports {ddr3_dq[12]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[12]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[12]}]

# ddram:0.dq
set_property LOC V4 [get_ports {ddr3_dq[13]}]
set_property SLEW FAST [get_ports {ddr3_dq[13]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[13]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[13]}]

# ddram:0.dq
set_property LOC V6 [get_ports {ddr3_dq[14]}]
set_property SLEW FAST [get_ports {ddr3_dq[14]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[14]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[14]}]

# ddram:0.dq
set_property LOC U2 [get_ports {ddr3_dq[15]}]
set_property SLEW FAST [get_ports {ddr3_dq[15]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[15]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[15]}]

# ddram:0.dq
set_property LOC AE3 [get_ports {ddr3_dq[16]}]
set_property SLEW FAST [get_ports {ddr3_dq[16]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[16]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[16]}]

# ddram:0.dq
set_property LOC AE6 [get_ports {ddr3_dq[17]}]
set_property SLEW FAST [get_ports {ddr3_dq[17]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[17]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[17]}]

# ddram:0.dq
set_property LOC AF3 [get_ports {ddr3_dq[18]}]
set_property SLEW FAST [get_ports {ddr3_dq[18]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[18]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[18]}]

# ddram:0.dq
set_property LOC AD1 [get_ports {ddr3_dq[19]}]
set_property SLEW FAST [get_ports {ddr3_dq[19]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[19]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[19]}]

# ddram:0.dq
set_property LOC AE1 [get_ports {ddr3_dq[20]}]
set_property SLEW FAST [get_ports {ddr3_dq[20]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[20]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[20]}]

# ddram:0.dq
set_property LOC AE2 [get_ports {ddr3_dq[21]}]
set_property SLEW FAST [get_ports {ddr3_dq[21]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[21]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[21]}]

# ddram:0.dq
set_property LOC AF2 [get_ports {ddr3_dq[22]}]
set_property SLEW FAST [get_ports {ddr3_dq[22]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[22]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[22]}]

# ddram:0.dq
set_property LOC AE5 [get_ports {ddr3_dq[23]}]
set_property SLEW FAST [get_ports {ddr3_dq[23]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[23]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[23]}]

# ddram:0.dq
set_property LOC AD5 [get_ports {ddr3_dq[24]}]
set_property SLEW FAST [get_ports {ddr3_dq[24]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[24]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[24]}]

# ddram:0.dq
set_property LOC Y5 [get_ports {ddr3_dq[25]}]
set_property SLEW FAST [get_ports {ddr3_dq[25]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[25]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[25]}]

# ddram:0.dq
set_property LOC AC6 [get_ports {ddr3_dq[26]}]
set_property SLEW FAST [get_ports {ddr3_dq[26]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[26]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[26]}]

# ddram:0.dq
set_property LOC Y6 [get_ports {ddr3_dq[27]}]
set_property SLEW FAST [get_ports {ddr3_dq[27]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[27]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[27]}]

# ddram:0.dq
set_property LOC AB4 [get_ports {ddr3_dq[28]}]
set_property SLEW FAST [get_ports {ddr3_dq[28]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[28]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[28]}]

# ddram:0.dq
set_property LOC AD6 [get_ports {ddr3_dq[29]}]
set_property SLEW FAST [get_ports {ddr3_dq[29]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[29]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[29]}]

# ddram:0.dq
set_property LOC AB6 [get_ports {ddr3_dq[30]}]
set_property SLEW FAST [get_ports {ddr3_dq[30]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[30]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[30]}]

# ddram:0.dq
set_property LOC AC3 [get_ports {ddr3_dq[31]}]
set_property SLEW FAST [get_ports {ddr3_dq[31]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[31]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[31]}]

# ddram:0.dq
set_property LOC AD16 [get_ports {ddr3_dq[32]}]
set_property SLEW FAST [get_ports {ddr3_dq[32]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[32]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[32]}]

# ddram:0.dq
set_property LOC AE17 [get_ports {ddr3_dq[33]}]
set_property SLEW FAST [get_ports {ddr3_dq[33]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[33]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[33]}]

# ddram:0.dq
set_property LOC AF15 [get_ports {ddr3_dq[34]}]
set_property SLEW FAST [get_ports {ddr3_dq[34]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[34]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[34]}]

# ddram:0.dq
set_property LOC AF20 [get_ports {ddr3_dq[35]}]
set_property SLEW FAST [get_ports {ddr3_dq[35]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[35]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[35]}]

# ddram:0.dq
set_property LOC AD15 [get_ports {ddr3_dq[36]}]
set_property SLEW FAST [get_ports {ddr3_dq[36]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[36]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[36]}]

# ddram:0.dq
set_property LOC AF14 [get_ports {ddr3_dq[37]}]
set_property SLEW FAST [get_ports {ddr3_dq[37]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[37]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[37]}]

# ddram:0.dq
set_property LOC AE15 [get_ports {ddr3_dq[38]}]
set_property SLEW FAST [get_ports {ddr3_dq[38]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[38]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[38]}]

# ddram:0.dq
set_property LOC AF17 [get_ports {ddr3_dq[39]}]
set_property SLEW FAST [get_ports {ddr3_dq[39]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[39]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[39]}]

# ddram:0.dq
set_property LOC AA14 [get_ports {ddr3_dq[40]}]
set_property SLEW FAST [get_ports {ddr3_dq[40]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[40]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[40]}]

# ddram:0.dq
set_property LOC AA15 [get_ports {ddr3_dq[41]}]
set_property SLEW FAST [get_ports {ddr3_dq[41]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[41]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[41]}]

# ddram:0.dq
set_property LOC AC14 [get_ports {ddr3_dq[42]}]
set_property SLEW FAST [get_ports {ddr3_dq[42]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[42]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[42]}]

# ddram:0.dq
set_property LOC AD14 [get_ports {ddr3_dq[43]}]
set_property SLEW FAST [get_ports {ddr3_dq[43]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[43]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[43]}]

# ddram:0.dq
set_property LOC AB14 [get_ports {ddr3_dq[44]}]
set_property SLEW FAST [get_ports {ddr3_dq[44]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[44]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[44]}]

# ddram:0.dq
set_property LOC AB15 [get_ports {ddr3_dq[45]}]
set_property SLEW FAST [get_ports {ddr3_dq[45]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[45]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[45]}]

# ddram:0.dq
set_property LOC AA17 [get_ports {ddr3_dq[46]}]
set_property SLEW FAST [get_ports {ddr3_dq[46]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[46]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[46]}]

# ddram:0.dq
set_property LOC AA18 [get_ports {ddr3_dq[47]}]
set_property SLEW FAST [get_ports {ddr3_dq[47]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[47]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[47]}]

# ddram:0.dq
set_property LOC AB20 [get_ports {ddr3_dq[48]}]
set_property SLEW FAST [get_ports {ddr3_dq[48]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[48]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[48]}]

# ddram:0.dq
set_property LOC AD19 [get_ports {ddr3_dq[49]}]
set_property SLEW FAST [get_ports {ddr3_dq[49]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[49]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[49]}]

# ddram:0.dq
set_property LOC AC19 [get_ports {ddr3_dq[50]}]
set_property SLEW FAST [get_ports {ddr3_dq[50]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[50]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[50]}]

# ddram:0.dq
set_property LOC AA20 [get_ports {ddr3_dq[51]}]
set_property SLEW FAST [get_ports {ddr3_dq[51]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[51]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[51]}]

# ddram:0.dq
set_property LOC AA19 [get_ports {ddr3_dq[52]}]
set_property SLEW FAST [get_ports {ddr3_dq[52]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[52]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[52]}]

# ddram:0.dq
set_property LOC AC17 [get_ports {ddr3_dq[53]}]
set_property SLEW FAST [get_ports {ddr3_dq[53]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[53]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[53]}]

# ddram:0.dq
set_property LOC AD18 [get_ports {ddr3_dq[54]}]
set_property SLEW FAST [get_ports {ddr3_dq[54]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[54]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[54]}]

# ddram:0.dq
set_property LOC AB17 [get_ports {ddr3_dq[55]}]
set_property SLEW FAST [get_ports {ddr3_dq[55]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[55]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[55]}]

# ddram:0.dq
set_property LOC W15 [get_ports {ddr3_dq[56]}]
set_property SLEW FAST [get_ports {ddr3_dq[56]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[56]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[56]}]

# ddram:0.dq
set_property LOC W16 [get_ports {ddr3_dq[57]}]
set_property SLEW FAST [get_ports {ddr3_dq[57]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[57]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[57]}]

# ddram:0.dq
set_property LOC W14 [get_ports {ddr3_dq[58]}]
set_property SLEW FAST [get_ports {ddr3_dq[58]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[58]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[58]}]

# ddram:0.dq
set_property LOC V16 [get_ports {ddr3_dq[59]}]
set_property SLEW FAST [get_ports {ddr3_dq[59]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[59]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[59]}]

# ddram:0.dq
set_property LOC V19 [get_ports {ddr3_dq[60]}]
set_property SLEW FAST [get_ports {ddr3_dq[60]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[60]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[60]}]

# ddram:0.dq
set_property LOC V17 [get_ports {ddr3_dq[61]}]
set_property SLEW FAST [get_ports {ddr3_dq[61]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[61]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[61]}]

# ddram:0.dq
set_property LOC V18 [get_ports {ddr3_dq[62]}]
set_property SLEW FAST [get_ports {ddr3_dq[62]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[62]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[62]}]

# ddram:0.dq
set_property LOC Y17 [get_ports {ddr3_dq[63]}]
set_property SLEW FAST [get_ports {ddr3_dq[63]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dq[63]}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_dq[63]}]

# ddram:0.dqs_p
set_property LOC AB1 [get_ports {ddr3_dqs_p[0]}]
set_property SLEW FAST [get_ports {ddr3_dqs_p[0]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dqs_p[0]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_p[0]}]

# ddram:0.dqs_p
set_property LOC W6 [get_ports {ddr3_dqs_p[1]}]
set_property SLEW FAST [get_ports {ddr3_dqs_p[1]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dqs_p[1]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_p[1]}]

# ddram:0.dqs_p
set_property LOC AF5 [get_ports {ddr3_dqs_p[2]}]
set_property SLEW FAST [get_ports {ddr3_dqs_p[2]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dqs_p[2]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_p[2]}]

# ddram:0.dqs_p
set_property LOC AA5 [get_ports {ddr3_dqs_p[3]}]
set_property SLEW FAST [get_ports {ddr3_dqs_p[3]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dqs_p[3]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_p[3]}]

# ddram:0.dqs_p
set_property LOC AE18 [get_ports {ddr3_dqs_p[4]}]
set_property SLEW FAST [get_ports {ddr3_dqs_p[4]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dqs_p[4]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_p[4]}]

# ddram:0.dqs_p
set_property LOC Y15 [get_ports {ddr3_dqs_p[5]}]
set_property SLEW FAST [get_ports {ddr3_dqs_p[5]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dqs_p[5]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_p[5]}]

# ddram:0.dqs_p
set_property LOC AD20 [get_ports {ddr3_dqs_p[6]}]
set_property SLEW FAST [get_ports {ddr3_dqs_p[6]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dqs_p[6]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_p[6]}]

# ddram:0.dqs_p
set_property LOC W18 [get_ports {ddr3_dqs_p[7]}]
set_property SLEW FAST [get_ports {ddr3_dqs_p[7]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dqs_p[7]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_p[7]}]

# ddram:0.dqs_n
set_property LOC AC1 [get_ports {ddr3_dqs_n[0]}]
set_property SLEW FAST [get_ports {ddr3_dqs_n[0]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dqs_n[0]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_n[0]}]

# ddram:0.dqs_n
set_property LOC W5 [get_ports {ddr3_dqs_n[1]}]
set_property SLEW FAST [get_ports {ddr3_dqs_n[1]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dqs_n[1]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_n[1]}]

# ddram:0.dqs_n
set_property LOC AF4 [get_ports {ddr3_dqs_n[2]}]
set_property SLEW FAST [get_ports {ddr3_dqs_n[2]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dqs_n[2]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_n[2]}]

# ddram:0.dqs_n
set_property LOC AB5 [get_ports {ddr3_dqs_n[3]}]
set_property SLEW FAST [get_ports {ddr3_dqs_n[3]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dqs_n[3]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_n[3]}]

# ddram:0.dqs_n
set_property LOC AF18 [get_ports {ddr3_dqs_n[4]}]
set_property SLEW FAST [get_ports {ddr3_dqs_n[4]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dqs_n[4]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_n[4]}]

# ddram:0.dqs_n
set_property LOC Y16 [get_ports {ddr3_dqs_n[5]}]
set_property SLEW FAST [get_ports {ddr3_dqs_n[5]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dqs_n[5]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_n[5]}]

# ddram:0.dqs_n
set_property LOC AE20 [get_ports {ddr3_dqs_n[6]}]
set_property SLEW FAST [get_ports {ddr3_dqs_n[6]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dqs_n[6]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_n[6]}]

# ddram:0.dqs_n
set_property LOC W19 [get_ports {ddr3_dqs_n[7]}]
set_property SLEW FAST [get_ports {ddr3_dqs_n[7]}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_dqs_n[7]}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_dqs_n[7]}]

# ddram:0.clk_p
set_property LOC AB12 [get_ports {ddr3_clk_p}]
set_property SLEW FAST [get_ports {ddr3_clk_p}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_clk_p}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_clk_p}]

# ddram:0.clk_n
set_property LOC AC12 [get_ports {ddr3_clk_n}]
set_property SLEW FAST [get_ports {ddr3_clk_n}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_clk_n}]
set_property IOSTANDARD DIFF_SSTL15 [get_ports {ddr3_clk_n}]

# ddram:0.cke
set_property LOC AA13 [get_ports {ddr3_cke}]
set_property SLEW FAST [get_ports {ddr3_cke}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_cke}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_cke}]

# ddram:0.odt
set_property LOC AD13 [get_ports {ddr3_odt}]
set_property SLEW FAST [get_ports {ddr3_odt}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_odt}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_odt}]

# ddram:0.reset_n
set_property LOC AB7 [get_ports {ddr3_reset_n}]
set_property SLEW FAST [get_ports {ddr3_reset_n}]
set_property VCCAUX_IO HIGH [get_ports {ddr3_reset_n}]
set_property IOSTANDARD SSTL15 [get_ports {ddr3_reset_n}]
set_property SLEW SLOW [get_ports {ddr3_reset_n}]

# user_led:0
set_property LOC U9 [get_ports {led[0]}]
set_property IOSTANDARD LVCMOS15 [get_ports {led[0]}]
set_property SLEW SLOW [get_ports {led[0]}]

# user_led:1
set_property LOC V12 [get_ports {led[1]}]
set_property IOSTANDARD LVCMOS15 [get_ports {led[1]}]
set_property SLEW SLOW [get_ports {led[1]}]

# user_led:2
set_property LOC V13 [get_ports {led[2]}]
set_property IOSTANDARD LVCMOS15 [get_ports {led[2]}]
set_property SLEW SLOW [get_ports {led[2]}]

# user_led:3
set_property LOC W13 [get_ports {led[3]}]
set_property IOSTANDARD LVCMOS15 [get_ports {led[3]}]
set_property SLEW SLOW [get_ports {led[3]}]


################################################################################
# Design constraints
################################################################################

set_property CONFIG_VOLTAGE 1.8 [current_design]

set_property CFGBVS GND [current_design]


################################################################################
# Clock constraints
################################################################################


create_clock -name i_clk200_p -period 5.0 [get_ports i_clk200_p]
