############## clock define##################
create_clock -period 5.000 [get_ports sys_clk_p]
set_property IOSTANDARD DIFF_SSTL15 [get_ports sys_clk_p]
# no need to create_clock for N side (only P side) or else tool will analyze interclock oaths and show failure in timing
# https://support.xilinx.com/s/article/57109?language=en_US
#create_clock -period 5.000 [get_ports sys_clk_n]
set_property PACKAGE_PIN AE10 [get_ports sys_clk_p]
set_property PACKAGE_PIN AF10 [get_ports sys_clk_n]
set_property IOSTANDARD DIFF_SSTL15 [get_ports sys_clk_n]

############## SODIMM SPD define##################
set_property IOSTANDARD LVCMOS33 [get_ports i2c_scl]
set_property PACKAGE_PIN B20 [get_ports i2c_scl]
set_property IOSTANDARD LVCMOS33 [get_ports i2c_sda]
set_property PACKAGE_PIN C20 [get_ports i2c_sda]

############## fan define##################
set_property IOSTANDARD LVCMOS25 [get_ports fan_pwm]
set_property PACKAGE_PIN AE26 [get_ports fan_pwm]

############## key define##################
set_property PACKAGE_PIN AG27 [get_ports i_rst_n]
set_property IOSTANDARD LVCMOS25 [get_ports i_rst_n]

##############LED define##################
set_property PACKAGE_PIN A22 [get_ports {led[0]}]
set_property IOSTANDARD LVCMOS33 [get_ports {led[0]}]
set_property PACKAGE_PIN C19 [get_ports {led[1]}]
set_property IOSTANDARD LVCMOS33 [get_ports {led[1]}]
set_property PACKAGE_PIN B19 [get_ports {led[2]}]
set_property IOSTANDARD LVCMOS33 [get_ports {led[2]}]
set_property PACKAGE_PIN E18 [get_ports {led[3]}]
set_property IOSTANDARD LVCMOS33 [get_ports {led[3]}]

##############uart define###########################
set_property IOSTANDARD LVCMOS33 [get_ports uart_tx]
set_property PACKAGE_PIN AK26 [get_ports uart_tx]