# Definitional proc to organize widgets for parameters.
proc init_gui { IPINST } {
  ipgui::add_param $IPINST -name "Component_Name"
  #Adding Page
  set Page_0 [ipgui::add_page $IPINST -name "Page 0"]
  ipgui::add_param $IPINST -name "AXI_ADDR_WIDTH" -parent ${Page_0}
  ipgui::add_param $IPINST -name "AXI_DATA_WIDTH" -parent ${Page_0}
  ipgui::add_param $IPINST -name "AXI_ID_WIDTH" -parent ${Page_0}
  ipgui::add_param $IPINST -name "AXI_LSBS" -parent ${Page_0}
  ipgui::add_param $IPINST -name "BA_BITS" -parent ${Page_0}
  ipgui::add_param $IPINST -name "BYTE_LANES" -parent ${Page_0}
  ipgui::add_param $IPINST -name "COL_BITS" -parent ${Page_0}
  ipgui::add_param $IPINST -name "CONTROLLER_CLK_PERIOD" -parent ${Page_0}
  ipgui::add_param $IPINST -name "DDR3_CLK_PERIOD" -parent ${Page_0}
  ipgui::add_param $IPINST -name "DIC" -parent ${Page_0}
  ipgui::add_param $IPINST -name "DQ_BITS" -parent ${Page_0}
  ipgui::add_param $IPINST -name "ECC_ENABLE" -parent ${Page_0}
  ipgui::add_param $IPINST -name "MICRON_SIM" -parent ${Page_0}
  ipgui::add_param $IPINST -name "ODELAY_SUPPORTED" -parent ${Page_0}
  ipgui::add_param $IPINST -name "ROW_BITS" -parent ${Page_0}
  ipgui::add_param $IPINST -name "RTT_NOM" -parent ${Page_0}
  ipgui::add_param $IPINST -name "SECOND_WISHBONE" -parent ${Page_0}
  ipgui::add_param $IPINST -name "SKIP_INTERNAL_TEST" -parent ${Page_0}
  ipgui::add_param $IPINST -name "WB2_ADDR_BITS" -parent ${Page_0}
  ipgui::add_param $IPINST -name "WB2_DATA_BITS" -parent ${Page_0}
  ipgui::add_param $IPINST -name "WB_ERROR" -parent ${Page_0}
  ipgui::add_param $IPINST -name "cmd_len" -parent ${Page_0}
  ipgui::add_param $IPINST -name "serdes_ratio" -parent ${Page_0}
  ipgui::add_param $IPINST -name "wb2_sel_bits" -parent ${Page_0}
  ipgui::add_param $IPINST -name "wb_addr_bits" -parent ${Page_0}
  ipgui::add_param $IPINST -name "wb_data_bits" -parent ${Page_0}
  ipgui::add_param $IPINST -name "wb_sel_bits" -parent ${Page_0}


}

proc update_PARAM_VALUE.AXI_ADDR_WIDTH { PARAM_VALUE.AXI_ADDR_WIDTH } {
	# Procedure called to update AXI_ADDR_WIDTH when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.AXI_ADDR_WIDTH { PARAM_VALUE.AXI_ADDR_WIDTH } {
	# Procedure called to validate AXI_ADDR_WIDTH
	return true
}

proc update_PARAM_VALUE.AXI_DATA_WIDTH { PARAM_VALUE.AXI_DATA_WIDTH } {
	# Procedure called to update AXI_DATA_WIDTH when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.AXI_DATA_WIDTH { PARAM_VALUE.AXI_DATA_WIDTH } {
	# Procedure called to validate AXI_DATA_WIDTH
	return true
}

proc update_PARAM_VALUE.AXI_ID_WIDTH { PARAM_VALUE.AXI_ID_WIDTH } {
	# Procedure called to update AXI_ID_WIDTH when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.AXI_ID_WIDTH { PARAM_VALUE.AXI_ID_WIDTH } {
	# Procedure called to validate AXI_ID_WIDTH
	return true
}

proc update_PARAM_VALUE.AXI_LSBS { PARAM_VALUE.AXI_LSBS } {
	# Procedure called to update AXI_LSBS when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.AXI_LSBS { PARAM_VALUE.AXI_LSBS } {
	# Procedure called to validate AXI_LSBS
	return true
}

proc update_PARAM_VALUE.BA_BITS { PARAM_VALUE.BA_BITS } {
	# Procedure called to update BA_BITS when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.BA_BITS { PARAM_VALUE.BA_BITS } {
	# Procedure called to validate BA_BITS
	return true
}

proc update_PARAM_VALUE.BYTE_LANES { PARAM_VALUE.BYTE_LANES } {
	# Procedure called to update BYTE_LANES when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.BYTE_LANES { PARAM_VALUE.BYTE_LANES } {
	# Procedure called to validate BYTE_LANES
	return true
}

proc update_PARAM_VALUE.COL_BITS { PARAM_VALUE.COL_BITS } {
	# Procedure called to update COL_BITS when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.COL_BITS { PARAM_VALUE.COL_BITS } {
	# Procedure called to validate COL_BITS
	return true
}

proc update_PARAM_VALUE.CONTROLLER_CLK_PERIOD { PARAM_VALUE.CONTROLLER_CLK_PERIOD } {
	# Procedure called to update CONTROLLER_CLK_PERIOD when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.CONTROLLER_CLK_PERIOD { PARAM_VALUE.CONTROLLER_CLK_PERIOD } {
	# Procedure called to validate CONTROLLER_CLK_PERIOD
	return true
}

proc update_PARAM_VALUE.DDR3_CLK_PERIOD { PARAM_VALUE.DDR3_CLK_PERIOD } {
	# Procedure called to update DDR3_CLK_PERIOD when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.DDR3_CLK_PERIOD { PARAM_VALUE.DDR3_CLK_PERIOD } {
	# Procedure called to validate DDR3_CLK_PERIOD
	return true
}

proc update_PARAM_VALUE.DIC { PARAM_VALUE.DIC } {
	# Procedure called to update DIC when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.DIC { PARAM_VALUE.DIC } {
	# Procedure called to validate DIC
	return true
}

proc update_PARAM_VALUE.DQ_BITS { PARAM_VALUE.DQ_BITS } {
	# Procedure called to update DQ_BITS when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.DQ_BITS { PARAM_VALUE.DQ_BITS } {
	# Procedure called to validate DQ_BITS
	return true
}

proc update_PARAM_VALUE.ECC_ENABLE { PARAM_VALUE.ECC_ENABLE } {
	# Procedure called to update ECC_ENABLE when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.ECC_ENABLE { PARAM_VALUE.ECC_ENABLE } {
	# Procedure called to validate ECC_ENABLE
	return true
}

proc update_PARAM_VALUE.MICRON_SIM { PARAM_VALUE.MICRON_SIM } {
	# Procedure called to update MICRON_SIM when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.MICRON_SIM { PARAM_VALUE.MICRON_SIM } {
	# Procedure called to validate MICRON_SIM
	return true
}

proc update_PARAM_VALUE.ODELAY_SUPPORTED { PARAM_VALUE.ODELAY_SUPPORTED } {
	# Procedure called to update ODELAY_SUPPORTED when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.ODELAY_SUPPORTED { PARAM_VALUE.ODELAY_SUPPORTED } {
	# Procedure called to validate ODELAY_SUPPORTED
	return true
}

proc update_PARAM_VALUE.ROW_BITS { PARAM_VALUE.ROW_BITS } {
	# Procedure called to update ROW_BITS when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.ROW_BITS { PARAM_VALUE.ROW_BITS } {
	# Procedure called to validate ROW_BITS
	return true
}

proc update_PARAM_VALUE.RTT_NOM { PARAM_VALUE.RTT_NOM } {
	# Procedure called to update RTT_NOM when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.RTT_NOM { PARAM_VALUE.RTT_NOM } {
	# Procedure called to validate RTT_NOM
	return true
}

proc update_PARAM_VALUE.SECOND_WISHBONE { PARAM_VALUE.SECOND_WISHBONE } {
	# Procedure called to update SECOND_WISHBONE when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.SECOND_WISHBONE { PARAM_VALUE.SECOND_WISHBONE } {
	# Procedure called to validate SECOND_WISHBONE
	return true
}

proc update_PARAM_VALUE.SKIP_INTERNAL_TEST { PARAM_VALUE.SKIP_INTERNAL_TEST } {
	# Procedure called to update SKIP_INTERNAL_TEST when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.SKIP_INTERNAL_TEST { PARAM_VALUE.SKIP_INTERNAL_TEST } {
	# Procedure called to validate SKIP_INTERNAL_TEST
	return true
}

proc update_PARAM_VALUE.WB2_ADDR_BITS { PARAM_VALUE.WB2_ADDR_BITS } {
	# Procedure called to update WB2_ADDR_BITS when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.WB2_ADDR_BITS { PARAM_VALUE.WB2_ADDR_BITS } {
	# Procedure called to validate WB2_ADDR_BITS
	return true
}

proc update_PARAM_VALUE.WB2_DATA_BITS { PARAM_VALUE.WB2_DATA_BITS } {
	# Procedure called to update WB2_DATA_BITS when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.WB2_DATA_BITS { PARAM_VALUE.WB2_DATA_BITS } {
	# Procedure called to validate WB2_DATA_BITS
	return true
}

proc update_PARAM_VALUE.WB_ERROR { PARAM_VALUE.WB_ERROR } {
	# Procedure called to update WB_ERROR when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.WB_ERROR { PARAM_VALUE.WB_ERROR } {
	# Procedure called to validate WB_ERROR
	return true
}

proc update_PARAM_VALUE.cmd_len { PARAM_VALUE.cmd_len } {
	# Procedure called to update cmd_len when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.cmd_len { PARAM_VALUE.cmd_len } {
	# Procedure called to validate cmd_len
	return true
}

proc update_PARAM_VALUE.serdes_ratio { PARAM_VALUE.serdes_ratio } {
	# Procedure called to update serdes_ratio when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.serdes_ratio { PARAM_VALUE.serdes_ratio } {
	# Procedure called to validate serdes_ratio
	return true
}

proc update_PARAM_VALUE.wb2_sel_bits { PARAM_VALUE.wb2_sel_bits } {
	# Procedure called to update wb2_sel_bits when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.wb2_sel_bits { PARAM_VALUE.wb2_sel_bits } {
	# Procedure called to validate wb2_sel_bits
	return true
}

proc update_PARAM_VALUE.wb_addr_bits { PARAM_VALUE.wb_addr_bits } {
	# Procedure called to update wb_addr_bits when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.wb_addr_bits { PARAM_VALUE.wb_addr_bits } {
	# Procedure called to validate wb_addr_bits
	return true
}

proc update_PARAM_VALUE.wb_data_bits { PARAM_VALUE.wb_data_bits } {
	# Procedure called to update wb_data_bits when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.wb_data_bits { PARAM_VALUE.wb_data_bits } {
	# Procedure called to validate wb_data_bits
	return true
}

proc update_PARAM_VALUE.wb_sel_bits { PARAM_VALUE.wb_sel_bits } {
	# Procedure called to update wb_sel_bits when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.wb_sel_bits { PARAM_VALUE.wb_sel_bits } {
	# Procedure called to validate wb_sel_bits
	return true
}


proc update_MODELPARAM_VALUE.CONTROLLER_CLK_PERIOD { MODELPARAM_VALUE.CONTROLLER_CLK_PERIOD PARAM_VALUE.CONTROLLER_CLK_PERIOD } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.CONTROLLER_CLK_PERIOD}] ${MODELPARAM_VALUE.CONTROLLER_CLK_PERIOD}
}

proc update_MODELPARAM_VALUE.DDR3_CLK_PERIOD { MODELPARAM_VALUE.DDR3_CLK_PERIOD PARAM_VALUE.DDR3_CLK_PERIOD } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.DDR3_CLK_PERIOD}] ${MODELPARAM_VALUE.DDR3_CLK_PERIOD}
}

proc update_MODELPARAM_VALUE.ROW_BITS { MODELPARAM_VALUE.ROW_BITS PARAM_VALUE.ROW_BITS } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.ROW_BITS}] ${MODELPARAM_VALUE.ROW_BITS}
}

proc update_MODELPARAM_VALUE.COL_BITS { MODELPARAM_VALUE.COL_BITS PARAM_VALUE.COL_BITS } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.COL_BITS}] ${MODELPARAM_VALUE.COL_BITS}
}

proc update_MODELPARAM_VALUE.BA_BITS { MODELPARAM_VALUE.BA_BITS PARAM_VALUE.BA_BITS } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.BA_BITS}] ${MODELPARAM_VALUE.BA_BITS}
}

proc update_MODELPARAM_VALUE.BYTE_LANES { MODELPARAM_VALUE.BYTE_LANES PARAM_VALUE.BYTE_LANES } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.BYTE_LANES}] ${MODELPARAM_VALUE.BYTE_LANES}
}

proc update_MODELPARAM_VALUE.AXI_ID_WIDTH { MODELPARAM_VALUE.AXI_ID_WIDTH PARAM_VALUE.AXI_ID_WIDTH } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.AXI_ID_WIDTH}] ${MODELPARAM_VALUE.AXI_ID_WIDTH}
}

proc update_MODELPARAM_VALUE.WB2_ADDR_BITS { MODELPARAM_VALUE.WB2_ADDR_BITS PARAM_VALUE.WB2_ADDR_BITS } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.WB2_ADDR_BITS}] ${MODELPARAM_VALUE.WB2_ADDR_BITS}
}

proc update_MODELPARAM_VALUE.WB2_DATA_BITS { MODELPARAM_VALUE.WB2_DATA_BITS PARAM_VALUE.WB2_DATA_BITS } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.WB2_DATA_BITS}] ${MODELPARAM_VALUE.WB2_DATA_BITS}
}

proc update_MODELPARAM_VALUE.MICRON_SIM { MODELPARAM_VALUE.MICRON_SIM PARAM_VALUE.MICRON_SIM } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.MICRON_SIM}] ${MODELPARAM_VALUE.MICRON_SIM}
}

proc update_MODELPARAM_VALUE.ODELAY_SUPPORTED { MODELPARAM_VALUE.ODELAY_SUPPORTED PARAM_VALUE.ODELAY_SUPPORTED } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.ODELAY_SUPPORTED}] ${MODELPARAM_VALUE.ODELAY_SUPPORTED}
}

proc update_MODELPARAM_VALUE.SECOND_WISHBONE { MODELPARAM_VALUE.SECOND_WISHBONE PARAM_VALUE.SECOND_WISHBONE } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.SECOND_WISHBONE}] ${MODELPARAM_VALUE.SECOND_WISHBONE}
}

proc update_MODELPARAM_VALUE.WB_ERROR { MODELPARAM_VALUE.WB_ERROR PARAM_VALUE.WB_ERROR } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.WB_ERROR}] ${MODELPARAM_VALUE.WB_ERROR}
}

proc update_MODELPARAM_VALUE.SKIP_INTERNAL_TEST { MODELPARAM_VALUE.SKIP_INTERNAL_TEST PARAM_VALUE.SKIP_INTERNAL_TEST } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.SKIP_INTERNAL_TEST}] ${MODELPARAM_VALUE.SKIP_INTERNAL_TEST}
}

proc update_MODELPARAM_VALUE.ECC_ENABLE { MODELPARAM_VALUE.ECC_ENABLE PARAM_VALUE.ECC_ENABLE } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.ECC_ENABLE}] ${MODELPARAM_VALUE.ECC_ENABLE}
}

proc update_MODELPARAM_VALUE.DIC { MODELPARAM_VALUE.DIC PARAM_VALUE.DIC } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.DIC}] ${MODELPARAM_VALUE.DIC}
}

proc update_MODELPARAM_VALUE.RTT_NOM { MODELPARAM_VALUE.RTT_NOM PARAM_VALUE.RTT_NOM } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.RTT_NOM}] ${MODELPARAM_VALUE.RTT_NOM}
}

proc update_MODELPARAM_VALUE.DQ_BITS { MODELPARAM_VALUE.DQ_BITS PARAM_VALUE.DQ_BITS } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.DQ_BITS}] ${MODELPARAM_VALUE.DQ_BITS}
}

proc update_MODELPARAM_VALUE.serdes_ratio { MODELPARAM_VALUE.serdes_ratio PARAM_VALUE.serdes_ratio } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.serdes_ratio}] ${MODELPARAM_VALUE.serdes_ratio}
}

proc update_MODELPARAM_VALUE.wb_addr_bits { MODELPARAM_VALUE.wb_addr_bits PARAM_VALUE.wb_addr_bits } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.wb_addr_bits}] ${MODELPARAM_VALUE.wb_addr_bits}
}

proc update_MODELPARAM_VALUE.wb_data_bits { MODELPARAM_VALUE.wb_data_bits PARAM_VALUE.wb_data_bits } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.wb_data_bits}] ${MODELPARAM_VALUE.wb_data_bits}
}

proc update_MODELPARAM_VALUE.wb_sel_bits { MODELPARAM_VALUE.wb_sel_bits PARAM_VALUE.wb_sel_bits } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.wb_sel_bits}] ${MODELPARAM_VALUE.wb_sel_bits}
}

proc update_MODELPARAM_VALUE.wb2_sel_bits { MODELPARAM_VALUE.wb2_sel_bits PARAM_VALUE.wb2_sel_bits } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.wb2_sel_bits}] ${MODELPARAM_VALUE.wb2_sel_bits}
}

proc update_MODELPARAM_VALUE.cmd_len { MODELPARAM_VALUE.cmd_len PARAM_VALUE.cmd_len } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.cmd_len}] ${MODELPARAM_VALUE.cmd_len}
}

proc update_MODELPARAM_VALUE.AXI_LSBS { MODELPARAM_VALUE.AXI_LSBS PARAM_VALUE.AXI_LSBS } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.AXI_LSBS}] ${MODELPARAM_VALUE.AXI_LSBS}
}

proc update_MODELPARAM_VALUE.AXI_ADDR_WIDTH { MODELPARAM_VALUE.AXI_ADDR_WIDTH PARAM_VALUE.AXI_ADDR_WIDTH } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.AXI_ADDR_WIDTH}] ${MODELPARAM_VALUE.AXI_ADDR_WIDTH}
}

proc update_MODELPARAM_VALUE.AXI_DATA_WIDTH { MODELPARAM_VALUE.AXI_DATA_WIDTH PARAM_VALUE.AXI_DATA_WIDTH } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.AXI_DATA_WIDTH}] ${MODELPARAM_VALUE.AXI_DATA_WIDTH}
}

