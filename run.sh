if [ "$1" == "" ]
then
    yosys -q -p "
    read_verilog -sv ./rtl/ddr3_top.v;
    read_verilog -sv ./rtl/ddr3_controller.v;
    read_verilog -sv ./rtl/ddr3_phy.v;
    synth -top ddr3_top"

elif [ "$1" == "iverilog" ] 
then
    iverilog ./rtl/ddr3_top.v ./rtl/ddr3_controller.v ./rtl/ddr3_phy.v -o .out
    vvp .out
fi

# :set fileformat=unix

