if [ "$1" == "" ]
then
    yosys -q -p "
    read_verilog -sv ./ddr3_phy.v;
    synth -top ddr3_phy"

elif [ "$1" == "iverilog" ] 
then
    iverilog ./ddr3_phy.v -o .out
    vvp .out

fi

# :set fileformat=unix
