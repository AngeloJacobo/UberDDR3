if [ "$1" == "" ]
then
    yosys -q -p "
    read_verilog -sv ./rtl/ddr3_controller.v;
    synth -top ddr3_controller"

elif [ "$1" == "iverilog" ] 
then
    iverilog ./rtl/ddr3_controller.v -I ./rtl/ -o .out
    vvp .out

fi

# :set fileformat=unix

