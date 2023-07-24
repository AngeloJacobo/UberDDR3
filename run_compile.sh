# run verilator lint
echo -e "\e[32mRun Verilator Lint:\e[0m"
verilator --lint-only ddr3_top.v -Irtl/
    

# run yosys compile
echo ""
echo ""
echo -e "\e[32mRun Yosys Compile:\e[0m"
yosys -q -p "
    read_verilog -sv ./rtl/ddr3_controller.v;
    synth -top ddr3_controller"

# run iverilog compile
echo ""
echo ""
echo -e "\e[32mRun IVerilog Compile:\e[0m"
iverilog rtl/ddr3_controller.v -o out
vvp out
rm out
echo

# run symbiyosys 
echo ""
echo -e "\e[32mRun Symbiyosys Formal Verification:\e[0m"
echo "---------------------------------------"
sby -f ddr3_controller.sby

