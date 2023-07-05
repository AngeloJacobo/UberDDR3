#!/bin/bash

# Define the path to the .vh file
vh_file="../testbench/8192Mb_ddr3_parameters.vh"

# Function to modify BUS_DELAY and execute the simulation command
run_simulation() {
  local bus_delay=$1
  local flyby_delay=$2
  local log_file=$3

  # Modify BUS_DELAY in the .vh file
  sed -i "s/parameter BUS_DELAY.*/parameter BUS_DELAY        =     $bus_delay; \/\/ delay in picoseconds/" "$vh_file"
  
  # Modify FLY_BY_DELAY in the .vh file
  sed -i "s/parameter FLY_BY_DELAY.*/parameter FLY_BY_DELAY        =     $flyby_delay; \/\/ delay in picoseconds/" "$vh_file"

  # Print BUS_DELAY and log file name
  echo "BUS_DELAY: $bus_delay ps"
  echo "FLY_BY_DELAY: $flyby_delay ps"
  echo "Log File: $log_file"

  # Execute the simulation command and redirect the output to the log file
  ./ddr3_dimm_micron_sim.sh >| "$log_file"

  # Print log contents starting from "------- SUMMARY -------"
  sed -n '/^------- SUMMARY -------/,$p' "$log_file"
  echo ""
  echo ""
}

# Run simulations with different BUS_DELAY values
run_simulation 0 0 "sim_busdelay0_flybydelay0.log"
run_simulation 625 0 "sim_busdelay625_flybydelay0.log"
run_simulation 1250 600 "sim_busdelay1250_flybydelay600.log"
run_simulation 1875 1000 "sim_busdelay1875_flybydelay1000.log"
run_simulation 2500 1500 "sim_busdelay2500_flybydelay1500.log"
run_simulation 5000 2200 "sim_busdelay5000_flybydelay2200.log"
run_simulation 10000 3000 "sim_busdelay10000_flybydelay3000.log"

