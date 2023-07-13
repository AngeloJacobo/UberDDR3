#!/bin/bash

# Define the path to the .vh file
vh_file="../testbench/8192Mb_ddr3_parameters.vh"

# Function to modify BUS_DELAY and execute the simulation command
run_simulation() {
  local bus_delay=$1
  local flyby_delay_0=$2
  local flyby_delay_1=$3
  local flyby_delay_2=$4
  local flyby_delay_3=$5
  local flyby_delay_4=$6
  local flyby_delay_5=$7
  local flyby_delay_6=$8
  local flyby_delay_7=$9
  local log_file=${10}

  # Modify BUS_DELAY in the .vh file
  sed -i "s/parameter BUS_DELAY.*/parameter BUS_DELAY        =     $bus_delay; \/\/ delay in picoseconds/" "$vh_file"
  
  # Modify FLY_BY_DELAY in the .vh file
  sed -i "s/parameter FLY_BY_DELAY_LANE_0.*/parameter FLY_BY_DELAY_LANE_0        =     $flyby_delay_0; \/\/ delay in picoseconds/" "$vh_file"
  sed -i "s/parameter FLY_BY_DELAY_LANE_1.*/parameter FLY_BY_DELAY_LANE_1        =     $flyby_delay_1; \/\/ delay in picoseconds/" "$vh_file"
  sed -i "s/parameter FLY_BY_DELAY_LANE_2.*/parameter FLY_BY_DELAY_LANE_2        =     $flyby_delay_2; \/\/ delay in picoseconds/" "$vh_file"
  sed -i "s/parameter FLY_BY_DELAY_LANE_3.*/parameter FLY_BY_DELAY_LANE_3        =     $flyby_delay_3; \/\/ delay in picoseconds/" "$vh_file"
  sed -i "s/parameter FLY_BY_DELAY_LANE_4.*/parameter FLY_BY_DELAY_LANE_4        =     $flyby_delay_4; \/\/ delay in picoseconds/" "$vh_file"
  sed -i "s/parameter FLY_BY_DELAY_LANE_5.*/parameter FLY_BY_DELAY_LANE_5        =     $flyby_delay_5; \/\/ delay in picoseconds/" "$vh_file"
  sed -i "s/parameter FLY_BY_DELAY_LANE_6.*/parameter FLY_BY_DELAY_LANE_6        =     $flyby_delay_6; \/\/ delay in picoseconds/" "$vh_file"
  sed -i "s/parameter FLY_BY_DELAY_LANE_7.*/parameter FLY_BY_DELAY_LANE_7        =     $flyby_delay_7; \/\/ delay in picoseconds/" "$vh_file"

  # Print BUS_DELAY and log file name
  echo "BUS_DELAY: $bus_delay ps"
  echo "Log File: $log_file"

  # Execute the simulation command and redirect the output to the log file
  ./ddr3_dimm_micron_sim.sh >| "$log_file"

  # Print log contents starting from "------- SUMMARY -------"
  sed -n '/^------- SUMMARY -------/,$p' "$log_file"
  echo ""
  echo ""
}

# Run simulations with different BUS_DELAY values
run_simulation 0 0 0 0 0 0 0 0 0 "sim_logs/sim_busdelay0.log"
run_simulation 625 100 200 100 300 200 50 0 250 "sim_logs/sim_busdelay625.log"
run_simulation 1250 0 100 200 300 600 150 500 600 "sim_logs/sim_busdelay1250.log"
run_simulation 1875 500 1000 800 100 0 250 100 400 "sim_logs/sim_busdelay1875.log"
run_simulation 2500 1500 1500 1500 1500 0 0 100 200 "sim_logs/sim_busdelay2500.log"
run_simulation 5000 0 100 50 300 200 1000 1500 2200 "sim_logs/sim_busdelay5000.log"
run_simulation 10000 1000 2000 3000 2000 1000 1000 5000 0 "sim_logs/sim_busdelay10000.log"

