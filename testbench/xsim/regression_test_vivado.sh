#!/bin/bash

#################################################################################################################

# Define the test configurations (CONTROLLER_CLK_PERIOD, DDR3_CLK_PERIOD, ODELAY_SUPPORTED, LANES_OPTION, ADD_BUS_DELAY, BIST_MODE)
TESTS=(
    # with bus delay
    "12_000 3_000 1 EIGHT_LANES 1 1" # DDR3-666
    "10_000 2_500 1 EIGHT_LANES 1 1" # DDR3-800
    "6_000  1_500 1 EIGHT_LANES 1 2" # DDR3-1333 write dm is weird (two happens at same time???)
    "5_000  1_250 1 EIGHT_LANES 1 2" # DDR3-1600
    # No bus delays
    "12_000 3_000 1 EIGHT_LANES 0 2"
    "10_000 2_500 1 EIGHT_LANES 0 2"
    "6_000  1_500 1 EIGHT_LANES 0 1"
    "5_000  1_250 1 EIGHT_LANES 0 1"
    # x16
    "12_000 3_000 1 TWO_LANES 1 1"
    "10_000 2_500 1 TWO_LANES 1 1"
    "6_000  1_500 1 TWO_LANES 1 2"
    "5_000  1_250 1 TWO_LANES 1 2"
    # no odelay
    "12_000 3_000 0 TWO_LANES 0 2"
    "10_000 2_500 0 TWO_LANES 0 2"
    "6_000  1_500 0 TWO_LANES 0 1"
    "5_000  1_250 0 TWO_LANES 0 1"
)

#################################################################################################################

# Define the files to modify
FILENAME="../ddr3_dimm_micron_sim.sv"
DEFINES_FILE="../sim_defines.vh"
PARAMETERS_FILE="../8192Mb_ddr3_parameters.vh"

# Check if the main file exists
if [[ ! -f "$FILENAME" ]]; then
    echo "Error: File '$FILENAME' does not exist."
    exit 1
fi

# Check if the defines file exists
if [[ ! -f "$DEFINES_FILE" ]]; then
    echo "Error: File '$DEFINES_FILE' does not exist."
    exit 1
fi

# Check if the parameters file exists
if [[ ! -f "$PARAMETERS_FILE" ]]; then
    echo "Error: File '$PARAMETERS_FILE' does not exist."
    exit 1
fi

#################################################################################################################

# Loop over each test configuration
index=1
for TEST in "${TESTS[@]}"; do
    # Parse the test configuration into individual variables
    read -r CONTROLLER_CLK_PERIOD DDR3_CLK_PERIOD ODELAY_SUPPORTED LANES_OPTION ADD_BUS_DELAY BIST_MODE <<< "$TEST"
    
    # Record the start time
    start_time=$(date +%s)
    start_time_am_pm=$(date +"%I:%M %p")  # Time in AM-PM format
    
    # Print the current test configuration with the start time
    echo "$index. Running test with CONTROLLER_CLK_PERIOD=$CONTROLLER_CLK_PERIOD, DDR3_CLK_PERIOD=$DDR3_CLK_PERIOD, ODELAY_SUPPORTED=$ODELAY_SUPPORTED, LANES_OPTION=$LANES_OPTION, ADD_BUS_DELAY=$ADD_BUS_DELAY, BIST_MODE=$BIST_MODE"
    echo "     Test started at: $start_time_am_pm"
    
    # Use sed to perform the replacements in the main file
    sed -i \
        -e "s/CONTROLLER_CLK_PERIOD = [0-9_]\+/CONTROLLER_CLK_PERIOD = $CONTROLLER_CLK_PERIOD/" \
        -e "s/DDR3_CLK_PERIOD = [0-9_]\+/DDR3_CLK_PERIOD = $DDR3_CLK_PERIOD/" \
        -e "s/ODELAY_SUPPORTED = [01]/ODELAY_SUPPORTED = $ODELAY_SUPPORTED/" \
        -e "s/BIST_MODE = [0-2]/BIST_MODE = $BIST_MODE/" \
        "$FILENAME"

    # Modify the sim_defines.vh file based on LANES_OPTION
    if [[ "$LANES_OPTION" == "TWO_LANES" ]]; then
        sed -i \
            -e "s|^//\(\`define TWO_LANES_x8\)|\1|" \
            -e "s|^\(\`define EIGHT_LANES_x8\)|//\1|" \
            "$DEFINES_FILE"
    elif [[ "$LANES_OPTION" == "EIGHT_LANES" ]]; then
        sed -i \
            -e "s|^//\(\`define EIGHT_LANES_x8\)|\1|" \
            -e "s|^\(\`define TWO_LANES_x8\)|//\1|" \
            "$DEFINES_FILE"
    else
        echo "Error: Invalid LANES_OPTION value. Choose either 'TWO_LANES' or 'EIGHT_LANES'."
        exit 1
    fi

    # Modify the parameters file based on ADD_BUS_DELAY
    if [[ "$ADD_BUS_DELAY" == "1" ]]; then
        sed -i \
            -e "s|BUS_DELAY        = [0-9]\+|BUS_DELAY        = 100|" \
            -e "s|FLY_BY_DELAY_LANE_0        = [0-9]\+|FLY_BY_DELAY_LANE_0        = 0|" \
            -e "s|FLY_BY_DELAY_LANE_1        = [0-9]\+|FLY_BY_DELAY_LANE_1        = 50|" \
            -e "s|FLY_BY_DELAY_LANE_2        = [0-9]\+|FLY_BY_DELAY_LANE_2        = 100|" \
            -e "s|FLY_BY_DELAY_LANE_3        = [0-9]\+|FLY_BY_DELAY_LANE_3        = 150|" \
            -e "s|FLY_BY_DELAY_LANE_4        = [0-9]\+|FLY_BY_DELAY_LANE_4        = 200|" \
            -e "s|FLY_BY_DELAY_LANE_5        = [0-9]\+|FLY_BY_DELAY_LANE_5        = 250|" \
            -e "s|FLY_BY_DELAY_LANE_6        = [0-9]\+|FLY_BY_DELAY_LANE_6        = 300|" \
            -e "s|FLY_BY_DELAY_LANE_7        = [0-9]\+|FLY_BY_DELAY_LANE_7        = 350|" \
            "$PARAMETERS_FILE"
    else
        sed -i \
            -e "s|BUS_DELAY        = [0-9]\+|BUS_DELAY        = 0|" \
            -e "s|FLY_BY_DELAY_LANE_0        = [0-9]\+|FLY_BY_DELAY_LANE_0        = 0|" \
            -e "s|FLY_BY_DELAY_LANE_1        = [0-9]\+|FLY_BY_DELAY_LANE_1        = 0|" \
            -e "s|FLY_BY_DELAY_LANE_2        = [0-9]\+|FLY_BY_DELAY_LANE_2        = 0|" \
            -e "s|FLY_BY_DELAY_LANE_3        = [0-9]\+|FLY_BY_DELAY_LANE_3        = 0|" \
            -e "s|FLY_BY_DELAY_LANE_4        = [0-9]\+|FLY_BY_DELAY_LANE_4        = 0|" \
            -e "s|FLY_BY_DELAY_LANE_5        = [0-9]\+|FLY_BY_DELAY_LANE_5        = 0|" \
            -e "s|FLY_BY_DELAY_LANE_6        = [0-9]\+|FLY_BY_DELAY_LANE_6        = 0|" \
            -e "s|FLY_BY_DELAY_LANE_7        = [0-9]\+|FLY_BY_DELAY_LANE_7        = 0|" \
            "$PARAMETERS_FILE"
    fi

    # Run the simulation script with the respective log file
    LOG_FILE="./test_${CONTROLLER_CLK_PERIOD}_ddr3_${DDR3_CLK_PERIOD}_odelay_${ODELAY_SUPPORTED}_lanes_${LANES_OPTION,,}_bus_delay_${ADD_BUS_DELAY}_bist_${BIST_MODE}.log"
    # ./ddr3_dimm_micron_sim.sh >> "$LOG_FILE"
    # add timeout if simulation takes too long
    timeout 3h ./ddr3_dimm_micron_sim.sh >> "$LOG_FILE" 2>&1
    EXIT_CODE=$?  # Capture exit code immediately
    if [ $EXIT_CODE -eq 124 ]; then
        echo "     Error: Simulation timed out after 1 hour!" | tee -a "$LOG_FILE"
    fi

    # Record the end time and calculate the duration in minutes
    end_time=$(date +%s)
    duration=$((end_time - start_time))
    minutes=$((duration / 60))
    seconds=$((duration % 60))

    # Report the results
    echo "     Test completed. Duration: ${minutes}m ${seconds}s. Results saved to '$LOG_FILE'."
    echo ""
    
    # Increment the index
    ((index++))
done

#################################################################################################################
