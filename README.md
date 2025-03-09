
# Table of Contents  
 - [Brief Description](https://github.com/AngeloJacobo/DDR3_Controller#brief-description)
 - [Open IP Hub Blog Posts](https://github.com/AngeloJacobo/UberDDR3/edit/main/README.md#open-ip-hub-blog-posts)
 - [Getting Started](https://github.com/AngeloJacobo/DDR3_Controller#getting-started)
    - [Instantiate Design](https://github.com/AngeloJacobo/DDR3_Controller#heavy_check_mark-instantiate-design)
    - [Create Constraint File](https://github.com/AngeloJacobo/DDR3_Controller#heavy_check_mark-create-constraint-file)
    - [Edit Localparams](https://github.com/AngeloJacobo/DDR3_Controller#heavy_check_mark-edit-localparams)
 - [Lint and Formal Verification](https://github.com/AngeloJacobo/DDR3_Controller#lint-and-formal-verification)
 - [Simulation](https://github.com/AngeloJacobo/DDR3_Controller#simulation)
 - [Demo Projects](https://github.com/AngeloJacobo/UberDDR3/tree/main?tab=readme-ov-file#demo-projects)

   
# Brief Description
This DDR3 controller was originally designed to be used on the [10-Gigabit Ethernet Project](https://github.com/ZipCPU/eth10g) for an 8-lane x8 DDR3 module running at 800 MHz DDR, but this is now being designed to be a more general-purpose DDR3 memory controller with multiple supported FPGA boards. This is a 4:1 memory controller with configurable timing parameters and mode registers so it can be configured to any DDR3 memory device. The user-interface is the basic Wishbone. Optional features include:
- AXI4 User Interface ([blog post here](https://www.openiphub.com/post/uberddr3-new-feature-axi4-interface))
- SECDEC for error correction ([blog post here](https://www.openiphub.com/post/uberddr3-feature-update-error-correction-part-1-post-5))
- Self-Refresh ([blog post here](https://www.openiphub.com/post/uberddr3-self-refresh-reducing-power-consumption-in-idle-periods-post-9))
- Dual-rank Support ([blog post here](https://www.openiphub.com/post/unlocking-more-memory-dual-rank-dimm-support-in-uberddr3-post-10))
- Integratable with MicroBlaze ([blog post here](https://www.openiphub.com/post/uberddr3-microblaze-part-1-post-7))
- Built-in self test
  
This memory controller is optimized to maintain a high data throughput and continuous sequential burst operations. The controller handles the reset sequence, refresh sequence, mode register configuration, bank status tracking, timing delay tracking, command issuing, and the PHY's calibration. The PHY's calibration handles the bitslip training, read-DQ/DQS alignment via MPR (read calibration), write-DQ/DQS alignment via write leveling (write calibration), and also an optional comprehensive read/write test. 

The optional built-in self read/write tests made it easier to test the memory controller without needing an external CPU. These tests include a burst access, random access, and alternating read-write access tests. Only if no error is found on these tests will the calibration end and user can start accessing the wishbone interface. 

This design is [formally verified](https://github.com/AngeloJacobo/DDR3_Controller#lint-and-formal-verification) and [simulated using the Micron DDR3 model](https://github.com/AngeloJacobo/DDR3_Controller#simulation).

# Open IP Hub Blog Posts
Check out these blog posts for detailed explanations on new features of UberDDR3, how to use them, and project demos:  
- [UberDDR3: An Opensource DDR3 Controller - Post #1](https://www.openiphub.com/post/uberddr3-an-opensource-ddr3-controller-post-1)  
- [Getting Started with UberDDR3 (Part 1) - Post #2](https://www.openiphub.com/post/getting-started-with-uberddr3-part-1-post-2)  
- [Getting Started with UberDDR3 (Part 2) - Post #3](https://www.openiphub.com/post/getting-started-with-uberddr3-part-2-post-3)  
- [UberDDR3 Update: AXI4 Interface - Post #4](https://www.openiphub.com/post/uberddr3-new-feature-axi4-interface)  
- [UberDDR3 Update: Error Correction (Part 1) - Post #5](https://www.openiphub.com/post/uberddr3-feature-update-error-correction-part-1-post-5)  
- [UberDDR3 Feature Update: Error Correction (Part 2) - Post #6](https://www.openiphub.com/post/uberddr3-feature-update-error-correction-part-2-post-6)  
- [UberDDR3 + MicroBlaze (Part 1) - Post #7](https://www.openiphub.com/post/uberddr3-microblaze-part-1-post-7)  
- [UberDDR3 + MicroBlaze (Part 2) - Post #8](https://www.openiphub.com/post/uberddr3-microblaze-part-2-post-8)  
- [UberDDR3 Self-Refresh: Reducing Power Consumption in Idle Periods - Post #9](https://www.openiphub.com/post/uberddr3-self-refresh-reducing-power-consumption-in-idle-periods-post-9)  
- [Unlocking More Memory: Dual-Rank DIMM Support in UberDDR3 - Post #10](https://www.openiphub.com/post/unlocking-more-memory-dual-rank-dimm-support-in-uberddr3-post-10)   

# Getting Started
The recommended way to instantiate this IP is to use the top module [`rtl/ddr3_top.v`](https://github.com/AngeloJacobo/DDR3_Controller/blob/main/rtl/ddr3_top.v), a template for instantiation is also included in that file. Steps to include this DDR3 memory controller IP is to instantiate design, create the constraint file, then edit the localparams. 

## :heavy_check_mark: Instantiate Design
The first thing to edit are the **top-level parameters**:

| Parameter | Function |
| :---:        |     :---       | 
| CONTROLLER_CLK_PERIOD   | clock period of the controller interface in picoseconds. Tested values range from `12_000` ps (83.33 MHz) to `10_000` ps (100 MHz).     | 
| DDR3_CLK_PERIOD     | clock period of the DDR3 RAM device in picoseconds which must be 1/4 of the `CONTROLLER_CLK_PERIOD`. Tested values range from `3_000` ps (333.33 MHz) to `2_500` ps (400 MHz).     |
| ROW_BITS     | width of row address. Use chapter _2.11 DDR3 SDRAM Addressing_ from [JEDEC DDR3 doc (page 15)](https://www.jedec.org/sites/default/files/docs/JESD79-3F.pdf) as a guide. Possible values range from `12` to `16`.     |
| COL_BITS     | width of column address. Use chapter _2.11 DDR3 SDRAM Addressing_ from [JEDEC DDR3 doc (page 15)](https://www.jedec.org/sites/default/files/docs/JESD79-3F.pdf) as a guide. Possible values range from `10` to `12`.     |
| BA_BITS     | width of bank address. Use chapter _2.11 DDR3 SDRAM Addressing_ from [JEDEC DDR3 doc (page 15)](https://www.jedec.org/sites/default/files/docs/JESD79-3F.pdf) as a guide. Usual value is `3`.      
| BYTE_LANES  | number of bytes based on width of DQ. <sup>[[1]](https://github.com/AngeloJacobo/DDR3_Controller#note) </sup> |
| AUX_WIDTH | width of auxiliary line. Value must be >= 4.  <sup>[[2]](https://github.com/AngeloJacobo/DDR3_Controller#note) </sup>  |
| WB2_ADDR_BITS | width of 2nd wishbone address bus for debugging (only relevant if SECOND_WISHBONE = 1).   |
| WB2_DATA_BITS  | width of 2nd wishbone data bus for debugging (only relevant if SECOND_WISHBONE = 1).  |
| MICRON_SIM  | set to 1 if used in Micron DDR3 model to shorten power-on sequence, otherwise 0. |
| ODELAY_SUPPORTED | set to 1 if ODELAYE2 primitive is supported by the FPGA, otherwise 0.  <sup>[[3]](https://github.com/AngeloJacobo/DDR3_Controller#note) </sup>  |
| SECOND_WISHBONE | set to 1 if 2nd wishbone for debugging is needed , otherwise 0.|
| WB_ERROR | set to 1 to support Wishbone error (asserts at ECC double bit error assuming ECCE_ENABLE != 0) |
| SKIP_INTERNAL_TEST | set to 1 to skip built-in self test which usually takes > 2 seconds|
| ECC_ENABLE |  set to 0 to disable ECC OR: 1 = Side-band ECC per burst, 2 = Side-band ECC per 8 bursts , 3 = Inline ECC (more about [ECC on this blog post](https://www.openiphub.com/post/uberddr3-feature-update-error-correction-part-1-post-5))|
| DIC | Output Driver Impedance Control (2'b00 = RZQ/6, 2'b01 = RZQ/7, RZQ = 240ohms) (only change this when you know what you are doing) |
| RTT_NOM | RTT Nominal (3'b000 = disabled, 3'b001 = RZQ/4, 3'b010 = RZQ/2 , 3'b011 = RZQ/6, RZQ = 240ohms)  (only change when you know what you are doing) |
| SELF_REFRESH | 0 = use i_user_self_refresh input, 1 = Self-refresh mode is enabled after 64 controller clock cycles of no requests, 2 = 128 cycles, 3 = 256 cycles (more on [self-refresh on this blog post](https://www.openiphub.com/post/uberddr3-self-refresh-reducing-power-consumption-in-idle-periods-post-9))|
***

After the parameters, connect the ports of the top module to your design. Below are the **ports for clocks and reset**:
| Ports | Function |
| :---:        |     :---       | 
| i_controller_clk   | clock of the controller interface with period of `CONTROLLER_CLK_PERIOD` | 
| i_ddr3_clk   | clock of the DDR3 interface with period of `DDR3_CLK_PERIOD` | 
| i_ref_clk   | reference clock for IDELAYCTRL primitive with frequency of 200 MHz | 
| i_ddr3_clk_90   | clock required only if ODELAY_SUPPORTED = 0, otherwise can be left unconnected. Has a period of `DDR3_CLK_PERIOD` with 90° phase shift. | 
| i_rst_n   | Active-low synchronous reset for the entire DDR3 controller and PHY | 

It is recommended to generate all these clocks from a single PLL or clock-generator.

***

Next are the **main wishbone ports**:

| Ports | Function |
| :---:        |     :---       | 
| i_wb_cyc   | Indicates if a bus cycle is active. A high value (1) signifies normal operation, while a low value (0) signals the cancellation of all ongoing transactions. | 
| i_wb_stb   |  Strobe or transfer request signal. It's asserted (set to 1) to request a data transfer. | 
| i_wb_we   | Write-enable signal. A high value (1) indicates a write operation, and a low value (0) indicates a read operation. | 
| i_wb_addr  | Address bus. Used to specify the address for the current read or write operation. Formatted as {row, bank, column}. | 
| i_wb_data   | Data bus for write operations. In a 4:1 controller, the data width is 8 times the DDR3 pins `8`x`DQ_BITS`x`LANES`. | 
| i_wb_sel   | Byte select for write operations. Indicates which bytes of the data bus are to be overwritten for the write operation. | 
| o_wb_stall   | Indicates if the controller is busy (1)and cannot accept any new requests. | 
| o_wb_ack   |  Acknowledgement signal. Indicates that a read or write request has been completed. | 
| o_wb_data   | Data bus for read operations. Similar to `i_wb_data`, the data width for a 4:1 controller is 8 times the DDR3 pins `8`x`DQ_BITS`x`LANES`. |

***

Below are the **auxiliary ports** associated with the main wishbone. This is not required for normal operation, but is intended for AXI-interface compatibility *which is not yet available*:  
| Ports | Function |
| :---:        |     :---       | 
| i_aux   | Request ID line with width of `AUX_WIDTH`. The Request ID is retrieved simultaneously with the strobe request. | 
| o_aux   | Request ID line with width of `AUX_WIDTH`. The Request ID is sent back concurrently with the acknowledgement signal.  | 


***

After main wishbone port are the **second-wishbone ports**. This interface is only for debugging-purposes and would normally not be needed thus can be left unconnected by setting `SECOND_WISHBONE` = 0. The ports for the second-wishbone is very much the same as the main wishbone.

Next are the **DDR3 I/O ports**, these will be connected directly to the top-level pins of your design thus port-names must match what is indicated on your constraint file. You do not need to understand what each DDR3 I/O ports does but if you're curious, details on each DDR3 I/O pins are described on _2.10 Pinout Description_ from [JEDEC DDR3 doc (page 13)](https://www.jedec.org/sites/default/files/docs/JESD79-3F.pdf).

Finally are the **debug ports**, these are connected to relevant registers containing information on current state of the controller. Trace each `o_debug_*` inside `ddr3_controller.v` to edit the registers to be monitored.

## :heavy_check_mark: Create Constraint File
* One example of constraint file is from the [Kintex-7 Ethernet Switch Project](https://github.com/AngeloJacobo/DDR3_Controller/blob/main/example_demo/klusterlab/kluster.xdc#L227-L389)  <sup>[[4]](https://github.com/AngeloJacobo/DDR3_Controller#note) </sup>, highlighted are all the DDR3 pins. This constraint file assumes a dual-rank DDR3 RAM (thus 2 pairs of `o_ddr3_clk`, `o_ddr3_cke`, `o_ddr3_s_n`, and `o_ddr3_odt`)  with 8 lanes of x8 DDR3 (thus 8 `o_ddr3_dm`, 8 `io_ddr3_dqs`, and 64 `io_ddr3_dq`). The constraint file also has [set_property](https://github.com/AngeloJacobo/DDR3_Controller/blob/main/example_demo/klusterlab/kluster.xdc#L453-L457) required for proper operation. The property `INTERNAL_VREF` must be set to half of the bank voltage (1.5V thus set to `0.75`). The property `BITSTREAM.STARTUP.MATCH_CYCLE` ([page 240 of UG628: Command Line Guide](https://docs.xilinx.com/v/u/en-US/devref)) is verified to work properly when value is set to `6`. Kintex-7 has HP bank where the DDR3 is connected thus allow the use of DCI (Digitally-Controlled Impedance) for impedance matching by using `SSTL15_T_DCI` type of `IOSTANDARD`.

* Another example of constraint file is for the [Arty-S7 project]( https://github.com/AngeloJacobo/UberDDR3/blob/main/example_demo/arty_s7/Arty-S7-50-Master.xdc#L24-L244), highlighted are the DDR3 pins. The Arty-S7 has x16 DDR3 and it works like two x8 (thus 2 `ddr3_dm`, 2 `ddr3_dqs`, and 16 `io_ddr3_dq`) <sup>[[1]](https://github.com/AngeloJacobo/DDR3_Controller#note) </sup>. Arty-S7 only has HR bank where the DDR3 is connected, this restricts the design to use on-chip split-termination [(UG471 7-Series Select Guide page 33)](https://docs.xilinx.com/v/u/en-US/ug471_7Series_SelectIO) for impedance matching instead of DCI used in HP banks. `IN_TERM UNTUNED_SPLIT_50` signifies that the input termination is set to an untuned split termination of 50 ohms. The constraint file was  easily created by retrieving the pin constraints generated by the Vivado Memory Interface Generator (MIG) together with the [`.prj` file](https://github.com/Digilent/vivado-boards/blob/master/new/board_files/arty-s7-50/B.0/mig.prj#L47-L96) provided by Digilent for Arty-S7. The generated `.xdc` file by the MIG can be located at `[vivado_proj].gen/sources_1/ip/mig_7series_0/mig_7series_0/user_design/constraints/mig_7series_0.xdc`

## :heavy_check_mark: Edit Localparams
The verilog file [`rtl/ddr3_controller`](https://github.com/AngeloJacobo/DDR3_Controller/blob/main/rtl/ddr3_controller.v) contains the timing parameters that needs to be configured by the user to align with the DDR3 device. User should base the timing values on _Chapter 13 Electrical Characteristics and AC Timing_ from [JEDEC DDR3 doc (page 169)](https://www.jedec.org/sites/default/files/docs/JESD79-3F.pdf). _The default values on the verilog file should generally work for DDR3-800_. 

### Note:  
[1]: For x16 DDR3 like in Arty S7, use `BYTE_LANES` of 2. If the memory configuration is a SO-DIMM with 8 DDR3 RAM modules, each being x8 to form a total of 64 bits of data, then BYTE_LANES would be 8.  
[2]: The auxiliary line is intended for AXI-interface compatibility but is also utilized in the reset sequence, which is the origin of the minimum required width of 4.  
[3]: ODELAYE2 is supported if DDR3 device is connected to an HP (High-Powered) bank of FPGA. HR (High-Rank) bank does not support ODELAYE2 as based on [UG471 7-Series Select Guide (page 134)](https://docs.xilinx.com/v/u/en-US/ug471_7Series_SelectIO).   
[4]: This is the open-sourced [10Gb Ethernet Project](https://github.com/ZipCPU/eth10g).


***

#  Lint and Formal Verification
The easiest way to compile, lint, and formally verify the design is to run [`./run_compile.sh`](https://github.com/AngeloJacobo/DDR3_Controller/blob/main/run_compile.sh) on the top-level directory. This will first run [Verilator](https://verilator.org/guide/latest/install.html) lint.

Next is compilation with [Yosys](https://github.com/YosysHQ/yosys), this will show warnings: 
> Warning: Replacing memory ... with list of registers.

Disregards this kind of warning as it just converts small memory elements in the design into a series of register elements.

After Yosys compilation is [Icarus Verilog](https://github.com/steveicarus/iverilog) compilation, this should not show any warning or errors but will display the `Test Functions` to verify that the verilog-functions return the correct values, and `Controller Parameters` to verify the top-level parameters are set properly. Delay values for some timing parameters are also shown.

Last is the [Symbiyosys Formal Verification](https://symbiyosys.readthedocs.io/en/latest/install.html), this will run the [single and multiple configuration sby](https://github.com/AngeloJacobo/UberDDR3/tree/main/formal) for formal verification. A summary is shown at the end where all tasks passed:  

![image](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/de554a92-880c-4513-83ba-a096da682f3b)


# Simulation

For simulation, the DDR3 SDRAM Verilog [Model from Micron](https://www.micron.com/search-results?searchRequest=DDR3+SDRAM+Verilog+Model&SelectedValues=%2Fsim-model--%2Fsim-model%2Fbdsl--%2Fsim-model%2Fbfm--%2Fsim-model%2Fcadence-dml--%2Fsim-model%2Fhspice--%2Fsim-model%2Fhyperlynx--%2Fsim-model%2Fibis--%2Fsim-model%2Fibis-ami--%2Fsim-model%2Fmentor-icx--%2Fsim-model%2Fs-parameter--%2Fsim-model%2Fspice--%2Fsim-model%2Fsisoft--%2Fsim-model%2Fsystem-c--%2Fsim-model%2Fsystem-verilog--%2Fsim-model%2Fthermal--%2Fsim-model%2Fverilog#accordion-db73c0b4db-item-4671aec5a3) is used. Import all simulation files under [./testbench](https://github.com/AngeloJacobo/DDR3_Controller/tree/main/testbench) to Vivado. [`ddr3_dimm_micron_sim.sv`](https://github.com/AngeloJacobo/DDR3_Controller/blob/main/testbench/ddr3_dimm_micron_sim.sv) is the top-level module which instantiates both the DDR3 memory controller and the Micron DDR3 model. This module issues read and write requests to the controller via the wishbone bus, then the returned data from read requests are verified if it matches the data written. Both sequential and random accesses are tested.

Currently, there are 2 general options for running the simulation and is defined by a `define` directive on the `ddr3_dimm_micron_sim.sv` file: `TWO_LANES_x8` and `EIGHT_LANES_x8`. `TWO_LANES_x8` simulates an Arty-S7 FPGA board which has an x16 DDR3, meanwhile `EIGHT_LANES_x8` simulates 8-lanes of x8 DDR3 module. **Make sure to change the organization via a `define` directive under [ddr3.sv](https://github.com/AngeloJacobo/DDR3_Controller/blob/main/testbench/ddr3.sv)** (`TWO_LANES_x8` must use `define x8` while `EIGHT_LANES_x8` must use `define x16`).


After configuring, run simulation. The `ddr3_dimm_micron_sim_behav.wcfg` contains the waveform. Shown below are the clocks:    
![image](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/f11afd00-ea17-4669-bebb-9f22e8ae6f6d)  


As shown below, `command_used` shows the command issued at a specific time. During reads the `dqs` should toggle and `dq` should have a valid value, else they must be in high-impedance `Z`. Precharge and activate also happens between reads when row addresses are different. 
![image](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/a289066f-2a5c-4d08-9660-a76cf537383a)


A part of internal test is to do alternate write then read consecutively as shown below. The data written must match the data read. `dqs` should also toggle along with the data written and read.  
![image](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/817124fa-43d0-4e9f-94c4-2889614d7c87)


There are counters for the number of correct and wrong read data during the internal read/write test: `correct_read_data` and `wrong_read_data`. As shown below, the `wrong_read_data` must remain zero while `correct_read_data` must increment until it reaches the maximum (3499 on this example).  
![image](https://github.com/AngeloJacobo/DDR3_Controller/assets/87559347/06d7b4c0-cd40-4fd1-9bc3-6329237e46e3)

The simulation also reports the status of the simulation. For example, the report below:
> [10000 ps]  RD @ (0,   840) -> [10000 ps]  RD @ (0,   848) -> [10000 ps]  RD @ (0,   856) -> [10000 ps]  RD @ (0,   864) -> [10000 ps]  RD @ (0,   872) -> 

The format is [`time_delay`] `command` @ (`bank`, `address`), so `[10000 ps]  RD @ (0,   840)` means 10000 ps delay before a read command with bank 0 and address 840. Notice how each read command has a delay of 10000 ps or 10 ns from each other, since this has a controller clock of 100 MHz (10 ns clock period) this shows that there are no interruptions between sequential read commands resulting in a very high throughput. 

A short report is also shown in each test section:  
> DONE TEST 1: LAST ROW  
Number of Operations: 2304  
Time Started: 363390 ns  
Time Done: 387980 ns  
Average Rate: 10 ns/request  


This report is after a burst write then burst read. This report means there were 2304 write and read operation, and the average time per request is 10 ns (1 controller clock period of 100 MHz). The average rate is optimal since this is a burst write and read. But for random writes and reads:  
> DONE TEST 2: RANDOM  
Number of Operations: 2304  
Time Started: 387980 ns  
Time Done: 497660 ns  
Average Rate: 47 ns/request  


Notice how the average rate increased to 47 ns/request. Random access requires occasional precharge and activate which takes time and thus prolong the time for every read or write access. At the very end of the report shows a summary:

> TEST CALIBRATION  
[-]: write_test_address_counter = 5000  
[-]: read_test_address_counter = 2000  
[-]: correct_read_data = 3499  
[-]: wrong_read_data = 0  

> ------- SUMMARY -------  
Number of Writes = 4608  
Number of Reads = 4608  
Number of Success = 4604  
Number of Fails = 4  
Number of Injected Errors = 4  

The summary under `TEST CALIBRATION` are the results from the **internal** read/write test as part of the internal calibration. These are the same counters on the waveform shown before where the `wrong_read_data` should be zero. Under `SUMMARY` is the report from the **external** read/write test where the top-level simulation file `ddr3_dimm_micron_sim.sv` sends read/write request to the DDR3 controller via the wishbone bus. Notice that the number of fails (4) matches the number of injected errors (4) which is only proper.  

# Demo Projects
- The [Arty-S7 demo project](./example_demo/arty_s7) is a basic project for testing the DDR3 controller. The gist is that the 4 LEDS should light-up which means reset sequence is done and all internal read/write test passed during calibration. This project also uses a UART line, sending small letters via UART will write those corresponding small letters to memory, meanwhile sending capital letters will read those small letters back from memory.
   - To run this project on your Arty-S7 board, import all verilog files and xdc file under `example_demo/arty_s7/` and `rtl/`. Run synthesis-to-bitstream generation then upload the bitfile. After around 2 seconds, the 4 LEDS should light up then you can start interacting with the UART line. BTN0 button is for reset.
   - Or just upload the [bitfile already given in the repo](./example_demo/arty_s7).

- The [Nexys Video demo project](./example_demo/nexys_video)  utilizes the DDR3 chip on the Digilent Nexys Video board with xc7a200t. Only one lane is used for simplicity. Supports OpenXC7 toolchain. Makefiles have been included for quick start, just run the following command in the root directory of repo:

  - Vivado compilation: `source /opt/Xilinx/Vivado/2019.1/settings64.sh` then `make -C example_demo/nexys_video -f Makefile.vivado`
  - OpenXC7 compilation (using toolchain in Docker): `docker run --rm -v .:/mnt -v /chipdb:/chipdb regymm/openxc7 make -C /mnt/nexys_video -f Makefile.openxc7`

  The bitstream will be compiled as `nexys_video/build/top.bit`. 

  - Board test: after programming bitstream, the 8 LEDs will show some pattern, then become all lit up after calibration. When pressing BTND(D22), LD7/LD6 will show a blinky, and LD5-LD0 will show 101110 after successful calibration. BTNC(B22) resets the controller, and calibration will be redone. 9600 baud UART will be the same as the Arty-S7 case: type small `abcd` to write to memory, and type capital `ABCD` to read back. For example, type `abcd` then `ABCDEFGH` will show `abcd����` (because EFGH memory locations are not written yet). 
- The [QMTech Wukong demo project](./example_demo/qmtech_wukong) is just the same as the arty-s7 demo mentioned above.
   - To run this project on your [QMTech Wukong board](https://github.com/ChinaQMTECH/QM_XC7A100T_WUKONG_BOARD/tree/master/V3), import all verilog files and xdc file under `example_demo/qmtech_wukong/` and `rtl/`. Run synthesis-to-bitstream generation then upload the bitfile. After around 2 seconds, the 2 LEDS should light up then you can start interacting with the UART line. SW2 button is for reset.
   - Or just upload the [bitfile already given in the repo](./example_demo/qmtech_wukong).
- The [10Gb Ethernet Switch](https://github.com/ZipCPU/eth10g) project utilizes this DDR3 controller for accessing a single-rank DDR3 module (8 lanes of x8 DDR3) at DDR3-800 (100 MHz controller and 400 MHz PHY).

# Other Open-Sourced DDR3 Controllers
(soon...)

# Developer Documentation 
There is no developer documentation yet. But may I include here the [notes I compiled](https://github.com/AngeloJacobo/DDR3-Notes) when I did an intensive study on DDR3 before I started this project.

# Acknowledgement
This project is funded through [NGI0 Entrust](https://nlnet.nl/entrust), a fund established by [NLnet](https://nlnet.nl) with financial support from the European Commission's [Next Generation Internet](https://ngi.eu) program. Learn more at the [NLnet project page](https://nlnet.nl/project/UberDDR3).

[<img src="https://nlnet.nl/logo/banner.png" alt="NLnet foundation logo" width="20%" />](https://nlnet.nl)
[<img src="https://nlnet.nl/image/logos/NGI0_tag.svg" alt="NGI Zero Logo" width="20%" />](https://nlnet.nl/entrust)
