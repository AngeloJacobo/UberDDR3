`default_nettype none
`timescale 1ns / 1ps

module spd_reader (
    // clock and reset
    input wire i_clk,
    input wire i_rst_n,
    // i2c interface
    inout wire i2c_scl,
    inout wire i2c_sda,
    // state of spd reader
    (* mark_debug = "true" *) output reg find_i2c_address_done,
    (* mark_debug = "true" *) output reg read_spd_done,
    // uart interface
    output wire uart_tx
);

    // byte 2: DRAM Device Type (DDR3 SDRAM = 0x0B)
    // byte 3: Module Type (SO-DIMM = 0x03)
    // byte 4: SDRAM Density and Banks ([6:4] = BA_BITS, [3:0] = SDRAM capacity)
    // byte 5: SDRAM Addressing ([5:3] = Row Addr , [2:0] = Column Addr)
    // byte 7: Module Organization ([5:3] = Ranks , Device Width = [2:0])
    // byte 8: Module Memory Bus Width ([2:0] = Bus Width)
    // byte 10,11: Medium Timebase (MTB) Dividend (0x01), Medium Timebase (MTB) Divisor (0x08 = 0.125ns , 0x10 = 0.0625ns) (tXX = tXX(MTB) * MTB)
    // byte 12: SDRAM Minimum Cycle Time tCK

    localparam I2C_ADDRESS = 7'h30;
    localparam IDLE = 0,
                READ_ADDRESS = 1, 
                READ_BYTE = 1,
                SEND_BYTE = 1,
                WAIT_ACK = 2,
                WAIT_SEND = 2,
                DONE_FIND_ADDRESS = 3,
                UART_SEND = 3,
                WAIT_UART_DONE = 4;
                
    (* mark_debug = "true" *) reg[1:0] state_find_i2c_address;
    (* mark_debug = "true" *) reg[6:0] i2c_address;

    // i2c master interface
    reg enable;
    reg read_write;
    reg[7:0] register_address;
    reg[6:0] device_address;
    wire[7:0] miso_data;
    wire busy;
    wire slave_nack;
    (* mark_debug = "true" *) reg nack_unexpected_err;
    (* mark_debug = "true" *) reg[2:0] state_read_spd;
    (* mark_debug = "true" *) reg[5:0] byte_address; // read until byte 63
    (* mark_debug = "true" *) reg[7:0] byte_data[63:0];
    // uart interface
    wire uart_tx_busy;
    reg uart_tx_en;
    reg[7:0] uart_tx_data;
    reg[30*8-1:0] uart_text; // max of 30 chars
    reg[2:0] state_uart_send;
    reg uart_start_send;
    reg[9:0] uart_text_length,uart_text_length_index;
    reg uart_send_done;
    reg skip_byte;
    reg[7:0] mtb_dividend, mtb_divisor;
    wire[7:0] mtb;
    reg[3:0] tras_high;

    // initialize in case fpga starts with no reset
    initial begin
        state_find_i2c_address = IDLE;
        find_i2c_address_done = 0;
        enable = 1'b0;
        read_write = 1'b0;
        register_address = 8'd0;
        i2c_address = 7'd0;
        read_spd_done = 1'b0;
        nack_unexpected_err = 1'b0;
        state_read_spd = IDLE;
        byte_address = 6'h00;
        state_uart_send = IDLE;
        uart_text_length_index = 0;
        uart_tx_en = 0;
        uart_send_done = 0;
        uart_tx_data = 0;
        uart_start_send = 0;
        uart_text_length = 0;
        uart_text = {(30*8){1'b0}};
        skip_byte = 0;
        mtb_dividend = 0;
        mtb_divisor = 0;
        tras_high = 0;
    end

    // FSM for I2C
    always @(posedge i_clk, negedge i_rst_n) begin
        if(!i_rst_n) begin
            state_find_i2c_address <= IDLE;
            find_i2c_address_done <= 0;
            enable <= 1'b0;
            read_write <= 1'b0;
            register_address <= 8'd0;
            i2c_address <= 7'd0;
            read_spd_done <= 1'b0;
            nack_unexpected_err <= 1'b0;
            state_read_spd <= IDLE;
            byte_address <= 6'h00;
            uart_start_send <= 0;
            uart_text_length = 0;
            uart_text = {(30*8){1'b0}};
            skip_byte <= 1'b0;
            mtb_dividend <= 0;
            mtb_divisor <= 0;
            tras_high <= 0;
        end
        else begin
            // Find I2C Address of SPD
            case(state_find_i2c_address)
                IDLE: if(!find_i2c_address_done) begin
                    state_find_i2c_address <= READ_ADDRESS;
                    i2c_address <= 7'h01; // start brute force find i2c address from 1 (0 might be general call)
                end
                READ_ADDRESS: if(!busy) begin
                    enable <= 1'b1;
                    read_write <= 1'b1; // read i2c
                    register_address <= 8'h00; // just always read byte 0
                    device_address <= i2c_address;
                    state_find_i2c_address <= WAIT_ACK;
                end
                WAIT_ACK: if(!busy && !enable) begin
                    if(slave_nack) begin // if wrong i2c_address
                        i2c_address <= i2c_address + 1; // increment i2c address
                        state_find_i2c_address <= READ_ADDRESS;
                    end
                    else begin // I2C acks so i2c_address is correct!
                        uart_start_send <= 1'b1;
                        uart_text_length <= 18; 
                        uart_text[30*8-1:8*3] <= "I2C Address: 0x";
                        uart_text[8*3-1:8*2] <= hex_to_ascii(i2c_address[6:4]);
                        uart_text[8*2-1:8*1] <= hex_to_ascii(i2c_address[3:0]);
                        uart_text[7:0] <= 8'h0a;
                        state_find_i2c_address <= DONE_FIND_ADDRESS;
                    end
                    end
                    else begin
                        enable <= 1'b0;
                    end
                DONE_FIND_ADDRESS: if(uart_send_done) begin
                    state_find_i2c_address <= IDLE;
                    find_i2c_address_done <= 1'b1;
                end
                else begin
                    uart_start_send <= 1'b0;
                end
                default: state_find_i2c_address <= IDLE;
            endcase

            // read bytes from SPD
            case(state_read_spd) 
                IDLE: if(find_i2c_address_done && !read_spd_done && !nack_unexpected_err) begin // start read SPD only once i2c address is found
                    state_read_spd <= READ_BYTE;
                    byte_address <= 6'h00; // start read from byte 0
                    uart_start_send <= 1'b0;
                    skip_byte <= 1'b0;
                end
                READ_BYTE: if(!busy) begin // if not busy, send i2c read transaction
                    enable <= 1'b1;
                    read_write <= 1'b1; // read i2c
                    register_address <= {2'b00,byte_address};
                    device_address <= i2c_address;
                    state_read_spd <= WAIT_ACK;
                end
                WAIT_ACK: if(!busy && !enable) begin
                    if(slave_nack) begin // if i2c_address NACKS, then something is wrong, raise nack_unexpected_err
                        nack_unexpected_err <= 1'b1;
                        state_read_spd <= IDLE;
                    end
                    else begin // I2C acks so send via UART the received data
                        state_read_spd <= UART_SEND;
                        byte_data[byte_address] <= miso_data;
                    end
                    end
                    else begin
                        enable <= 1'b0;
                    end
                UART_SEND: begin
                    case(byte_address) 
                        0: begin
                            uart_start_send <= 1'b1;
                            uart_text_length <= 29; 
                            uart_text[30*8-1:8*29] <= 8'h0a;
                            uart_text[29*8-1:8] <= "------ START SPD READ ------";
                            uart_text[7:0] <= 8'h0a;
                        end
                        1: begin
                            uart_start_send <= 1'b1;
                            uart_text_length <= 18; 
                            uart_text[30*8-1:8*4] <= "SPD Revision: ";
                            uart_text[8*4-1:8*3] <= hex_to_ascii(miso_data[7:4]);
                            uart_text[8*3-1:8*2] <= ".";
                            uart_text[8*2-1:8*1] <= hex_to_ascii(miso_data[3:0]);
                            uart_text[7:0] <= 8'h0a;
                        end
                        2: begin
                            if(miso_data == 8'h0b) begin
                                uart_start_send <= 1'b1;
                                uart_text_length <= 22; 
                                uart_text[30*8-1:8] <= "DRAM Type: DDR3 SDRAM";
                                uart_text[7:0] <= 8'h0a;
                            end
                            else begin
                                uart_start_send <= 1'b1;
                                uart_text_length <= 21; 
                                uart_text[30*8-1:8] <= "DRAM Type: NOT DDR3!";
                                uart_text[7:0] <= 8'h0a;
                            end
                        end
                        3: begin
                            case(miso_data)
                                8'h00: begin
                                    uart_start_send <= 1'b1;
                                    uart_text_length <= 24; 
                                    uart_text[30*8-1:8] <= "Module Type: Undefined!";
                                    uart_text[7:0] <= 8'h0a;
                                end
                                8'h01: begin
                                    uart_start_send <= 1'b1;
                                    uart_text_length <= 19; 
                                    uart_text[30*8-1:8] <= "Module Type: RDIMM";
                                    uart_text[7:0] <= 8'h0a;
                                end
                                8'h02: begin
                                    uart_start_send <= 1'b1;
                                    uart_text_length <= 19; 
                                    uart_text[30*8-1:8] <= "Module Type: UDIMM";
                                    uart_text[7:0] <= 8'h0a;
                                end
                                8'h03: begin
                                    uart_start_send <= 1'b1;
                                    uart_text_length <= 21; 
                                    uart_text[30*8-1:8] <= "Module Type: SO-DIMM";
                                    uart_text[7:0] <= 8'h0a;
                                end
                            endcase
                        end
                        4: begin
                                uart_start_send <= 1'b1;
                                uart_text_length <= 29; 
                                uart_text[30*8-1:8*20] <= "BA_BITS: ";
                                uart_text[8*20-1:8*19] <= hex_to_ascii(miso_data[6:4]+3);
                                uart_text[8*19-1:8*18] <= 8'h0a;
                                uart_text[8*18-1:8*2] <= "SDRAM_CAPACITY: ";
                                uart_text[8*2-1:8*1] <= hex_to_ascii(miso_data[3:0]);
                                uart_text[7:0] <= 8'h0a;
                        end
                        5: begin
                                uart_start_send <= 1'b1;
                                uart_text_length <= 26; 
                                uart_text[30*8-1:8*16] <= "ROW_BITS: ";
                                case(miso_data[5:3])
                                    0: uart_text[8*16-1:8*14] <= "12";
                                    1: uart_text[8*16-1:8*14] <= "13";
                                    2: uart_text[8*16-1:8*14] <= "14";
                                    3: uart_text[8*16-1:8*14] <= "15";
                                    4: uart_text[8*16-1:8*14] <= "16";
                                endcase
                                uart_text[8*14-1:8*13] <= 8'h0a;
                                uart_text[8*13-1:8*3] <= "COL_BITS: ";
                                case(miso_data[2:0])
                                    0: uart_text[8*3-1:8*1] <= "9 ";
                                    1: uart_text[8*3-1:8*1] <= "10";
                                    2: uart_text[8*3-1:8*1] <= "11";
                                    3: uart_text[8*3-1:8*1] <= "12";
                                endcase
                                uart_text[8*1-1:8*0] <= 8'h0a;
                        end
                        7: begin
                                uart_start_send <= 1'b1;
                                uart_text_length <= 18; 
                                if(miso_data[5:3] == 1) begin
                                    uart_text[30*8-1:8] <= "DUAL_RANK_DIMM: 1";
                                end
                                else begin
                                    uart_text[30*8-1:8] <= "DUAL_RANK_DIMM: 0";
                                end
                                uart_text[7:0] <= 8'h0a;
                        end
                        8: begin
                            uart_start_send <= 1'b1;
                            uart_text_length <= 14; 
                            case(miso_data[2:0])
                                0: uart_text[30*8-1:8] <= "BYTE_LANES: 1";
                                1: uart_text[30*8-1:8] <= "BYTE_LANES: 2";
                                2: uart_text[30*8-1:8] <= "BYTE_LANES: 4";
                                3: uart_text[30*8-1:8] <= "BYTE_LANES: 8";
                            endcase
                            uart_text[7:0] <= 8'h0a;
                        end
                        10: begin
                            mtb_dividend = miso_data;
                            uart_start_send <= 1'b1;
                            uart_text_length <= 30; 
                            uart_text[30*8-1:8*1] <= "----- timing parameters -----";
                            uart_text[7:0] <= 8'h0a;
                        end
                        11: begin
                            mtb_divisor <= miso_data;
                            uart_start_send <= 1'b1;
                            uart_text_length <= 1; 
                            uart_text[7:0] <= "m";
                        end
                        12: begin // give time for mtb to be computer
                            uart_start_send <= 1'b1;
                            uart_text_length <= 14; 
                            uart_text[30*8-1:8*8] <= "tb: 0x";
                            uart_text[8*8-1:8*7] <= hex_to_ascii(mtb[7:4]);
                            uart_text[7*8-1:8*6] <= hex_to_ascii(mtb[3:0]);
                            uart_text[6*8-1:8*1] <= " (ps)";
                            uart_text[7:0] <= 8'h0a;
                        end
                        18: begin
                            uart_start_send <= 1'b1;
                            uart_text_length <= 17; 
                            uart_text[30*8-1:8*3] <= "TRCD: mtb * 0x";
                            uart_text[3*8-1:8*2] <= hex_to_ascii(miso_data[7:4]);
                            uart_text[2*8-1:8*1] <= hex_to_ascii(miso_data[3:0]);
                            uart_text[7:0] <= 8'h0a;
                        end
                        20: begin
                            uart_start_send <= 1'b1;
                            uart_text_length <= 16; 
                            uart_text[30*8-1:8*3] <= "TRP: mtb * 0x";
                            uart_text[3*8-1:8*2] <= hex_to_ascii(miso_data[7:4]);
                            uart_text[2*8-1:8*1] <= hex_to_ascii(miso_data[3:0]);
                            uart_text[7:0] <= 8'h0a;
                        end
                        21: begin
                            tras_high = miso_data[3:0];
                            uart_start_send <= 1'b1;
                            uart_text_length <= 1; 
                            uart_text[7:0] <= "T";
                        end
                        22: begin
                            uart_start_send <= 1'b1;
                            uart_text_length <= 17; 
                            uart_text[30*8-1:8*4] <= "RAS: mtb * 0x";
                            uart_text[4*8-1:8*3] <= hex_to_ascii(tras_high[3:0]);
                            uart_text[3*8-1:8*2] <= hex_to_ascii(miso_data[7:4]);
                            uart_text[2*8-1:8*1] <= hex_to_ascii(miso_data[3:0]);
                            uart_text[7:0] <= 8'h0a;
                        end
                        default: begin
                            skip_byte <= 1;
                        end
                    endcase
                    state_read_spd <= WAIT_UART_DONE;
                end
                WAIT_UART_DONE: if(uart_send_done || skip_byte) begin
                    state_read_spd <= READ_BYTE;
                    byte_address <= byte_address + 1;
                    if(byte_address == 63) begin
                        read_spd_done <= 1'b1;
                        state_read_spd <= IDLE;
                    end
                    skip_byte <= 1'b0;
                end
                else begin
                    uart_start_send <= 1'b0;
                end
            endcase
        end
    end
    assign mtb = mtb_dividend*1000/miso_data; // mtb is MCP (multicycle path) to give time for multiplication to be done

    // FSM for uart 
    // uart_text = "Hello" , uart_text_length = 5
    // [5<<3-1 (39):4<<3 (32)] = "H" , [4<<3-1 (31):3<<3(24)] = "e" , [3<<3-1(23):2<<3(16)] = "l" , [2<<3-1(15):1<<3(8)] = "l" ,  [1<<3-1(7):0<<3(0)] = "o"
     always @(posedge i_clk, negedge i_rst_n) begin
        if(!i_rst_n) begin
            state_uart_send <= IDLE;
            uart_text_length_index <= 0;
            uart_tx_en <= 0;
            uart_send_done <= 0;
            uart_tx_data <= 0;
        end
        else begin
            case(state_uart_send)
                IDLE: if (uart_start_send) begin // if receive request to send via uart
                    state_uart_send <= SEND_BYTE;
                    uart_text_length_index <= uart_text_length-1;
                end
                else begin
                    uart_tx_en <= 1'b0;
                    uart_send_done <= 1'b0;
                end
                SEND_BYTE: if(!uart_tx_busy) begin // if uart tx is not busy, send character
                    uart_tx_en <= 1'b1;
                    uart_tx_data <= uart_text[((uart_text_length_index)<<3) +: 8];
                end
                else begin // once busy, go to wait state
                    state_uart_send <= WAIT_SEND;
                    uart_tx_en <= 1'b0;
                end
                WAIT_SEND: if(!uart_tx_busy) begin // if not busy again, then uart is done sending
                    if(uart_text_length_index != 0) begin // if not yet at 0, go to next character
                        uart_text_length_index <= uart_text_length_index - 1;
                        state_uart_send <= SEND_BYTE;
                    end
                    else begin // if already at 1, go back to idle
                        state_uart_send <= IDLE;
                        uart_send_done <= 1'b1;
                    end
                end
                default: state_uart_send <= IDLE;
            endcase
        end
     end
     
     // Function to convert hex to ASCII
    function [7:0] hex_to_ascii;
        input [3:0] hex;
        begin
            if (hex < 4'd10)
                hex_to_ascii = hex + 8'd48; // ASCII for '0'-'9'
            else
                hex_to_ascii = hex + 8'd55; // ASCII for 'A'-'F'
        end
    endfunction


    // module instantiations
    i2c_master #(.DATA_WIDTH(8),.REGISTER_WIDTH(8),.ADDRESS_WIDTH(7))
        i2c_master_inst(
            .clock                  (i_clk),
            .reset_n                (i_rst_n),
            .enable                 (enable),
            .read_write             (read_write),
            .mosi_data              (8'd0),
            .register_address       (register_address),
            .device_address         (device_address),
            .divider                (249), // 100MHz/(4*(249+1)) =  100KHz

            .miso_data              (miso_data),
            .busy                   (busy),

            .external_serial_data   (i2c_sda),
            .external_serial_clock  (i2c_scl),
            .slave_nack             (slave_nack)
        );

        uart_tx #(
            .BIT_RATE(115200),
            .CLK_HZ(100_000_000),
            .PAYLOAD_BITS(8),
            .STOP_BITS(1)
        ) uart_tx_inst (
            .clk(i_clk), // Top level system clock input 
            .resetn(i_rst_n), // Asynchronous active low reset.
            .uart_txd(uart_tx)    , // UART transmit pin.
            .uart_tx_busy(uart_tx_busy), // Module busy sending previous item.
            .uart_tx_en(uart_tx_en), // Send the data on uart_tx_data
            .uart_tx_data(uart_tx_data)  // The data to be sent
        );

    generate 
        if(1) begin // set to 1 to debug registers in ILA
            (* mark_debug = "true" *) wire [7:0] byte_data_0;
            (* mark_debug = "true" *) wire [7:0] byte_data_1;
            (* mark_debug = "true" *) wire [7:0] byte_data_2;
            (* mark_debug = "true" *) wire [7:0] byte_data_3;
            (* mark_debug = "true" *) wire [7:0] byte_data_4;
            (* mark_debug = "true" *) wire [7:0] byte_data_5;
            (* mark_debug = "true" *) wire [7:0] byte_data_6;
            (* mark_debug = "true" *) wire [7:0] byte_data_7;
            (* mark_debug = "true" *) wire [7:0] byte_data_8;
            (* mark_debug = "true" *) wire [7:0] byte_data_9;
            (* mark_debug = "true" *) wire [7:0] byte_data_10;
            (* mark_debug = "true" *) wire [7:0] byte_data_11;
            (* mark_debug = "true" *) wire [7:0] byte_data_12;
            (* mark_debug = "true" *) wire [7:0] byte_data_13;
            (* mark_debug = "true" *) wire [7:0] byte_data_14;
            (* mark_debug = "true" *) wire [7:0] byte_data_15;
            (* mark_debug = "true" *) wire [7:0] byte_data_16;
            (* mark_debug = "true" *) wire [7:0] byte_data_17;
            (* mark_debug = "true" *) wire [7:0] byte_data_18;
            (* mark_debug = "true" *) wire [7:0] byte_data_19;
            (* mark_debug = "true" *) wire [7:0] byte_data_20;
            (* mark_debug = "true" *) wire [7:0] byte_data_21;
            (* mark_debug = "true" *) wire [7:0] byte_data_22;
            (* mark_debug = "true" *) wire [7:0] byte_data_23;
            (* mark_debug = "true" *) wire [7:0] byte_data_24;
            (* mark_debug = "true" *) wire [7:0] byte_data_25;
            (* mark_debug = "true" *) wire [7:0] byte_data_26;
            (* mark_debug = "true" *) wire [7:0] byte_data_27;
            (* mark_debug = "true" *) wire [7:0] byte_data_28;
            (* mark_debug = "true" *) wire [7:0] byte_data_29;
            (* mark_debug = "true" *) wire [7:0] byte_data_30;
            (* mark_debug = "true" *) wire [7:0] byte_data_31;
            (* mark_debug = "true" *) wire [7:0] byte_data_32;
            (* mark_debug = "true" *) wire [7:0] byte_data_33;
            (* mark_debug = "true" *) wire [7:0] byte_data_34;
            (* mark_debug = "true" *) wire [7:0] byte_data_35;
            (* mark_debug = "true" *) wire [7:0] byte_data_36;
            (* mark_debug = "true" *) wire [7:0] byte_data_37;
            (* mark_debug = "true" *) wire [7:0] byte_data_38;
            (* mark_debug = "true" *) wire [7:0] byte_data_39;
            (* mark_debug = "true" *) wire [7:0] byte_data_40;
            (* mark_debug = "true" *) wire [7:0] byte_data_41;
            (* mark_debug = "true" *) wire [7:0] byte_data_42;
            (* mark_debug = "true" *) wire [7:0] byte_data_43;
            (* mark_debug = "true" *) wire [7:0] byte_data_44;
            (* mark_debug = "true" *) wire [7:0] byte_data_45;
            (* mark_debug = "true" *) wire [7:0] byte_data_46;
            (* mark_debug = "true" *) wire [7:0] byte_data_47;
            (* mark_debug = "true" *) wire [7:0] byte_data_48;
            (* mark_debug = "true" *) wire [7:0] byte_data_49;
            (* mark_debug = "true" *) wire [7:0] byte_data_50;
            (* mark_debug = "true" *) wire [7:0] byte_data_51;
            (* mark_debug = "true" *) wire [7:0] byte_data_52;
            (* mark_debug = "true" *) wire [7:0] byte_data_53;
            (* mark_debug = "true" *) wire [7:0] byte_data_54;
            (* mark_debug = "true" *) wire [7:0] byte_data_55;
            (* mark_debug = "true" *) wire [7:0] byte_data_56;
            (* mark_debug = "true" *) wire [7:0] byte_data_57;
            (* mark_debug = "true" *) wire [7:0] byte_data_58;
            (* mark_debug = "true" *) wire [7:0] byte_data_59;
            (* mark_debug = "true" *) wire [7:0] byte_data_60;
            (* mark_debug = "true" *) wire [7:0] byte_data_61;
            (* mark_debug = "true" *) wire [7:0] byte_data_62;
            (* mark_debug = "true" *) wire [7:0] byte_data_63;

            // Assign each wire to its respective array index
            assign byte_data_0 = byte_data[0];
            assign byte_data_1 = byte_data[1];
            assign byte_data_2 = byte_data[2];
            assign byte_data_3 = byte_data[3];
            assign byte_data_4 = byte_data[4];
            assign byte_data_5 = byte_data[5];
            assign byte_data_6 = byte_data[6];
            assign byte_data_7 = byte_data[7];
            assign byte_data_8 = byte_data[8];
            assign byte_data_9 = byte_data[9];
            assign byte_data_10 = byte_data[10];
            assign byte_data_11 = byte_data[11];
            assign byte_data_12 = byte_data[12];
            assign byte_data_13 = byte_data[13];
            assign byte_data_14 = byte_data[14];
            assign byte_data_15 = byte_data[15];
            assign byte_data_16 = byte_data[16];
            assign byte_data_17 = byte_data[17];
            assign byte_data_18 = byte_data[18];
            assign byte_data_19 = byte_data[19];
            assign byte_data_20 = byte_data[20];
            assign byte_data_21 = byte_data[21];
            assign byte_data_22 = byte_data[22];
            assign byte_data_23 = byte_data[23];
            assign byte_data_24 = byte_data[24];
            assign byte_data_25 = byte_data[25];
            assign byte_data_26 = byte_data[26];
            assign byte_data_27 = byte_data[27];
            assign byte_data_28 = byte_data[28];
            assign byte_data_29 = byte_data[29];
            assign byte_data_30 = byte_data[30];
            assign byte_data_31 = byte_data[31];
            assign byte_data_32 = byte_data[32];
            assign byte_data_33 = byte_data[33];
            assign byte_data_34 = byte_data[34];
            assign byte_data_35 = byte_data[35];
            assign byte_data_36 = byte_data[36];
            assign byte_data_37 = byte_data[37];
            assign byte_data_38 = byte_data[38];
            assign byte_data_39 = byte_data[39];
            assign byte_data_40 = byte_data[40];
            assign byte_data_41 = byte_data[41];
            assign byte_data_42 = byte_data[42];
            assign byte_data_43 = byte_data[43];
            assign byte_data_44 = byte_data[44];
            assign byte_data_45 = byte_data[45];
            assign byte_data_46 = byte_data[46];
            assign byte_data_47 = byte_data[47];
            assign byte_data_48 = byte_data[48];
            assign byte_data_49 = byte_data[49];
            assign byte_data_50 = byte_data[50];
            assign byte_data_51 = byte_data[51];
            assign byte_data_52 = byte_data[52];
            assign byte_data_53 = byte_data[53];
            assign byte_data_54 = byte_data[54];
            assign byte_data_55 = byte_data[55];
            assign byte_data_56 = byte_data[56];
            assign byte_data_57 = byte_data[57];
            assign byte_data_58 = byte_data[58];
            assign byte_data_59 = byte_data[59];
            assign byte_data_60 = byte_data[60];
            assign byte_data_61 = byte_data[61];
            assign byte_data_62 = byte_data[62];
            assign byte_data_63 = byte_data[63];
        end
    endgenerate
endmodule


