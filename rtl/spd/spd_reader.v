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
    (* mark_debug = "true" *) output reg read_spd_done
    // uart interface
    // input uart_rx,
    // output uart_tx
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
                WAIT_ACK = 2;
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
    end

    // main FSM
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
                        state_find_i2c_address <= IDLE;
                        find_i2c_address_done <= 1'b1;
                    end
                    end
                    else begin
                        enable <= 1'b0;
                    end
                default: state_find_i2c_address <= IDLE;
            endcase

            // read bytes from SPD
            case(state_read_spd) 
                IDLE: if(find_i2c_address_done && !read_spd_done && !nack_unexpected_err) begin // start read SPD only once i2c address is found
                    state_read_spd <= READ_BYTE;
                    byte_address <= 6'h00; // start read from byte 0
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
                    else begin // I2C acks so store the received byte
                        byte_data[byte_address] <= miso_data;
                        state_read_spd <= READ_BYTE;
                        byte_address <= byte_address + 1;
                        if(byte_address == 63) begin
                            read_spd_done <= 1'b1;
                            state_read_spd <= IDLE;
                        end
                    end
                    end
                    else begin
                        enable <= 1'b0;
                    end
            endcase
        end
    end

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
endmodule


