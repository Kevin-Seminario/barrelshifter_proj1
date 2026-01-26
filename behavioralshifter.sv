`timescale 1ns / 1ps
`default_nettype none

// A behavioral description of a barrel shifter. Used as a reference
module barrelshifter_ref #(parameter D_SIZE) (
  input  logic [D_SIZE-1:0]         x_in,
  input  logic [$clog2(D_SIZE)-1:0] s_in,
  input  logic [2:0]                op_in,
  output logic [D_SIZE-1:0]         y_out,
  output logic                      zf_out,
  output logic                      vf_out
);

  // The following wires are used during overflow calculations
  logic msb; // most significant bit
  logic [D_SIZE-1:0] shifted_out; // bits which were shifted out during ASL

  always_comb begin
    casez(op_in)
      3'b000: y_out = x_in >> s_in; // shift right logical
      3'b001: y_out = ($signed(x_in)) >>> s_in; // shift right arithmetic
      3'b01?: y_out = (x_in >> s_in) | (x_in << (-s_in)); // rotate right
      3'b100: y_out = x_in << s_in; // shift left logical
      3'b101: y_out = ((x_in <<< s_in) & ~(1<<(D_SIZE-1))) | (x_in & (1<<(D_SIZE-1))); // shift left arithmetic
      3'b11?: y_out = (x_in << s_in) | (x_in >> (-s_in)); // rotate left
      default: y_out = 'x;
    endcase
    // During an ASR op, if any of the bits shifted out are different
    // than the most significant bit, then there is overflow.
    // ~s_in is a bit hack to calc D_SIZE-s_in (assuming D_SIZE is a power of 2)
    msb = x_in[D_SIZE-1];
    shifted_out = $signed(x_in) >>> ~s_in; // store the bits which were shifted out
    vf_out = (op_in == 3'b101) && |(shifted_out[D_SIZE-2:0] ^ {D_SIZE-1{msb}});
    zf_out = &(~y_out);
  end
endmodule : barrelshifter_ref
