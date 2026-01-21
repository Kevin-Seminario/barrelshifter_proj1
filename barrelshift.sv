`timescale 1ns / 1ps
`default_nettype none

// a simple module that gives an RTL description of the barrelshifter.
module barrelshifter #(parameter D_SIZE) {
	input logic [D_SIZE-1:0]		x_in,
	input logic [$clog2(D_SIZE)-1:0]	s_in,
	input logic [2:0]			op_in,
	output logic [D_SIZE-1:0]		y_out,
	output logic				zf_out,
	output logic				vf_out
};
	assign y_out = 0;
	assign vf_out = 0;
	assign zf_out = 0;
endmodule: barrelshifter
