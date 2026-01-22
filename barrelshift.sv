`timescale 1ns / 1ps
`default_nettype none`
module mux2 #(parameter V_SIZE) {
	input logic [V_SIZE - 1:0] 		a,
	input logic [V_SIZE - 1:0]		b,
	input logic						sel,
	output logic					out
};
	logic t_1, t_2, sel_bar;
	and (t_1, a, sel);
	and (t_2, b, sel_bar);
	not (sel_bar, sel);
	or (y, t_1, t_2);
endmodule: mux2

// a simple module that gives an RTL description of the barrelshifter.
module barrelshifter #(parameter D_SIZE) {
	input logic [D_SIZE-1:0]			x_in,
	input logic [$clog2(D_SIZE)-1:0]	s_in,
	input logic [2:0]					op_in,
	output logic [D_SIZE-1:0]			y_out,
	output logic						zf_out,
	output logic						vf_out
};

	logic [D_SIZE * ($clog2(D_SIZE) + 1)-1:0] external_store;
    assign external_store[D_SIZE * ($clog2(D_SIZE) + 1) - 1:D_SIZE * $clog2(D_SIZE)] = x_in[D_SIZE-1:0];
    integer pow = 0;

	// Set the VG iff shift left airthmetic or >=1 shifted-out bits (X_(N-2) through X_(N-s-1))
	// differ from the sign bit (X_(N-1)).
	// The zero flag ZF is set iff Y is the zero vector
	always @(*) begin
		vf_out = 1'b0;
		casez (op_in)
			3'b000: begin // Shift Right Logical (unsigned extension)
				for (integer i = $clog2(D_SIZE) - 1; i >= 0; i = i - 1) begin
      				pow = 2 ** i;
					for (integer j = 0; j < D_SIZE; j = j + 1) begin
						if (j + pow >= D_SIZE) begin
							external_store[D_SIZE * i + j] = s_in[i] ? 0 : external_store[D_SIZE * (i + 1) + j];
						end
						else begin
							external_store[D_SIZE * i + j] = s_in[i] ? external_store[D_SIZE * (i + 1) + j + pow] : external_store[D_SIZE * (i + 1) + j];
						end
					end
				end
			end
			3'b001: begin // Shift Right Arithmetic (sign extension)
				for (integer i = $clog2(D_SIZE) - 1; i >= 0; i = i - 1) begin
      				pow = 2 ** i;
					for (integer j = 0; j < D_SIZE; j = j + 1) begin
						if (j + pow >= D_SIZE) begin
							external_store[D_SIZE * i + j] = s_in[i] ? external_store[D_SIZE * (i + 2) - 1] : external_store[D_SIZE * (i + 1) + j];
						end
						else begin
							external_store[D_SIZE * i + j] = s_in[i] ? external_store[D_SIZE * (i + 1) + j + pow] : external_store[D_SIZE * (i + 1) + j];
						end
					end
				end
			end
			3'b01z: begin // Rotate Right
				for (integer i = $clog2(D_SIZE) - 1; i >= 0; i = i - 1) begin
      				pow = 2 ** i;
      				for (integer j = 0; j < D_SIZE; j = j + 1) begin
          				if (j + pow >= D_SIZE) begin
            				external_store[D_SIZE * i + j] = s_in[i] ? external_store[D_SIZE * i + j + pow] : external_store[D_SIZE * (i + 1) + j];
          				end
          				else begin
            				external_store[D_SIZE * i + j] = s_in[i] ? external_store[D_SIZE * (i + 1) + j + pow] : external_store[D_SIZE * (i + 1) + j];
          				end
       				end
				end
			end
			3'b100: begin // Shift Left Logical
				for (integer i = $clog2(D_SIZE) - 1; i >= 0; i = i - 1) begin
      				pow = 2 ** i;
      				for (integer j = 0; j < D_SIZE; j = j + 1) begin
          				if (j < pow) begin
            				external_store[D_SIZE * i + j] = s_in[i] ? 0 : external_store[D_SIZE * (i + 1) + j];
          				end
          				else begin
            				external_store[D_SIZE * i + j] = s_in[i] ? external_store[D_SIZE * (i + 1) + j - pow] : external_store[D_SIZE * (i + 1) + j];
          				end
       				end
				end
			end
			3'b101: begin // Shift Left Arithmetic
				for (integer i = $clog2(D_SIZE) - 1; i >= 0; i = i - 1) begin
      				pow = 2 ** i;
      				for (integer j = 0; j < D_SIZE; j = j + 1) begin
          				if (j < pow) begin
            				external_store[D_SIZE * i + j] = s_in[i] ? 0 : external_store[D_SIZE * (i + 1) + j];
          				end
          				else begin
            				external_store[D_SIZE * i + j] = s_in[i] ? external_store[D_SIZE * (i + 1) + j - pow] : external_store[D_SIZE * (i + 1) + j];
          				end
       				end
				end
			end
			3'b11z: begin // Rotate Left
				for (integer i = $clog2(D_SIZE) - 1; i >= 0; i = i - 1) begin
      				pow = 2 ** i;
      				for (integer j = 0; j < D_SIZE; j = j + 1) begin
          				if (j < pow) begin
            				external_store[D_SIZE * i + j] = s_in[i] ? external_store[D_SIZE * (i + 2) + j - pow] : external_store[D_SIZE * (i + 1) + j];
          				end
          				else begin
            				external_store[D_SIZE * i + j] = s_in[i] ? external_store[D_SIZE * (i + 1) + j - pow] : external_store[D_SIZE * (i + 1) + j];
          				end
       				end
				end
			end
		endcase
		y_out[D_SIZE-1:0] = external_store[D_SIZE-1:0];
		zf_out = ~& y_out;
	end
endmodule: barrelshifter
