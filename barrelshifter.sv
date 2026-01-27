`timescale 1ns / 1ps
`default_nettype none

// a simple module that gives an RTL description of the barrelshifter.
module barrelshifter #(parameter D_SIZE) (
	input logic [D_SIZE-1:0]			x_in,
	input logic [$clog2(D_SIZE)-1:0]	s_in,
	input logic [2:0]					op_in,
	output logic [D_SIZE-1:0]			y_out,
	output logic						zf_out,
	output logic						vf_out
);

  logic [D_SIZE * ($clog2(D_SIZE) + 1)-1:0] logic_shift_right_interim;
  assign logic_shift_right_interim[D_SIZE*($clog2(D_SIZE) + 1)-1:D_SIZE*$clog2(D_SIZE)] = x_in[D_SIZE-1:0];
  
  logic [D_SIZE * ($clog2(D_SIZE) + 1)-1:0] arith_shift_right_interim;
  assign arith_shift_right_interim[D_SIZE*($clog2(D_SIZE) + 1)-1:D_SIZE*$clog2(D_SIZE)] = x_in[D_SIZE-1:0];
  
  logic [D_SIZE * ($clog2(D_SIZE) + 1)-1:0] rot_right_interim;
  assign rot_right_interim[D_SIZE*($clog2(D_SIZE) + 1)-1:D_SIZE*$clog2(D_SIZE)] = x_in[D_SIZE-1:0];
  
  logic [D_SIZE * ($clog2(D_SIZE) + 1)-1:0] logic_shift_left_interim;
  assign logic_shift_left_interim[D_SIZE*($clog2(D_SIZE) + 1)-1:D_SIZE*$clog2(D_SIZE)] = x_in[D_SIZE-1:0];
  
  logic [D_SIZE * ($clog2(D_SIZE) + 1)-1:0] arith_shift_left_interim;
  assign arith_shift_left_interim[D_SIZE*($clog2(D_SIZE) + 1)-1:D_SIZE*$clog2(D_SIZE)] = x_in[D_SIZE-1:0];
  
  logic [D_SIZE * ($clog2(D_SIZE) + 1)-1:0] rot_left_interim;
  assign rot_left_interim[D_SIZE*($clog2(D_SIZE) + 1)-1:D_SIZE*$clog2(D_SIZE)] = x_in[D_SIZE-1:0];
  
  long_nor #(D_SIZE) zf_long_nor (y_out[D_SIZE-1:0], zf_out);
  
  logic [$clog2(D_SIZE)-1:0] vf_asl_interim;
  logic [$clog2(D_SIZE)-1:0] vf_asl_mux_interim;
  logic zr_flag_sin, same_bit_flag, overflow_flag;
  long_nor #($clog2(D_SIZE)) vf_zero_check (s_in, zr_flag_sin);
  long_or #($clog2(D_SIZE)) vf_asl_mux_and_all (vf_asl_mux_interim[$clog2(D_SIZE)-1:0], same_bit_flag);
  mux2 vf_zero_mux (1'b0, same_bit_flag, zr_flag_sin, overflow_flag);
  
  genvar i, j, k;
  generate
    for (i = 0; i < $clog2(D_SIZE); i = i + 1) begin
      for (j = 0; j < D_SIZE; j = j + 1) begin
        if (j + 2 ** i < D_SIZE) begin 
          mux2 flsrmux (logic_shift_right_interim[D_SIZE * (i + 1) + j + 2 ** i], logic_shift_right_interim[D_SIZE * (i + 1) + j], s_in[i], logic_shift_right_interim[D_SIZE * i + j]);
          mux2 fasrmux (arith_shift_right_interim[D_SIZE * (i + 1) + j + 2 ** i], arith_shift_right_interim[D_SIZE * (i + 1) + j], s_in[i], arith_shift_right_interim[D_SIZE * i + j]);
          mux2 frrmux (rot_right_interim[D_SIZE * (i + 1) + j + 2 ** i], rot_right_interim[D_SIZE * (i + 1) + j], s_in[i], rot_right_interim[D_SIZE * i + j]);
        end
        else begin
          mux2 ulsrmux (1'b0, logic_shift_right_interim[D_SIZE * (i + 1) + j], s_in[i], logic_shift_right_interim[D_SIZE * i + j]);
          mux2 uasrmux (x_in[D_SIZE-1], arith_shift_right_interim[D_SIZE * (i + 1) + j], s_in[i], arith_shift_right_interim[D_SIZE * i + j]);
          mux2 urrmux (rot_right_interim[D_SIZE * (i + 1) + ((j + 2 ** i) % D_SIZE)], rot_right_interim[D_SIZE * (i + 1) + j], s_in[i], rot_right_interim[D_SIZE * i + j]);
        end
        if (j < 2 ** i) begin
          mux2 flslmux (1'b0, logic_shift_left_interim[D_SIZE * (i + 1) + j], s_in[i], logic_shift_left_interim[D_SIZE * i + j]);
          mux2 flrmux (rot_left_interim[D_SIZE * (i + 1) + (j + D_SIZE - 2 ** i)], rot_left_interim[D_SIZE * (i + 1) + j], s_in[i], rot_left_interim[D_SIZE * i + j]);
        end
        else begin
          mux2 ulslmux (logic_shift_left_interim[D_SIZE * (i + 1) + j - 2 ** i], logic_shift_left_interim[D_SIZE * (i + 1) + j], s_in[i], logic_shift_left_interim[D_SIZE * i + j]);
          mux2 ulrmux (rot_left_interim[D_SIZE * (i + 1) + j - 2 ** i], rot_left_interim[D_SIZE * (i + 1) + j], s_in[i], rot_left_interim[D_SIZE * i + j]);
        end
      end
      assign arith_shift_left_interim[D_SIZE * (i + 1) - 1] = arith_shift_left_interim[D_SIZE * (i + 2) - 1];
      for (k = 1; k < D_SIZE; k = k + 1) begin
        if (k - 1 < 2 ** i) begin
          mux2 farlmux (1'b0, arith_shift_left_interim[D_SIZE * (i + 1) + k - 1], s_in[i], arith_shift_left_interim[D_SIZE * i + k - 1]);
        end
        else begin
          mux2 uarlmux (arith_shift_left_interim[D_SIZE * (i + 1) + k - 1 - 2 ** i], arith_shift_left_interim[D_SIZE * (i + 1) + k - 1], s_in[i], arith_shift_left_interim[D_SIZE * i + k - 1]);
        end
      end
      long_xor #(2 ** i + 1) vf_xors (logic_shift_left_interim[D_SIZE * (i + 2) - 1:D_SIZE * (i + 2) - 2 ** i - 1], vf_asl_interim[i]);
      mux2 vf_mux (vf_asl_interim[i], 1'b0, s_in[i], vf_asl_mux_interim[i]);
    end
    
  endgenerate

  logic [D_SIZE-1:0] final_y_out;
  logic [D_SIZE-1:0] lrs_ars_mux_out, rs_rr_mux_out, lsl_asl_mux_out, ls_rl_mux_out;
  long_mux2 #(D_SIZE) lrs_ars_mux (arith_shift_right_interim[D_SIZE-1:0], logic_shift_right_interim[D_SIZE-1:0], op_in[0], lrs_ars_mux_out[D_SIZE-1:0]);
  long_mux2 #(D_SIZE) lsl_asl_mux (arith_shift_left_interim[D_SIZE-1:0], logic_shift_left_interim[D_SIZE-1:0], op_in[0], lsl_asl_mux_out[D_SIZE-1:0]);
  long_mux2 #(D_SIZE) rs_rr_mux (rot_right_interim[D_SIZE-1:0], lrs_ars_mux_out[D_SIZE-1:0], op_in[1], rs_rr_mux_out[D_SIZE-1:0]);
  long_mux2 #(D_SIZE) ls_rl_mux (rot_left_interim[D_SIZE-1:0], lsl_asl_mux_out[D_SIZE-1:0], op_in[1], ls_rl_mux_out[D_SIZE-1:0]);
  long_mux2 #(D_SIZE) final_y_mux (ls_rl_mux_out[D_SIZE-1:0], rs_rr_mux_out[D_SIZE-1:0], op_in[2], final_y_out[D_SIZE-1:0]);


  logic vf_out_trigger, vf_out_final;
  equalizer #(2'b11) op_vf_long (op_in, 3'b101, vf_out_trigger);
  mux2 vf_check (overflow_flag, 1'b0, vf_out_trigger, vf_out_final);
  
  always_comb begin
    vf_out = vf_out_final;
    y_out = final_y_out;
  end
endmodule: barrelshifter

module mux2 (
	input logic		a_in,
	input logic		b_in,
	input logic		sel_in,
	output logic 	out
);
	logic temp1, temp2, bar_sel_in;
	and (temp1, a_in, sel_in);
	not (bar_sel_in, sel_in);
	and (temp2, b_in, bar_sel_in);
	or (out, temp1, temp2);
endmodule: mux2

module long_mux2 #(parameter V_SIZE) (
  input logic [V_SIZE-1:0]    av_in,
  input logic [V_SIZE-1:0]    bv_in,
  input logic                 sel_in,
  output logic [V_SIZE-1:0]   outv
);
  genvar i;
  generate
    for (i = 0; i < V_SIZE; i = i + 1) begin
      mux2 temp_mux (av_in[i], bv_in[i], sel_in, outv[i]);
    end
  endgenerate
endmodule: long_mux2

module long_xor #(parameter V_SIZE) (
  input logic [V_SIZE-1:0]		in,
  output logic					out
);
  logic [V_SIZE-1:0] or_interim;
  logic [V_SIZE:0] xor_interim;
  assign or_interim[0] = 1'b0;
  assign out = or_interim[V_SIZE - 1];
  
  genvar i;
  generate
    for (i = 1; i < V_SIZE; i = i + 1) begin
      xor (xor_interim[i-1], in[i], in[i - 1]);
      or (or_interim[i], or_interim[i - 1], xor_interim[i - 1]);
    end
  endgenerate
endmodule: long_xor

module long_nor #(parameter V_SIZE) (
  input logic [V_SIZE-1:0]		in,
  output logic					out
);
  logic [V_SIZE:0] and_interim;
  logic [V_SIZE:0] nor_interim;
  not (nor_interim[0], in[0]);
  assign and_interim[0] = nor_interim[0];
  assign out = and_interim[V_SIZE - 1];
  
  genvar i;
  generate
    for (i = 1; i < V_SIZE; i = i + 1) begin
      nor (nor_interim[i], in[i], in[i - 1]);
      and (and_interim[i], and_interim[i - 1], nor_interim[i]);
    end
  endgenerate
endmodule: long_nor

module long_or #(parameter V_SIZE) (
  input logic [V_SIZE-1:0]		in,
  output logic					out
);
  logic [V_SIZE-1:0] or_interim;
  assign or_interim[0] = in[0];
  assign out = or_interim[V_SIZE-1];
  
  genvar i;
  generate
    for (i = 1; i < V_SIZE; i = i + 1) begin
      or (or_interim[i], or_interim[i - 1], in[i]);
    end
  endgenerate
endmodule: long_or

module equalizer #(parameter V_SIZE) (
  input logic [V_SIZE-1:0]		in_0,
  input logic [V_SIZE-1:0]    in_1,
  output logic					      out
);
  logic [V_SIZE-1:0] xnor_interim;
  logic [V_SIZE-1:0] and_interim;
  xnor (xnor_interim[0], in_0[0], in_1[0]);
  assign and_interim[0] = xnor_interim[0];
  assign out = and_interim[V_SIZE-1];
  
  genvar i;
  generate
    for (i = 1; i < V_SIZE; i = i + 1) begin
      xnor (xnor_interim[i], in_0[i], in_1[i]);
      and (and_interim[i], xnor_interim[i], and_interim[i - 1]);
    end
  endgenerate
endmodule: equalizer