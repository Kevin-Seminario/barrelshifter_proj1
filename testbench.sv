`timescale 1ns / 1ps
`default_nettype none

module bs_testbench #(parameter D_SIZE = 4) ();

  logic                           clk_in;
  logic [D_SIZE-1:0]              x_in;
  logic [$clog2(D_SIZE)-1:0]      s_in;
  logic [2:0]                     op_in;
  logic [D_SIZE-1:0]              y_out_ref, y_out_stu;
  logic                           zf_out_ref, zf_out_stu;
  logic                           vf_out_ref, vf_out_stu;
  int                             num_wrong;

  // This is a known working module. Our reference
  barrelshifter_ref #(D_SIZE) ref_bs (
    .x_in(x_in),
    .s_in(s_in),
    .op_in(op_in),
    .y_out(y_out_ref),
    .zf_out(zf_out_ref),
    .vf_out(vf_out_ref)
  );

  // This is the student shifter. The DUT (design under test)
  barrelshifter #(D_SIZE) dut (
    .x_in(x_in),
    .s_in(s_in),
    .op_in(op_in),
    .y_out(y_out_stu),
    .zf_out(zf_out_stu),
    .vf_out(vf_out_stu)
  );

  //initial block...this is our test simulation
  initial begin
    $display("Starting simulator");
    clk_in = 0; //0 is generally a safe value to initialize with and not specify size
    x_in = 0;
    s_in = 0;
    op_in = 0;
    for (int op = 0; op < 8; op++) begin
      num_wrong = 0;
      for (int i = 0; i < $pow(2, D_SIZE); i++) begin
        for (int j = 0; j < D_SIZE; j++) begin
          x_in = i[D_SIZE-1:0];
          s_in = j[$clog2(D_SIZE)-1:0];
          op_in = op[2:0];
          #1; // Wait a short time for the combinational logic to propogate
          if ((y_out_ref != y_out_stu) || (zf_out_ref != zf_out_stu) || (vf_out_ref != vf_out_stu)) begin
            num_wrong++;
            $display("\tref != dut --- op: %b, x_in: %b, s_in: %d)", op_in, x_in, s_in);
            $display(
              "\t\t(y_out, vf, zf) - ref: (%b, %d, %d), dut: (%b, %d, %d)", 
              y_out_ref, vf_out_ref, zf_out_ref, y_out_stu, vf_out_stu, zf_out_stu
            );
          end
        end
      end
      $display("OP: %b -- num_wrong: %d", op[2:0], num_wrong);
    end
    $finish;
  end
endmodule: bs_testbench
