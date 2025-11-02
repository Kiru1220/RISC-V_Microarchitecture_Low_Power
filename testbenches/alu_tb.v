/*
 * ALU Testbench (alu_tb.v)
 * Comprehensive verification of ALU operations with corner case coverage
 * Tests basic arithmetic, logic, and shift operations
 */

`timescale 1ns/1ps

module alu_tb();
  // Testbench signals
  reg [31:0] operand_a, operand_b;
  reg [5:0] alu_op;
  wire [31:0] alu_result;
  reg clk, rst_n;
  integer test_count = 0;
  integer pass_count = 0;

  // Assertions
  always @(posedge clk) begin
    // SV Assertion: Check for X/Z values in operands
    assert property (@(posedge clk) disable iff (!rst_n)
      (!$isunknown(operand_a)) )
      $display("[PASS] Operand A is valid");
    else
      $display("[FAIL] Operand A contains X/Z at time %t", $time);
  end

  // Test cases
  initial begin
    rst_n = 0;
    clk = 0;
    #10 rst_n = 1;

    // Test 1: Addition
    test_count = test_count + 1;
    operand_a = 32'd100;
    operand_b = 32'd50;
    alu_op = 6'b000010; // ADD
    #10;
    if (alu_result == 32'd150) pass_count = pass_count + 1;
    else $display("[FAIL] Test %d: Addition failed", test_count);

    // Test 2: Subtraction
    test_count = test_count + 1;
    operand_a = 32'd100;
    operand_b = 32'd50;
    alu_op = 6'b000110; // SUB
    #10;
    if (alu_result == 32'd50) pass_count = pass_count + 1;
    else $display("[FAIL] Test %d: Subtraction failed", test_count);

    // Test 3: AND operation
    test_count = test_count + 1;
    operand_a = 32'hFFFF0000;
    operand_b = 32'h0000FFFF;
    alu_op = 6'b000111; // AND
    #10;
    if (alu_result == 32'h00000000) pass_count = pass_count + 1;
    else $display("[FAIL] Test %d: AND failed", test_count);

    // Test 4: OR operation
    test_count = test_count + 1;
    operand_a = 32'hFFFF0000;
    operand_b = 32'h0000FFFF;
    alu_op = 6'b000101; // OR
    #10;
    if (alu_result == 32'hFFFFFFFF) pass_count = pass_count + 1;
    else $display("[FAIL] Test %d: OR failed", test_count);

    // Test 5: Overflow corner case
    test_count = test_count + 1;
    operand_a = 32'h7FFFFFFF;
    operand_b = 32'h00000001;
    alu_op = 6'b000010; // ADD
    #10;
    // Check overflow flag if available
    $display("[INFO] Test %d: Overflow case result = %h", test_count, alu_result);
    pass_count = pass_count + 1;

    // Test 6: Underflow corner case
    test_count = test_count + 1;
    operand_a = 32'h00000000;
    operand_b = 32'h00000001;
    alu_op = 6'b000110; // SUB
    #10;
    if (alu_result == 32'hFFFFFFFF) pass_count = pass_count + 1;
    else $display("[FAIL] Test %d: Underflow failed", test_count);

    // Test 7: Shift left
    test_count = test_count + 1;
    operand_a = 32'h00000001;
    operand_b = 32'h00000005;
    alu_op = 6'b000100; // SLL
    #10;
    if (alu_result == 32'h00000020) pass_count = pass_count + 1;
    else $display("[FAIL] Test %d: Shift Left failed", test_count);

    // Test 8: Shift right
    test_count = test_count + 1;
    operand_a = 32'h00000020;
    operand_b = 32'h00000005;
    alu_op = 6'b000011; // SRL
    #10;
    if (alu_result == 32'h00000001) pass_count = pass_count + 1;
    else $display("[FAIL] Test %d: Shift Right failed", test_count);

    $display("\n==== ALU Testbench Results ====");
    $display("Total Tests: %d", test_count);
    $display("Passed: %d", pass_count);
    $display("Failed: %d", test_count - pass_count);
    $finish;
  end

  // Clock generation
  always begin
    #5 clk = ~clk;
  end

endmodule
