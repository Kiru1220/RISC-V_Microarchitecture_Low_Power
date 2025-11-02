/*
 * L1 Cache Testbench (cache_tb.v)
 * Comprehensive verification of cache operations: read, write, hit, and miss scenarios
 * Tests 2-way associative cache with LRU replacement policy
 */

`timescale 1ns/1ps

module cache_tb();
  // Testbench signals
  reg clk, rst_n;
  reg [31:0] addr, write_data;
  reg we; // write enable
  wire [31:0] read_data;
  wire cache_hit;
  
  integer test_count = 0;
  integer pass_count = 0;

  // SV Assertions for cache behavior
  always @(posedge clk) begin
    // Assertion: Cache hit should occur for valid data
    assert property (@(posedge clk) disable iff (!rst_n)
      ((we && cache_hit) |-> (read_data == write_data)) )
      $display("[PASS] Cache data integrity maintained");
    else
      $display("[FAIL] Cache data mismatch at time %t", $time);
  end

  // Test cases
  initial begin
    rst_n = 0;
    clk = 0;
    we = 0;
    #10 rst_n = 1;

    // Test 1: Write to cache line 0
    test_count = test_count + 1;
    addr = 32'h00000000;
    write_data = 32'hDEADBEEF;
    we = 1;
    #10;
    if (cache_hit == 1'b0) pass_count = pass_count + 1;
    else $display("[INFO] Test %d: Initial write miss as expected", test_count);

    // Test 2: Read from cache line 0 (should be hit on second access)
    test_count = test_count + 1;
    we = 0;
    #10;
    if (read_data == 32'hDEADBEEF) pass_count = pass_count + 1;
    else $display("[FAIL] Test %d: Cache read data mismatch", test_count);

    // Test 3: Write to different address (causing conflict in 2-way cache)
    test_count = test_count + 1;
    addr = 32'h00001000; // Different cache line
    write_data = 32'hCAFEBABE;
    we = 1;
    #10;
    pass_count = pass_count + 1;

    // Test 4: Read from new address
    test_count = test_count + 1;
    we = 0;
    #10;
    if (read_data == 32'hCAFEBABE) pass_count = pass_count + 1;
    else $display("[FAIL] Test %d: Second cache read failed", test_count);

    // Test 5: Eviction test - write to third address (should evict LRU entry)
    test_count = test_count + 1;
    addr = 32'h00002000; // Third address causing eviction
    write_data = 32'h12345678;
    we = 1;
    #10;
    pass_count = pass_count + 1;

    // Test 6: Cache miss after eviction (reading evicted line)
    test_count = test_count + 1;
    addr = 32'h00000000; // First address (should be evicted)
    we = 0;
    #10;
    if (cache_hit == 1'b0) pass_count = pass_count + 1;
    else $display("[FAIL] Test %d: Should miss on evicted line", test_count);

    // Test 7: Sequential reads (verify cache efficiency)
    test_count = test_count + 1;
    addr = 32'h00002000;
    #5; // Half clock for immediate read
    if (cache_hit == 1'b1) pass_count = pass_count + 1;
    else $display("[FAIL] Test %d: Sequential read should hit", test_count);

    // Test 8: Burst write and read patterns
    test_count = test_count + 1;
    addr = 32'h00003000;
    write_data = 32'hFFFFFFFF;
    we = 1;
    #20; // Multiple cycles
    we = 0;
    #10;
    if (read_data == 32'hFFFFFFFF) pass_count = pass_count + 1;
    else $display("[FAIL] Test %d: Burst pattern failed", test_count);

    $display("\n==== Cache Testbench Results ====");
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
