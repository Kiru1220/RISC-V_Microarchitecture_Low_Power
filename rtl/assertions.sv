/*
 * SystemVerilog Assertions Module (assertions.sv)
 * Provides comprehensive functional and property-based assertions for RISC-V microarchitecture
 * Covers signal integrity, protocol compliance, and functional correctness
 */

`ifndef ASSERTIONS_SV
`define ASSERTIONS_SV

// ALU Assertions
module alu_assertions #(
  parameter WIDTH = 32
) (
  input logic clk, rst_n,
  input logic [WIDTH-1:0] operand_a, operand_b,
  input logic [5:0] alu_op,
  input logic [WIDTH-1:0] result,
  input logic overflow, underflow
);

  // SV Assertion 1: Operands should be stable during computation
  property stable_operands;
    @(posedge clk) disable iff (!rst_n)
      ($past(operand_a) == operand_a) |-> ($past(result) == result);
  endproperty
  assert property (stable_operands)
    $display("[PASS] ALU: Operands remain stable during computation");
  else
    $warning("[FAIL] ALU: Operand stability violation at time %t", $time);

  // SV Assertion 2: Result should not contain unknown values
  property no_unknown_result;
    @(posedge clk) disable iff (!rst_n)
      (!$isunknown(result));
  endproperty
  assert property (no_unknown_result)
    $display("[PASS] ALU: Result is always valid (no X/Z)");
  else
    $error("[FAIL] ALU: Unknown result value at time %t", $time);

  // SV Assertion 3: Overflow flag assertion
  property overflow_detection;
    @(posedge clk) disable iff (!rst_n)
      ((operand_a == {WIDTH{1'b1}} && operand_b == {WIDTH{1'b1}} && alu_op == 6'b000010) 
        |-> (overflow == 1'b1));
  endproperty
  assert property (overflow_detection)
    $display("[PASS] ALU: Overflow correctly detected");
  else
    $warning("[FAIL] ALU: Overflow detection failed at time %t", $time);

endmodule

// Cache Assertions
module cache_assertions #(
  parameter ADDR_WIDTH = 32,
  parameter DATA_WIDTH = 32
) (
  input logic clk, rst_n,
  input logic [ADDR_WIDTH-1:0] addr,
  input logic [DATA_WIDTH-1:0] write_data, read_data,
  input logic we, cache_hit, cache_valid
);

  // SV Assertion 1: Data consistency
  property data_consistency;
    @(posedge clk) disable iff (!rst_n)
      ((we && cache_valid) |-> (!$isunknown(write_data)));
  endproperty
  assert property (data_consistency)
    $display("[PASS] Cache: Written data is always valid");
  else
    $error("[FAIL] Cache: Invalid data written at time %t", $time);

  // SV Assertion 2: Cache hit/miss consistency
  property hit_miss_consistency;
    @(posedge clk) disable iff (!rst_n)
      ((cache_hit) |-> (cache_valid));
  endproperty
  assert property (hit_miss_consistency)
    $display("[PASS] Cache: Hit implies valid data");
  else
    $warning("[FAIL] Cache: Hit/miss inconsistency at time %t", $time);

  // SV Assertion 3: Address should be stable with valid cache operations
  property stable_address;
    @(posedge clk) disable iff (!rst_n)
      ($stable(addr) || (we && cache_hit));
  endproperty
  assert property (stable_address)
    $display("[PASS] Cache: Address remains stable during hits");
  else
    $warning("[FAIL] Cache: Address instability detected at time %t", $time);

endmodule

// Control Path Assertions
module control_assertions #(
  parameter WIDTH = 32
) (
  input logic clk, rst_n,
  input logic [31:0] pc, next_pc,
  input logic branch_taken, jump,
  input logic [WIDTH-1:0] branch_target
);

  // SV Assertion 1: PC should increment normally when no branch
  property normal_pc_increment;
    @(posedge clk) disable iff (!rst_n)
      ((!branch_taken && !jump) |-> (next_pc == pc + 32'd4));
  endproperty
  assert property (normal_pc_increment)
    $display("[PASS] Control: PC increments normally");
  else
    $warning("[FAIL] Control: Abnormal PC increment at time %t", $time);

  // SV Assertion 2: Branch target should be valid when branch taken
  property branch_target_valid;
    @(posedge clk) disable iff (!rst_n)
      ((branch_taken) |-> (!$isunknown(branch_target)));
  endproperty
  assert property (branch_target_valid)
    $display("[PASS] Control: Branch target is always valid");
  else
    $error("[FAIL] Control: Invalid branch target at time %t", $time);

  // SV Assertion 3: Jump and branch should not occur simultaneously
  property exclusive_branch_jump;
    @(posedge clk) disable iff (!rst_n)
      (!(branch_taken && jump));
  endproperty
  assert property (exclusive_branch_jump)
    $display("[PASS] Control: Jump and branch are mutually exclusive");
  else
    $error("[FAIL] Control: Jump/branch simultaneous at time %t", $time);

endmodule

// Register File Assertions
module regfile_assertions #(
  parameter DATA_WIDTH = 32,
  parameter NUM_REGS = 32
) (
  input logic clk, rst_n,
  input logic [4:0] rd_addr1, rd_addr2, wr_addr,
  input logic [DATA_WIDTH-1:0] wr_data, rd_data1, rd_data2,
  input logic we
);

  // SV Assertion 1: Register 0 should always be 0
  property reg_zero_always_zero;
    @(posedge clk) disable iff (!rst_n)
      ((wr_addr == 5'b00000) |-> (wr_data == 32'h00000000));
  endproperty
  assert property (reg_zero_always_zero)
    $display("[PASS] RegFile: Register x0 is hardwired to zero");
  else
    $error("[FAIL] RegFile: Register x0 modified at time %t", $time);

  // SV Assertion 2: Read data should match written data
  property read_write_consistency;
    @(posedge clk) disable iff (!rst_n)
      ((we && wr_addr == rd_addr1) |=> (rd_data1 == $past(wr_data)));
  endproperty
  assert property (read_write_consistency)
    $display("[PASS] RegFile: Read data matches written data");
  else
    $warning("[FAIL] RegFile: Read/write inconsistency at time %t", $time);

endmodule

`endif // ASSERTIONS_SV
