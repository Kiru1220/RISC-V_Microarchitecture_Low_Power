# RISC-V 64-bit In-Order Microarchitecture with Low-Power Design Optimizations

This repository contains a simple, synthesizable, in-order RV64I microarchitecture with a focus on low-power design. It includes RTL, testbenches, and guidance to simulate, analyze, and extend the design.


## 1) Processor Block Diagram (ASCII) and Overview

High-level pipeline and memory subsystem:

```
               +----------------------------- Core ------------------------------+
               |                                                                  |
               |  +--------+    +--------+    +---------+   +--------+  +-------+ |
 PC --> IF --> |  |  IFU   | -> | Decode | -> | Execute |-> | Memory |->| WB    | | -> Regfile
         ^     |  |(Fetch) |    |  (ID)  |    |  (EX)   |   | (MEM)  |  |(WB)   | |
         |     |  +--------+    +--------+    +---------+   +--------+  +-------+ |
         |     |       |              |             |            |          |     |
         |     |       v              v             v            v          v     |
         |     |  Inst Cache --> TLB/I-VA         ALU       Data Cache   RegFile |
         |     |                                                                  |
         |     +------------------------------------------------------------------+
         |                       Branch/Jump redirect (from EX)
         |
         +------------------ Next PC / BTB (optional simple predictor)
```

Explanation:
- IFU fetches instructions via Instruction Cache and ITLB; branch outcomes from EX redirect PC.
- Decode reads the register file, decodes control signals.
- Execute runs ALU ops, computes branch decisions/targets, and effective addresses.
- Memory stage accesses Data Cache through DTLB for loads/stores.
- Writeback stage commits results to the register file.


## 2) Instruction Flow: Step-by-Step (5-stage pipeline)

- Fetch (IF):
  - PC used to request an instruction line from instruction cache; ITLB translates virtual to physical if enabled.
  - Next PC selection: PC+4 by default; on branch/jump resolution (from EX), PC is redirected.
  - Basic stall on I-cache miss; pipeline bubble inserted until fill completes.

- Decode (ID):
  - Instruction decode (RV64I base): opcode, funct3/funct7, rd, rs1, rs2, imm extraction.
  - Register file read: rs1, rs2.
  - Control generation by controller: ALU op, mem read/write, branch type, writeback select.

- Execute (EX):
  - ALU computes arithmetic/logic results and branch condition compare.
  - Branch target = PC + imm; branch taken flag forwarded to IF for redirect.
  - Address generation for load/store: rs1 + imm.

- Memory (MEM):
  - If load/store: access D-cache; DTLB translates VA->PA if enabled.
  - Handles byte/half/word/dword widths and sign extension on loads.
  - Miss handling: wait state until cache line is filled (simple blocking cache model).

- Writeback (WB):
  - Selected result written to rd: ALU result, load data, or PC+4 for JAL/JALR.
  - x0 register hardwired to zero (writes ignored).


## 3) RTL Modules: Description and Purpose

- datapath:
  - Wires the 5-stage pipeline, register file, forwarding (if implemented), and stage registers.
  - Routes control from controller to ALU, memory interface, and writeback muxes.

- controller:
  - Decodes RV64I instructions and drives control signals: ALUControl, MemRead/Write, RegWrite, Branch, ImmType, ResultSrc.
  - Generates stall/flush for hazards on cache misses and branch redirects.

- ALU:
  - Supports add/sub, shifts, boolean ops, set-less-than (signed/unsigned), and compare for branches.
  - Parameterizable width (default 64-bit); zero and sign flags for control.

- cache:
  - Simple direct-mapped (or set-associative, per implementation) instruction and data caches.
  - Interfaces: request/ready, address, wdata, byte-enable, rdata, miss line fill handshake.
  - Supports write-through with write buffer (or write-back if implemented in rtl/cache).

- TLB:
  - Instruction TLB (ITLB) and Data TLB (DTLB) provide VA->PA translation.
  - Simple fully-associative or direct-mapped entries with valid and ASID fields.
  - Can be stubbed off for a purely physical-address build.

- instruction_memory:
  - Backing memory/ROM model for instruction fetch used by I-cache on miss.
  - In simulation, preloaded with a hex/ELF-converted image.

- data_memory:
  - Backing memory model for data accesses used by D-cache on miss.
  - Byte-addressable with per-byte write enable; initializes from a data hex or zeros.

Note: Directory names may include separate files for icache/dcache and itlb/dtlb variants.


## 4) Simulation Workflow

Prerequisites:
- Verilog/SystemVerilog simulator (e.g., Icarus Verilog, Verilator, or Questa/VCS)
- Make or simple shell scripts to compile and run testbenches

Steps:
1. Build the DUT and testbench:
   - Example (Icarus):
     - iverilog -g2012 -o simv rtl/*.v testbenches/top_tb.sv
     - vvp simv
   - Example (Verilator):
     - verilator -cc --exe --build rtl/top.sv testbenches/top_tb.cpp
     - ./obj_dir/Vtop
2. Provide program image to instruction_memory:
   - Use a hex file produced by objcopy (e.g., riscv64-unknown-elf-objcopy -O verilog program.elf program.hex)
   - The testbench loads program.hex into instruction_memory at time 0.
3. Run and observe output:
   - Waveforms: dump.vcd generated by testbench for GTKWave.
   - Console: prints PASS/FAIL signature or final register/memory dumps.
4. Expected output:
   - For unit tests (ALU, branch, load/store): PASS messages when results match reference.
   - For example programs (Fibonacci, matrix multiply): final register x10 contains result; memory signature at a known address matches golden values.

Note: See testbenches/ for specific tb names and run scripts; each tb documents its parameters and memory init files.


## 5) Low-Power Features

- Clock Gating:
  - Fine-grain: Gate pipeline stage enables on stalls (e.g., IF/ID register hold) to prevent redundant toggling.
  - Coarse-grain: Domain-level gating for caches and TLBs when unused (instruction-side idle during data-only loops, etc.).
  - Implementation: Integrated enable signals feeding clock-gating cells (or modeled as clock-enables in RTL for synthesis to infer CG cells).

- Power Gating:
  - Optional retention for register file and architectural state; caches may be flushed prior to power-down.
  - Isolation cells at domain boundaries; wake-up sequence managed by controller FSM.
  - In RTL, modeled via power_down signals that freeze state and force outputs to safe values; synthesis maps to PG cells.

- Data-path optimizations:
  - Operand isolation for ALU inputs when op not used.
  - Multi-Vt cell selection on non-critical paths (synthesis hinting) to reduce leakage.

- Memory hierarchy optimizations:
  - Way shut-down (if set-associative): disable unused ways based on access patterns.
  - Linefill burst length tuned to program locality to reduce unnecessary transfers.


## 6) Glossary

- IF/ID/EX/MEM/WB: Pipeline stages.
- BTB: Branch Target Buffer; predicts next PC for branches.
- TLB: Translation Lookaside Buffer; caches virtual to physical translations.
- CPI: Cycles Per Instruction; performance metric.
- Hazard: Condition requiring stall/forward/flush to preserve correctness.
- Write-through/Write-back: Cache write policies controlling memory update timing.
- Byte-enable: Per-byte write mask used on stores.


## 7) References (IEEE style)

[1] A. Waterman and K. Asanović, The RISC-V Instruction Set Manual, Volume I: User-Level ISA, v2.2, 2019.
[2] J. L. Hennessy and D. A. Patterson, Computer Architecture: A Quantitative Approach, 6th ed., Morgan Kaufmann, 2017.
[3] N. H. E. Weste and D. Harris, CMOS VLSI Design: A Circuits and Systems Perspective, 4th ed., Addison-Wesley, 2010. (Clock/power gating fundamentals)
[4] IEEE Std 1801-2018, IEEE Standard for Design and Verification of Low-Power, Energy-Aware Electronic Systems (UPF), 2018.
[5] D. Kroft, "Lockup-Free Instruction Fetch/Prefetch Cache Organization," ISCA 1981. (Cache miss handling)
[6] M. D. Hill and A. J. Smith, "Evaluating Associativity in CPU Caches," IEEE Trans. Comput., vol. 38, no. 12, 1989.


## 8) Getting Started

- Clone: git clone https://github.com/Kiru1220/RISC-V_Microarchitecture_Low_Power.git
- Explore RTL in rtl/, tests in testbenches/.
- Run a simple test as described in Simulation Workflow.


## 9) Author and License

Author: Usha Kiran H N (ushakiru20@gmail.com)
License: MIT (see LICENSE)

```
Revision history
- v1.1: Expanded README with architecture diagram, pipeline, module docs, simulation, low-power, glossary, references.
```
