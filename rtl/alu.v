// RISC-V 64-bit ALU (Arithmetic Logic Unit)
// Supports all RV64I integer operations
// Low-power implementation with optimized datapath

module alu #(
    parameter WIDTH = 64
)(
    input  [WIDTH-1:0]    operand_a,
    input  [WIDTH-1:0]    operand_b,
    input  [4:0]          alu_control,
    output reg [WIDTH-1:0] result,
    output                 zero_flag
);

    // ALU Control Signals
    parameter ALU_ADD  = 5'b00000;
    parameter ALU_SUB  = 5'b00001;
    parameter ALU_AND  = 5'b00010;
    parameter ALU_OR   = 5'b00011;
    parameter ALU_XOR  = 5'b00100;
    parameter ALU_SLL  = 5'b00101;  // Shift Left Logical
    parameter ALU_SRL  = 5'b00110;  // Shift Right Logical
    parameter ALU_SRA  = 5'b00111;  // Shift Right Arithmetic
    parameter ALU_SLT  = 5'b01000;  // Set if Less Than (signed)
    parameter ALU_SLTU = 5'b01001;  // Set if Less Than Unsigned

    wire [WIDTH-1:0] add_result;
    wire [WIDTH-1:0] sub_result;
    wire [WIDTH-1:0] and_result;
    wire [WIDTH-1:0] or_result;
    wire [WIDTH-1:0] xor_result;
    wire [WIDTH-1:0] sll_result;
    wire [WIDTH-1:0] srl_result;
    wire [WIDTH-1:0] sra_result;
    wire             slt_result;
    wire             sltu_result;

    // Arithmetic Operations
    assign add_result  = operand_a + operand_b;
    assign sub_result  = operand_a - operand_b;

    // Logical Operations
    assign and_result  = operand_a & operand_b;
    assign or_result   = operand_a | operand_b;
    assign xor_result  = operand_a ^ operand_b;

    // Shift Operations
    assign sll_result  = operand_a << operand_b[5:0];
    assign srl_result  = operand_a >> operand_b[5:0];
    assign sra_result  = $signed(operand_a) >>> operand_b[5:0];

    // Comparison Operations
    assign slt_result  = $signed(operand_a) < $signed(operand_b) ? 1'b1 : 1'b0;
    assign sltu_result = operand_a < operand_b ? 1'b1 : 1'b0;

    // Result Multiplexer
    always @(*) begin
        case(alu_control)
            ALU_ADD:  result = add_result;
            ALU_SUB:  result = sub_result;
            ALU_AND:  result = and_result;
            ALU_OR:   result = or_result;
            ALU_XOR:  result = xor_result;
            ALU_SLL:  result = sll_result;
            ALU_SRL:  result = srl_result;
            ALU_SRA:  result = sra_result;
            ALU_SLT:  result = {{(WIDTH-1){1'b0}}, slt_result};
            ALU_SLTU: result = {{(WIDTH-1){1'b0}}, sltu_result};
            default:  result = {WIDTH{1'b0}};
        endcase
    end

    // Zero Flag Output
    assign zero_flag = (result == {WIDTH{1'b0}}) ? 1'b1 : 1'b0;

endmodule
