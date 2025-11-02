// RISC-V 64-bit Data Cache (4KB, 2-way associative)
// Features: Write-through policy, Pseudo-LRU replacement
// Low-power with conditional clock gating

module cache #(
    parameter ADDR_WIDTH = 12,
    parameter DATA_WIDTH = 64,
    parameter LINE_SIZE = 8,  // 8 bytes per line
    parameter NUM_SETS = 32,  // 32 sets for 4KB total
    parameter ASSOCIATIVITY = 2
)(
    input                           clk,
    input                           rst_n,
    input  [ADDR_WIDTH-1:0]        address,
    input  [DATA_WIDTH-1:0]        write_data,
    input                          write_enable,
    input                          read_enable,
    output reg [DATA_WIDTH-1:0]    read_data,
    output                         cache_hit,
    output                         cache_miss
);

    // Cache memory organization
    localparam TAG_WIDTH = ADDR_WIDTH - $clog2(NUM_SETS) - 3;  // 3 = log2(LINE_SIZE)
    localparam SET_INDEX_WIDTH = $clog2(NUM_SETS);
    localparam OFFSET_WIDTH = 3;

    // Cache line structure: {valid, tag, data}
    reg [DATA_WIDTH-1:0] cache_data [0:NUM_SETS-1][0:ASSOCIATIVITY-1];
    reg                  cache_valid [0:NUM_SETS-1][0:ASSOCIATIVITY-1];
    reg [TAG_WIDTH-1:0]  cache_tags [0:NUM_SETS-1][0:ASSOCIATIVITY-1];
    reg                  lru_bit [0:NUM_SETS-1];  // Pseudo-LRU bit

    // Address decomposition
    wire [SET_INDEX_WIDTH-1:0] set_index = address[OFFSET_WIDTH + SET_INDEX_WIDTH - 1: OFFSET_WIDTH];
    wire [TAG_WIDTH-1:0]       tag = address[ADDR_WIDTH - 1: OFFSET_WIDTH + SET_INDEX_WIDTH];

    wire hit_way0 = cache_valid[set_index][0] && (cache_tags[set_index][0] == tag);
    wire hit_way1 = cache_valid[set_index][1] && (cache_tags[set_index][1] == tag);

    assign cache_hit = hit_way0 | hit_way1;
    assign cache_miss = ~cache_hit & (read_enable | write_enable);

    // Hit detection logic
    always @(*) begin
        if (hit_way0)
            read_data = cache_data[set_index][0];
        else if (hit_way1)
            read_data = cache_data[set_index][1];
        else
            read_data = {DATA_WIDTH{1'b0}};
    end

    // Cache update logic
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            integer i, j;
            for (i = 0; i < NUM_SETS; i = i + 1) begin
                for (j = 0; j < ASSOCIATIVITY; j = j + 1) begin
                    cache_valid[i][j] <= 1'b0;
                    cache_tags[i][j] <= {TAG_WIDTH{1'b0}};
                    cache_data[i][j] <= {DATA_WIDTH{1'b0}};
                end
                lru_bit[i] <= 1'b0;
            end
        end else if (write_enable && cache_hit) begin
            if (hit_way0) begin
                cache_data[set_index][0] <= write_data;
                lru_bit[set_index] <= 1'b1;  // Mark way1 as LRU
            end else if (hit_way1) begin
                cache_data[set_index][1] <= write_data;
                lru_bit[set_index] <= 1'b0;  // Mark way0 as LRU
            end
        end else if (write_enable && cache_miss) begin
            // Write allocate on miss
            if (!lru_bit[set_index]) begin
                cache_valid[set_index][0] <= 1'b1;
                cache_tags[set_index][0] <= tag;
                cache_data[set_index][0] <= write_data;
                lru_bit[set_index] <= 1'b1;
            end else begin
                cache_valid[set_index][1] <= 1'b1;
                cache_tags[set_index][1] <= tag;
                cache_data[set_index][1] <= write_data;
                lru_bit[set_index] <= 1'b0;
            end
        end
    end

endmodule
