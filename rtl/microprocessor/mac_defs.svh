// mac_defs.svh
`ifndef MAC_DEFS_SVH
`define MAC_DEFS_SVH

// 1. Tamaños base
`define MAC_DATA_WIDTH 32
`define MAC_ACC_WIDTH  72

// 2. Límites Matemáticos (Basados en DATA_WIDTH)
`define MAC_MAX_POS    ((1 << (`MAC_DATA_WIDTH-1)) - 1)
`define MAC_MAX_NEG    (-(1 << (`MAC_DATA_WIDTH-1)))

// 3. Rangos para Cobertura (Bins)
`define MAC_SMALL_POS_LIMIT  1000
`define MAC_SMALL_NEG_LIMIT -1000

`endif