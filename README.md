# RISC-V ISA Semantics for Lean

These semantics are generated from the official RISC-V SPEC available at
https://github.com/riscv/sail-riscv/.

⚠️ While this repository covers the full RISC-V SPEC, our Lean backend for sail
is still work-in-progress. As a result, our semantics are still full of warnings
and errors. Similarly, our output is not yet polished for readability.
# RISC-V Lean Statistics

Lines: 75879  
Definitions: 3205  
Inductive definitions: 129  
Abbreviations: 95  

# Warnings and Errors

Errors found: 475  
Warnings found: 1  

## Error Classes

- 83x application type mismatch
- 58x redundant alternative
- 52x function expected at
- 40x unknown identifier 'shiftl'
- 39x unknown identifier 'shiftr'
- 39x type mismatch, result value has type
- 28x failed to synthesize
- 27x unknown identifier 'slice'
- 14x unknown identifier 'shift_bits_right'
- 13x unknown identifier 'get_slice_int'
- 11x unknown identifier 'shift_bits_left'
- 9x unknown identifier 'emod_int'
- 8x don't know how to synthesize placeholder
- 7x don't know how to synthesize placeholder for argument 'α'
- 5x unknown identifier 'print'
- 4x unknown identifier 'parse_hex_bits'
- 4x unknown identifier 'length'
- 4x unknown identifier 'cancel_reservation'
- 3x unknown identifier 'valid_hex_bits'
- 3x unknown identifier 'hex_str'
- 3x unexpected token '←'; expected ':=' or '|'
- 3x invalid `do` notation, expected type is not a monad application
- 2x unknown identifier 'print_bits'
- 2x unknown identifier 'plat_cache_block_size_exp'
- 2x unexpected token 'if'; expected ')', ',' or ':'
- 2x unexpected token '('; expected ':=', '_', 'rec' or identifier
- 1x unknown identifier 'speculate_conditional'
- 1x unknown identifier 'print_string'
- 1x unknown identifier 'match_reservation'
- 1x unknown identifier 'load_reservation'
- 1x unknown identifier 'get_16_random_bits'
- 1x unknown identifier 'cycle_count'
- 1x unexpected token 'while'; expected ')' or term
- 1x type mismatch
- 1x fail to show termination for
- 1x Lean exited with code 1
