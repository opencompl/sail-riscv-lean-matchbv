# RISC-V ISA Semantics for Lean

These semantics are generated from the official RISC-V SPEC available at
https://github.com/riscv/sail-riscv/.

⚠️ While this repository covers the full RISC-V SPEC, our Lean backend for sail
is still work-in-progress. As a result, our semantics are still full of warnings
and errors. Similarly, our output is not yet polished for readability.
# RISC-V Lean Statistics

Lines: 74383  
Definitions: 3204  
Inductive definitions: 0  
Abbreviations: 0  

# Warnings and Errors

Errors found: 179  
Warnings found: 0  

## Error Classes

- 52x function expected at
- 39x type mismatch, result value has type
- 37x application type mismatch
- 25x failed to synthesize
- 7x don't know how to synthesize placeholder
- 4x don't know how to synthesize placeholder for argument 'α'
- 3x unexpected token '←'; expected ':=' or '|'
- 3x invalid `do` notation, expected type is not a monad application
- 2x unexpected token 'if'; expected ')', ',' or ':'
- 2x unexpected token '('; expected ':=', '_', 'rec' or identifier
- 2x type mismatch
- 1x unexpected token 'while'; expected ')' or term
- 1x fail to show termination for
- 1x Lean exited with code 1
