# RISC-V ISA Semantics for Lean

These semantics are generated from the official RISC-V SPEC available at
https://github.com/riscv/sail-riscv/.

⚠️ While this repository covers the full RISC-V SPEC, our Lean backend for sail
is still work-in-progress. As a result, our semantics are still full of warnings
and errors. Similarly, our output is not yet polished for readability.
# RISC-V Lean Statistics

Lines: 76930  
Definitions: 3147  
Inductive definitions: 129  
Abbreviations: 92  

# Warnings and Errors

Errors found: 1261  
Warnings found: 1  

## Error Classes

- 479x application type mismatch
- 81x unknown identifier 'pow2'
- 50x unknown identifier 'print_endline'
- 38x unknown identifier 'shiftl'
- 34x unknown identifier 'shiftr'
- 32x unsolved goals
- 30x type mismatch
- 29x unknown identifier 'sys_enable_fdext'
- 29x could not synthesize default value for parameter 'hmn' using tactics
- 24x unexpected token 'match'; expected ')', ',' or ':'
- 22x unknown identifier 'k_n'
- 22x failed to synthesize
- 20x unknown identifier 'k_m'
- 19x unknown identifier 'sys_enable_zfinx'
- 19x type mismatch, result value has type
- 18x unexpected token 'if'; expected ')', ',' or ':'
- 13x unexpected token '←'; expected ':=' or '|'
- 13x invalid dotted identifier notation, expected type is not of the form (... → C ...) where C is a constant
- 12x unknown identifier 'shift_bits_right'
- 12x unknown identifier 'quot_positive_round_zero'
- 12x unknown identifier 'VLEN'
- 11x unknown identifier 'shift_bits_left'
- 11x don't know how to synthesize placeholder for argument 'α'
- 10x unknown identifier 'slice'
- 9x unknown identifier 'sys_pmp_count'
- 9x unknown identifier 'quot_round_zero'
- 9x unknown identifier 'emod_int'
- 7x cannot lift `(<- ...)` over a binder, this error usually happens when you are trying to lift a method nested in a `fun`, `let`, or `match`-alternative, and it can often be fixed by adding a missing `do`
- 6x unknown identifier 'sys_writable_hpm_counters'
- 6x unknown identifier 'sub_vec'
- 6x unknown identifier 'nzui5'
- 6x unexpected token 'let'; expected 'else'
- 6x invalid use of `(<- ...)`, must be nested inside a 'do' expression
- 6x don't know how to synthesize implicit argument 'n'
- 5x unknown identifier 'early_return'
- 4x unknown identifier 'rsd'
- 4x unknown identifier 'rs2'
- 4x unknown identifier 'print'
- 4x unknown identifier 'parse_hex_bits'
- 4x unexpected token '('; expected ':=', '_', 'rec' or identifier
- 3x unknown identifier 'valid_hex_bits'
- 3x unknown identifier 'sys_pmp_grain'
- 3x unknown identifier 'sys_enable_rvc'
- 3x unknown identifier 'k_o'
- 3x unknown identifier 'hex_str'
- 2x unknown identifier 'sys_enable_vext'
- 2x unknown identifier 'rem_round_zero'
- 2x unknown identifier 'rd'
- 2x unknown identifier 'plat_cache_block_size_exp'
- 2x unknown identifier 'length'
- 2x unknown identifier 'imm17'
- 2x unknown identifier 'imm1612'
- 2x unexpected token ':'; expected ':=' or '←'
- 1x unknown identifier 'sys_vext_vl_use_ceil'
- 1x unknown identifier 'sys_vector_vlen_exp'
- 1x unknown identifier 'sys_vector_elen_exp'
- 1x unknown identifier 'sys_enable_zicboz'
- 1x unknown identifier 'sys_enable_zicbom'
- 1x unknown identifier 'sys_enable_zcb'
- 1x unknown identifier 'sys_enable_writable_misa'
- 1x unknown identifier 'sys_enable_svinval'
- 1x unknown identifier 'sys_enable_sstc'
- 1x unknown identifier 'sys_enable_bext'
- 1x unknown identifier 'speculate_conditional'
- 1x unknown identifier 'plat_term_write'
- 1x unknown identifier 'plat_rom_size'
- 1x unknown identifier 'plat_rom_base'
- 1x unknown identifier 'plat_ram_size'
- 1x unknown identifier 'plat_ram_base'
- 1x unknown identifier 'plat_mtval_has_illegal_inst_bits'
- 1x unknown identifier 'plat_enable_misaligned_access'
- 1x unknown identifier 'plat_clint_size'
- 1x unknown identifier 'plat_clint_base'
- 1x unknown identifier 'k_num_elem_single'
- 1x unknown identifier 'get_slice_int'
- 1x unknown identifier 'get_16_random_bits'
- 1x unknown identifier 'extern_ui64ToF64'
- 1x unknown identifier 'extern_ui64ToF32'
- 1x unknown identifier 'extern_ui64ToF16'
- 1x unknown identifier 'extern_ui32ToF64'
- 1x unknown identifier 'extern_ui32ToF32'
- 1x unknown identifier 'extern_ui32ToF16'
- 1x unknown identifier 'extern_i64ToF64'
- 1x unknown identifier 'extern_i64ToF32'
- 1x unknown identifier 'extern_i64ToF16'
- 1x unknown identifier 'extern_i32ToF64'
- 1x unknown identifier 'extern_i32ToF32'
- 1x unknown identifier 'extern_i32ToF16'
- 1x unknown identifier 'extern_f64roundToInt'
- 1x unknown identifier 'extern_f64ToUi64'
- 1x unknown identifier 'extern_f64ToUi32'
- 1x unknown identifier 'extern_f64ToI64'
- 1x unknown identifier 'extern_f64ToI32'
- 1x unknown identifier 'extern_f64ToF32'
- 1x unknown identifier 'extern_f64ToF16'
- 1x unknown identifier 'extern_f64Sub'
- 1x unknown identifier 'extern_f64Sqrt'
- 1x unknown identifier 'extern_f64MulAdd'
- 1x unknown identifier 'extern_f64Mul'
- 1x unknown identifier 'extern_f64Lt_quiet'
- 1x unknown identifier 'extern_f64Lt'
- 1x unknown identifier 'extern_f64Le_quiet'
- 1x unknown identifier 'extern_f64Le'
- 1x unknown identifier 'extern_f64Eq'
- 1x unknown identifier 'extern_f64Div'
- 1x unknown identifier 'extern_f64Add'
- 1x unknown identifier 'extern_f32roundToInt'
- 1x unknown identifier 'extern_f32ToUi64'
- 1x unknown identifier 'extern_f32ToUi32'
- 1x unknown identifier 'extern_f32ToI64'
- 1x unknown identifier 'extern_f32ToI32'
- 1x unknown identifier 'extern_f32ToF64'
- 1x unknown identifier 'extern_f32ToF16'
- 1x unknown identifier 'extern_f32Sub'
- 1x unknown identifier 'extern_f32Sqrt'
- 1x unknown identifier 'extern_f32MulAdd'
- 1x unknown identifier 'extern_f32Mul'
- 1x unknown identifier 'extern_f32Lt_quiet'
- 1x unknown identifier 'extern_f32Lt'
- 1x unknown identifier 'extern_f32Le_quiet'
- 1x unknown identifier 'extern_f32Le'
- 1x unknown identifier 'extern_f32Eq'
- 1x unknown identifier 'extern_f32Div'
- 1x unknown identifier 'extern_f32Add'
- 1x unknown identifier 'extern_f16roundToInt'
- 1x unknown identifier 'extern_f16ToUi64'
- 1x unknown identifier 'extern_f16ToUi32'
- 1x unknown identifier 'extern_f16ToI64'
- 1x unknown identifier 'extern_f16ToI32'
- 1x unknown identifier 'extern_f16ToF64'
- 1x unknown identifier 'extern_f16ToF32'
- 1x unknown identifier 'extern_f16Sub'
- 1x unknown identifier 'extern_f16Sqrt'
- 1x unknown identifier 'extern_f16MulAdd'
- 1x unknown identifier 'extern_f16Mul'
- 1x unknown identifier 'extern_f16Lt_quiet'
- 1x unknown identifier 'extern_f16Lt'
- 1x unknown identifier 'extern_f16Le_quiet'
- 1x unknown identifier 'extern_f16Le'
- 1x unknown identifier 'extern_f16Eq'
- 1x unknown identifier 'extern_f16Div'
- 1x unknown identifier 'extern_f16Add'
- 1x unknown identifier 'elf_tohost'
- 1x unknown identifier 'cancel_reservation'
- 1x unexpected token 'if'; expected 'else'
- 1x overloaded, errors 
- 1x fail to show termination for
- 1x Lean exited with code 134
