# RISC-V ISA Semantics for Lean

These semantics are generated from the official RISC-V SPEC available at
https://github.com/riscv/sail-riscv/.

⚠️ While this repository covers the full RISC-V SPEC, our Lean backend for sail
is still work-in-progress. As a result, our semantics are still full of warnings
and errors. Similarly, our output is not yet polished for readability.
# RISC-V Lean Statistics

Lines: 78138  
Definitions: 3205  
Inductive definitions: 129  
Abbreviations: 95  

# Warnings and Errors

Errors found: 635  
Warnings found: 1  

## Error Classes

- 179x application type mismatch
- 47x unknown identifier 'print_endline'
- 47x function expected at
- 39x failed to synthesize
- 31x unknown identifier 'sys_enable_fdext'
- 29x unsolved goals
- 22x unknown identifier 'sys_enable_zfinx'
- 21x type mismatch, result value has type
- 16x could not synthesize default value for parameter 'hmn' using tactics
- 13x could not synthesize default value for parameter 'hw' using tactics
- 12x unknown identifier 'shiftl'
- 9x unknown identifier 'sys_pmp_count'
- 8x unknown identifier 'emod_int'
- 7x unknown identifier 'sys_writable_hpm_counters'
- 7x unknown identifier 'slice'
- 7x unknown identifier 'shiftr'
- 6x type mismatch
- 6x don't know how to synthesize implicit argument 'n'
- 4x unknown identifier 'shift_bits_right'
- 4x unknown identifier 'parse_hex_bits'
- 3x unknown identifier 'valid_hex_bits'
- 3x unknown identifier 'sys_pmp_grain'
- 3x unknown identifier 'sys_enable_rvc'
- 3x unknown identifier 'plat_clint_base'
- 3x unknown identifier 'hex_str'
- 3x invalid `do` notation, expected type is not a monad application
- 2x unknown identifier 'sys_enable_writable_fiom'
- 2x unknown identifier 'sys_enable_vext'
- 2x unknown identifier 'shift_bits_left'
- 2x unknown identifier 'print'
- 2x unknown identifier 'plat_enable_dirty_update'
- 2x unknown identifier 'length'
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
- 1x unknown identifier 'plat_term_write'
- 1x unknown identifier 'plat_rom_size'
- 1x unknown identifier 'plat_rom_base'
- 1x unknown identifier 'plat_ram_size'
- 1x unknown identifier 'plat_ram_base'
- 1x unknown identifier 'plat_mtval_has_illegal_inst_bits'
- 1x unknown identifier 'plat_enable_misaligned_access'
- 1x unknown identifier 'plat_clint_size'
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
- 1x fail to show termination for
- 1x Lean exited with code 134
