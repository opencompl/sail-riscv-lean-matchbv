import LeanRV64D.RiscvZkrControl

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

noncomputable section

namespace LeanRV64D.Functions

open zicondop
open wxfunct6
open wvxfunct6
open wvvfunct6
open wvfunct6
open write_kind
open word_width
open wmvxfunct6
open wmvvfunct6
open vxsgfunct6
open vxmsfunct6
open vxmfunct6
open vxmcfunct6
open vxfunct6
open vxcmpfunct6
open vvmsfunct6
open vvmfunct6
open vvmcfunct6
open vvfunct6
open vvcmpfunct6
open vregno
open vregidx
open vmlsop
open vlewidth
open visgfunct6
open virtaddr
open vimsfunct6
open vimfunct6
open vimcfunct6
open vifunct6
open vicmpfunct6
open vfwunary0
open vfunary1
open vfunary0
open vfnunary0
open vext8funct6
open vext4funct6
open vext2funct6
open uop
open sopw
open sop
open seed_opst
open rounding_mode
open ropw
open rop
open rmvvfunct6
open rivvfunct6
open rfvvfunct6
open regno
open regidx
open read_kind
open pmpMatch
open pmpAddrMatch
open physaddr
open option
open nxsfunct6
open nxfunct6
open nvsfunct6
open nvfunct6
open nisfunct6
open nifunct6
open mvxmafunct6
open mvxfunct6
open mvvmafunct6
open mvvfunct6
open mmfunct6
open maskfunct3
open iop
open fwvvmafunct6
open fwvvfunct6
open fwvfunct6
open fwvfmafunct6
open fwvffunct6
open fwffunct6
open fvvmfunct6
open fvvmafunct6
open fvvfunct6
open fvfmfunct6
open fvfmafunct6
open fvffunct6
open fregno
open fregidx
open f_un_x_op_H
open f_un_x_op_D
open f_un_rm_xf_op_S
open f_un_rm_xf_op_H
open f_un_rm_xf_op_D
open f_un_rm_fx_op_S
open f_un_rm_fx_op_H
open f_un_rm_fx_op_D
open f_un_rm_ff_op_S
open f_un_rm_ff_op_H
open f_un_rm_ff_op_D
open f_un_op_x_S
open f_un_op_f_S
open f_un_f_op_H
open f_un_f_op_D
open f_madd_op_S
open f_madd_op_H
open f_madd_op_D
open f_bin_x_op_H
open f_bin_x_op_D
open f_bin_rm_op_S
open f_bin_rm_op_H
open f_bin_rm_op_D
open f_bin_op_x_S
open f_bin_op_f_S
open f_bin_f_op_H
open f_bin_f_op_D
open extop_zbb
open extension
open exception
open ctl_result
open csrop
open cregidx
open checked_cbop
open cbop_zicbom
open cbie
open bropw_zbb
open bropw_zba
open brop_zbs
open brop_zbkb
open brop_zbb
open brop_zba
open bop
open biop_zbs
open barrier_kind
open ast
open amoop
open agtype
open TrapVectorMode
open TR_Result
open SATPMode
open Retired
open Register
open Privilege
open PmpAddrMatchType
open PTW_Result
open PTW_Error
open PTE_Check
open InterruptType
open FetchResult
open Ext_PhysAddr_Check
open Ext_FetchAddr_Check
open Ext_DataAddr_Check
open Ext_ControlAddr_Check
open ExtStatus
open ExceptionType
open Architecture
open AccessType

def riscv_f16Add (rm : (BitVec 3)) (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16Add rm v1 v2)
  let t__4559 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4560 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4559, t__4560))

def riscv_f16Sub (rm : (BitVec 3)) (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16Sub rm v1 v2)
  let t__4557 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4558 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4557, t__4558))

def riscv_f16Mul (rm : (BitVec 3)) (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16Mul rm v1 v2)
  let t__4555 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4556 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4555, t__4556))

def riscv_f16Div (rm : (BitVec 3)) (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16Div rm v1 v2)
  let t__4553 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4554 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4553, t__4554))

def riscv_f32Add (rm : (BitVec 3)) (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32Add rm v1 v2)
  let t__4551 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4552 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4551, t__4552))

def riscv_f32Sub (rm : (BitVec 3)) (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32Sub rm v1 v2)
  let t__4549 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4550 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4549, t__4550))

def riscv_f32Mul (rm : (BitVec 3)) (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32Mul rm v1 v2)
  let t__4547 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4548 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4547, t__4548))

def riscv_f32Div (rm : (BitVec 3)) (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32Div rm v1 v2)
  let t__4545 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4546 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4545, t__4546))

def riscv_f64Add (rm : (BitVec 3)) (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64Add rm v1 v2)
  let t__4543 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4543, (← readReg float_result)))

def riscv_f64Sub (rm : (BitVec 3)) (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64Sub rm v1 v2)
  let t__4541 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4541, (← readReg float_result)))

def riscv_f64Mul (rm : (BitVec 3)) (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64Mul rm v1 v2)
  let t__4539 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4539, (← readReg float_result)))

def riscv_f64Div (rm : (BitVec 3)) (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64Div rm v1 v2)
  let t__4537 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4537, (← readReg float_result)))

def riscv_f16MulAdd (rm : (BitVec 3)) (v1 : (BitVec 16)) (v2 : (BitVec 16)) (v3 : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16MulAdd rm v1 v2 v3)
  let t__4535 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4536 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4535, t__4536))

def riscv_f32MulAdd (rm : (BitVec 3)) (v1 : (BitVec 32)) (v2 : (BitVec 32)) (v3 : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32MulAdd rm v1 v2 v3)
  let t__4533 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4534 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4533, t__4534))

def riscv_f64MulAdd (rm : (BitVec 3)) (v1 : (BitVec 64)) (v2 : (BitVec 64)) (v3 : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64MulAdd rm v1 v2 v3)
  let t__4531 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4531, (← readReg float_result)))

def riscv_f16Sqrt (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16Sqrt rm v)
  let t__4529 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4530 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4529, t__4530))

def riscv_f32Sqrt (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32Sqrt rm v)
  let t__4527 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4528 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4527, t__4528))

def riscv_f64Sqrt (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64Sqrt rm v)
  let t__4525 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4525, (← readReg float_result)))

def riscv_f16ToI32 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f16ToI32 rm v)
  let t__4523 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4524 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4523, t__4524))

def riscv_f16ToUi32 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f16ToUi32 rm v)
  let t__4521 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4522 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4521, t__4522))

def riscv_i32ToF16 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_i32ToF16 rm v)
  let t__4519 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4520 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4519, t__4520))

def riscv_ui32ToF16 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_ui32ToF16 rm v)
  let t__4517 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4518 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4517, t__4518))

def riscv_f16ToI64 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f16ToI64 rm v)
  let t__4515 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4515, (← readReg float_result)))

def riscv_f16ToUi64 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f16ToUi64 rm v)
  let t__4513 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4513, (← readReg float_result)))

def riscv_i64ToF16 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_i64ToF16 rm v)
  let t__4511 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4512 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4511, t__4512))

def riscv_ui64ToF16 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_ui64ToF16 rm v)
  let t__4509 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4510 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4509, t__4510))

def riscv_f32ToI32 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32ToI32 rm v)
  let t__4507 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4508 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4507, t__4508))

def riscv_f32ToUi32 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32ToUi32 rm v)
  let t__4505 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4506 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4505, t__4506))

def riscv_i32ToF32 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_i32ToF32 rm v)
  let t__4503 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4504 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4503, t__4504))

def riscv_ui32ToF32 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_ui32ToF32 rm v)
  let t__4501 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4502 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4501, t__4502))

def riscv_f32ToI64 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f32ToI64 rm v)
  let t__4499 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4499, (← readReg float_result)))

def riscv_f32ToUi64 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f32ToUi64 rm v)
  let t__4497 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4497, (← readReg float_result)))

def riscv_i64ToF32 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_i64ToF32 rm v)
  let t__4495 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4496 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4495, t__4496))

def riscv_ui64ToF32 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_ui64ToF32 rm v)
  let t__4493 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4494 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4493, t__4494))

def riscv_f64ToI32 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f64ToI32 rm v)
  let t__4491 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4492 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4491, t__4492))

def riscv_f64ToUi32 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f64ToUi32 rm v)
  let t__4489 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4490 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4489, t__4490))

def riscv_i32ToF64 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_i32ToF64 rm v)
  let t__4487 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4487, (← readReg float_result)))

def riscv_ui32ToF64 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_ui32ToF64 rm v)
  let t__4485 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4485, (← readReg float_result)))

def riscv_f64ToI64 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64ToI64 rm v)
  let t__4483 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4483, (← readReg float_result)))

def riscv_f64ToUi64 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64ToUi64 rm v)
  let t__4481 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4481, (← readReg float_result)))

def riscv_i64ToF64 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_i64ToF64 rm v)
  let t__4479 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4479, (← readReg float_result)))

def riscv_ui64ToF64 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_ui64ToF64 rm v)
  let t__4477 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4477, (← readReg float_result)))

def riscv_f16ToF32 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f16ToF32 rm v)
  let t__4475 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4476 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4475, t__4476))

def riscv_f16ToF64 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f16ToF64 rm v)
  let t__4473 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4473, (← readReg float_result)))

def riscv_f32ToF64 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f32ToF64 rm v)
  let t__4471 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4471, (← readReg float_result)))

def riscv_f32ToF16 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f32ToF16 rm v)
  let t__4469 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4470 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4469, t__4470))

def riscv_f64ToF16 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f64ToF16 rm v)
  let t__4467 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4468 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4467, t__4468))

def riscv_f64ToF32 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f64ToF32 rm v)
  let t__4465 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4466 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4465, t__4466))

def riscv_f16Lt (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f16Lt v1 v2)
  let t__4463 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4464 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4463, t__4464))

def riscv_f16Lt_quiet (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f16Lt_quiet v1 v2)
  let t__4461 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4462 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4461, t__4462))

def riscv_f16Le (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f16Le v1 v2)
  let t__4459 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4460 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4459, t__4460))

def riscv_f16Le_quiet (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f16Le_quiet v1 v2)
  let t__4457 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4458 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4457, t__4458))

def riscv_f16Eq (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f16Eq v1 v2)
  let t__4455 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4456 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4455, t__4456))

def riscv_f32Lt (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f32Lt v1 v2)
  let t__4453 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4454 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4453, t__4454))

def riscv_f32Lt_quiet (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f32Lt_quiet v1 v2)
  let t__4451 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4452 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4451, t__4452))

def riscv_f32Le (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f32Le v1 v2)
  let t__4449 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4450 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4449, t__4450))

def riscv_f32Le_quiet (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f32Le_quiet v1 v2)
  let t__4447 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4448 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4447, t__4448))

def riscv_f32Eq (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f32Eq v1 v2)
  let t__4445 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4446 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4445, t__4446))

def riscv_f64Lt (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f64Lt v1 v2)
  let t__4443 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4444 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4443, t__4444))

def riscv_f64Lt_quiet (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f64Lt_quiet v1 v2)
  let t__4441 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4442 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4441, t__4442))

def riscv_f64Le (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f64Le v1 v2)
  let t__4439 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4440 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4439, t__4440))

def riscv_f64Le_quiet (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f64Le_quiet v1 v2)
  let t__4437 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4438 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4437, t__4438))

def riscv_f64Eq (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f64Eq v1 v2)
  let t__4435 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4436 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4435, t__4436))

/-- Type quantifiers: k_ex317397# : Bool -/
def riscv_f16roundToInt (rm : (BitVec 3)) (v : (BitVec 16)) (exact : Bool) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16roundToInt rm v exact)
  let t__4433 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4434 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4433, t__4434))

/-- Type quantifiers: k_ex317401# : Bool -/
def riscv_f32roundToInt (rm : (BitVec 3)) (v : (BitVec 32)) (exact : Bool) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32roundToInt rm v exact)
  let t__4431 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4432 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4431, t__4432))

/-- Type quantifiers: k_ex317405# : Bool -/
def riscv_f64roundToInt (rm : (BitVec 3)) (v : (BitVec 64)) (exact : Bool) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64roundToInt rm v exact)
  let t__4429 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4429, (← readReg float_result)))

