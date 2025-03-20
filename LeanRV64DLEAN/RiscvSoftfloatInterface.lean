import LeanRV64DLEAN.RiscvZkrControl

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

noncomputable section

namespace LeanRV64DLEAN.Functions

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
  let t__4470 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4471 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4470, t__4471))

def riscv_f16Sub (rm : (BitVec 3)) (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16Sub rm v1 v2)
  let t__4468 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4469 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4468, t__4469))

def riscv_f16Mul (rm : (BitVec 3)) (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16Mul rm v1 v2)
  let t__4466 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4467 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4466, t__4467))

def riscv_f16Div (rm : (BitVec 3)) (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16Div rm v1 v2)
  let t__4464 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4465 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4464, t__4465))

def riscv_f32Add (rm : (BitVec 3)) (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32Add rm v1 v2)
  let t__4462 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4463 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4462, t__4463))

def riscv_f32Sub (rm : (BitVec 3)) (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32Sub rm v1 v2)
  let t__4460 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4461 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4460, t__4461))

def riscv_f32Mul (rm : (BitVec 3)) (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32Mul rm v1 v2)
  let t__4458 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4459 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4458, t__4459))

def riscv_f32Div (rm : (BitVec 3)) (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32Div rm v1 v2)
  let t__4456 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4457 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4456, t__4457))

def riscv_f64Add (rm : (BitVec 3)) (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64Add rm v1 v2)
  let t__4454 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4454, (← readReg float_result)))

def riscv_f64Sub (rm : (BitVec 3)) (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64Sub rm v1 v2)
  let t__4452 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4452, (← readReg float_result)))

def riscv_f64Mul (rm : (BitVec 3)) (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64Mul rm v1 v2)
  let t__4450 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4450, (← readReg float_result)))

def riscv_f64Div (rm : (BitVec 3)) (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64Div rm v1 v2)
  let t__4448 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4448, (← readReg float_result)))

def riscv_f16MulAdd (rm : (BitVec 3)) (v1 : (BitVec 16)) (v2 : (BitVec 16)) (v3 : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16MulAdd rm v1 v2 v3)
  let t__4446 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4447 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4446, t__4447))

def riscv_f32MulAdd (rm : (BitVec 3)) (v1 : (BitVec 32)) (v2 : (BitVec 32)) (v3 : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32MulAdd rm v1 v2 v3)
  let t__4444 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4445 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4444, t__4445))

def riscv_f64MulAdd (rm : (BitVec 3)) (v1 : (BitVec 64)) (v2 : (BitVec 64)) (v3 : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64MulAdd rm v1 v2 v3)
  let t__4442 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4442, (← readReg float_result)))

def riscv_f16Sqrt (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16Sqrt rm v)
  let t__4440 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4441 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4440, t__4441))

def riscv_f32Sqrt (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32Sqrt rm v)
  let t__4438 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4439 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4438, t__4439))

def riscv_f64Sqrt (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64Sqrt rm v)
  let t__4436 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4436, (← readReg float_result)))

def riscv_f16ToI32 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f16ToI32 rm v)
  let t__4434 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4435 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4434, t__4435))

def riscv_f16ToUi32 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f16ToUi32 rm v)
  let t__4432 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4433 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4432, t__4433))

def riscv_i32ToF16 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_i32ToF16 rm v)
  let t__4430 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4431 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4430, t__4431))

def riscv_ui32ToF16 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_ui32ToF16 rm v)
  let t__4428 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4429 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4428, t__4429))

def riscv_f16ToI64 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f16ToI64 rm v)
  let t__4426 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4426, (← readReg float_result)))

def riscv_f16ToUi64 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f16ToUi64 rm v)
  let t__4424 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4424, (← readReg float_result)))

def riscv_i64ToF16 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_i64ToF16 rm v)
  let t__4422 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4423 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4422, t__4423))

def riscv_ui64ToF16 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_ui64ToF16 rm v)
  let t__4420 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4421 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4420, t__4421))

def riscv_f32ToI32 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32ToI32 rm v)
  let t__4418 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4419 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4418, t__4419))

def riscv_f32ToUi32 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32ToUi32 rm v)
  let t__4416 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4417 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4416, t__4417))

def riscv_i32ToF32 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_i32ToF32 rm v)
  let t__4414 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4415 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4414, t__4415))

def riscv_ui32ToF32 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_ui32ToF32 rm v)
  let t__4412 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4413 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4412, t__4413))

def riscv_f32ToI64 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f32ToI64 rm v)
  let t__4410 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4410, (← readReg float_result)))

def riscv_f32ToUi64 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f32ToUi64 rm v)
  let t__4408 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4408, (← readReg float_result)))

def riscv_i64ToF32 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_i64ToF32 rm v)
  let t__4406 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4407 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4406, t__4407))

def riscv_ui64ToF32 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_ui64ToF32 rm v)
  let t__4404 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4405 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4404, t__4405))

def riscv_f64ToI32 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f64ToI32 rm v)
  let t__4402 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4403 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4402, t__4403))

def riscv_f64ToUi32 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f64ToUi32 rm v)
  let t__4400 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4401 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4400, t__4401))

def riscv_i32ToF64 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_i32ToF64 rm v)
  let t__4398 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4398, (← readReg float_result)))

def riscv_ui32ToF64 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_ui32ToF64 rm v)
  let t__4396 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4396, (← readReg float_result)))

def riscv_f64ToI64 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64ToI64 rm v)
  let t__4394 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4394, (← readReg float_result)))

def riscv_f64ToUi64 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64ToUi64 rm v)
  let t__4392 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4392, (← readReg float_result)))

def riscv_i64ToF64 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_i64ToF64 rm v)
  let t__4390 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4390, (← readReg float_result)))

def riscv_ui64ToF64 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_ui64ToF64 rm v)
  let t__4388 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4388, (← readReg float_result)))

def riscv_f16ToF32 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f16ToF32 rm v)
  let t__4386 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4387 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4386, t__4387))

def riscv_f16ToF64 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f16ToF64 rm v)
  let t__4384 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4384, (← readReg float_result)))

def riscv_f32ToF64 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f32ToF64 rm v)
  let t__4382 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4382, (← readReg float_result)))

def riscv_f32ToF16 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f32ToF16 rm v)
  let t__4380 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4381 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4380, t__4381))

def riscv_f64ToF16 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f64ToF16 rm v)
  let t__4378 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4379 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4378, t__4379))

def riscv_f64ToF32 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f64ToF32 rm v)
  let t__4376 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4377 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4376, t__4377))

def riscv_f16Lt (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f16Lt v1 v2)
  let t__4374 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4375 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4374, t__4375))

def riscv_f16Lt_quiet (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f16Lt_quiet v1 v2)
  let t__4372 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4373 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4372, t__4373))

def riscv_f16Le (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f16Le v1 v2)
  let t__4370 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4371 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4370, t__4371))

def riscv_f16Le_quiet (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f16Le_quiet v1 v2)
  let t__4368 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4369 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4368, t__4369))

def riscv_f16Eq (v1 : (BitVec 16)) (v2 : (BitVec 16)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f16Eq v1 v2)
  let t__4366 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4367 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4366, t__4367))

def riscv_f32Lt (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f32Lt v1 v2)
  let t__4364 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4365 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4364, t__4365))

def riscv_f32Lt_quiet (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f32Lt_quiet v1 v2)
  let t__4362 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4363 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4362, t__4363))

def riscv_f32Le (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f32Le v1 v2)
  let t__4360 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4361 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4360, t__4361))

def riscv_f32Le_quiet (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f32Le_quiet v1 v2)
  let t__4358 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4359 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4358, t__4359))

def riscv_f32Eq (v1 : (BitVec 32)) (v2 : (BitVec 32)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f32Eq v1 v2)
  let t__4356 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4357 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4356, t__4357))

def riscv_f64Lt (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f64Lt v1 v2)
  let t__4354 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4355 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4354, t__4355))

def riscv_f64Lt_quiet (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f64Lt_quiet v1 v2)
  let t__4352 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4353 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4352, t__4353))

def riscv_f64Le (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f64Le v1 v2)
  let t__4350 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4351 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4350, t__4351))

def riscv_f64Le_quiet (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f64Le_quiet v1 v2)
  let t__4348 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4349 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4348, t__4349))

def riscv_f64Eq (v1 : (BitVec 64)) (v2 : (BitVec 64)) : SailM ((BitVec 5) × Bool) := do
  let _ : Unit := (extern_f64Eq v1 v2)
  let t__4346 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4347 ← do (bit_to_bool (BitVec.access (← readReg float_result) 0))
  (pure (t__4346, t__4347))

/-- Type quantifiers: k_ex299816# : Bool -/
def riscv_f16roundToInt (rm : (BitVec 3)) (v : (BitVec 16)) (exact : Bool) : SailM ((BitVec 5) × (BitVec 16)) := do
  let _ : Unit := (extern_f16roundToInt rm v exact)
  let t__4344 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4345 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 15 0))
  (pure (t__4344, t__4345))

/-- Type quantifiers: k_ex299820# : Bool -/
def riscv_f32roundToInt (rm : (BitVec 3)) (v : (BitVec 32)) (exact : Bool) : SailM ((BitVec 5) × (BitVec 32)) := do
  let _ : Unit := (extern_f32roundToInt rm v exact)
  let t__4342 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  let t__4343 ← do (pure (Sail.BitVec.extractLsb (← readReg float_result) 31 0))
  (pure (t__4342, t__4343))

/-- Type quantifiers: k_ex299824# : Bool -/
def riscv_f64roundToInt (rm : (BitVec 3)) (v : (BitVec 64)) (exact : Bool) : SailM ((BitVec 5) × (BitVec 64)) := do
  let _ : Unit := (extern_f64roundToInt rm v exact)
  let t__4340 ← do (pure (Sail.BitVec.extractLsb (← readReg float_fflags) 4 0))
  (pure (t__4340, (← readReg float_result)))

