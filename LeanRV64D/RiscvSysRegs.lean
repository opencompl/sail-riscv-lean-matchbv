import LeanRV64D.RiscvPcAccess

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

noncomputable section

namespace LeanRV64D.Functions

open zvkfunct6
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
open Step
open SATPMode
open Register
open Privilege
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open InterruptType
open HartState
open FetchResult
open Ext_PhysAddr_Check
open Ext_FetchAddr_Check
open Ext_DataAddr_Check
open Ext_ControlAddr_Check
open ExtStatus
open ExecutionResult
open ExceptionType
open Architecture
open AccessType

def undefined_Misa (_ : Unit) : SailM (BitVec (2 ^ 3 * 8)) := do
  (undefined_bitvector ((2 ^i 3) *i 8))

def Mk_Misa (v : (BitVec 64)) : (BitVec (2 ^ 3 * 8)) :=
  v

def _get_Misa_bits (v : (BitVec (2 ^ 3 * 8))) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (((2 ^i 3) *i 8) -i 1) 0)

def _update_Misa_bits (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 64)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v (((2 ^i 3) *i 8) -i 1) 0 x)

def _update_CountSmcntrpmf_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Counteren_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_Counterin_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_Fcsr_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_HpmEvent_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MEnvcfg_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Mcause_bits (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 64)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v (((2 ^i 3) *i 8) -i 1) 0 x)

def _update_Medeleg_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Minterrupts_bits (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 64)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v (((2 ^i 3) *i 8) -i 1) 0 x)

def _update_Mstatus_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Mtvec_bits (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 64)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v (((2 ^i 3) *i 8) -i 1) 0 x)

def _update_PTE_Ext_bits (v : (BitVec 10)) (x : (BitVec 10)) : (BitVec 10) :=
  (Sail.BitVec.updateSubrange v (10 -i 1) 0 x)

def _update_PTE_Flags_bits (v : (BitVec 8)) (x : (BitVec 8)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v (8 -i 1) 0 x)

def _update_Pmpcfg_ent_bits (v : (BitVec 8)) (x : (BitVec 8)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v (8 -i 1) 0 x)

def _update_SEnvcfg_bits (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 64)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v (((2 ^i 3) *i 8) -i 1) 0 x)

def _update_Satp32_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_Satp64_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Sinterrupts_bits (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 64)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v (((2 ^i 3) *i 8) -i 1) 0 x)

def _update_Sstatus_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_Vcsr_bits (v : (BitVec 3)) (x : (BitVec 3)) : (BitVec 3) :=
  (Sail.BitVec.updateSubrange v (3 -i 1) 0 x)

def _update_Vtype_bits (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 64)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v (((2 ^i 3) *i 8) -i 1) 0 x)

def _update_htif_cmd_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _set_Misa_bits (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_bits r v)

def _get_CountSmcntrpmf_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Counteren_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_Counterin_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_Fcsr_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_HpmEvent_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MEnvcfg_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Mcause_bits (v : (BitVec (2 ^ 3 * 8))) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (((2 ^i 3) *i 8) -i 1) 0)

def _get_Medeleg_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Minterrupts_bits (v : (BitVec (2 ^ 3 * 8))) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (((2 ^i 3) *i 8) -i 1) 0)

def _get_Mstatus_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Mtvec_bits (v : (BitVec (2 ^ 3 * 8))) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (((2 ^i 3) *i 8) -i 1) 0)

def _get_PTE_Ext_bits (v : (BitVec 10)) : (BitVec 10) :=
  (Sail.BitVec.extractLsb v (10 -i 1) 0)

def _get_PTE_Flags_bits (v : (BitVec 8)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v (8 -i 1) 0)

def _get_Pmpcfg_ent_bits (v : (BitVec 8)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v (8 -i 1) 0)

def _get_SEnvcfg_bits (v : (BitVec (2 ^ 3 * 8))) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (((2 ^i 3) *i 8) -i 1) 0)

def _get_Satp32_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_Satp64_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Sinterrupts_bits (v : (BitVec (2 ^ 3 * 8))) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (((2 ^i 3) *i 8) -i 1) 0)

def _get_Sstatus_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Vcsr_bits (v : (BitVec 3)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v (3 -i 1) 0)

def _get_Vtype_bits (v : (BitVec (2 ^ 3 * 8))) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (((2 ^i 3) *i 8) -i 1) 0)

def _get_htif_cmd_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _set_CountSmcntrpmf_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CountSmcntrpmf_bits r v)

def _set_Counteren_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counteren_bits r v)

def _set_Counterin_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counterin_bits r v)

def _set_Fcsr_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Fcsr_bits r v)

def _set_HpmEvent_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HpmEvent_bits r v)

def _set_MEnvcfg_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_bits r v)

def _set_Mcause_bits (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mcause_bits r v)

def _set_Medeleg_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_bits r v)

def _set_Minterrupts_bits (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Minterrupts_bits r v)

def _set_Mstatus_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_bits r v)

def _set_Mtvec_bits (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mtvec_bits r v)

def _set_PTE_Ext_bits (r_ref : (RegisterRef (BitVec 10))) (v : (BitVec 10)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Ext_bits r v)

def _set_PTE_Flags_bits (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_bits r v)

def _set_Pmpcfg_ent_bits (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Pmpcfg_ent_bits r v)

def _set_SEnvcfg_bits (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_bits r v)

def _set_Satp32_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp32_bits r v)

def _set_Satp64_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp64_bits r v)

def _set_Sinterrupts_bits (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sinterrupts_bits r v)

def _set_Sstatus_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_bits r v)

def _set_Vcsr_bits (r_ref : (RegisterRef (BitVec 3))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Vcsr_bits r v)

def _set_Vtype_bits (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Vtype_bits r v)

def _set_htif_cmd_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_htif_cmd_bits r v)

def _get_Misa_A (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_Misa_A (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PTE_Flags_A (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_Pmpcfg_ent_A (v : (BitVec 8)) (x : (BitVec 2)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 4 3 x)

def _set_Misa_A (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_A r v)

def _get_PTE_Flags_A (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_Pmpcfg_ent_A (v : (BitVec 8)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 4 3)

def _set_PTE_Flags_A (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_A r v)

def _set_Pmpcfg_ent_A (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Pmpcfg_ent_A r v)

def _get_Misa_B (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_Misa_B (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _set_Misa_B (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_B r v)

def _get_Misa_C (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_Misa_C (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _set_Misa_C (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_C r v)

def _get_Misa_D (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_Misa_D (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PTE_Flags_D (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Misa_D (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_D r v)

def _get_PTE_Flags_D (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _set_PTE_Flags_D (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_D r v)

def _get_Misa_E (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_Misa_E (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _set_Misa_E (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_E r v)

def _get_Misa_F (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_Misa_F (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _set_Misa_F (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_F r v)

def _get_Misa_G (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_Misa_G (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PTE_Flags_G (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _set_Misa_G (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_G r v)

def _get_PTE_Flags_G (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _set_PTE_Flags_G (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_G r v)

def _get_Misa_H (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_Misa_H (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Misa_H (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_H r v)

def _get_Misa_I (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_Misa_I (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _set_Misa_I (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_I r v)

def _get_Misa_J (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_Misa_J (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _set_Misa_J (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_J r v)

def _get_Misa_K (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_Misa_K (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _set_Misa_K (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_K r v)

def _get_Misa_L (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_Misa_L (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_Pmpcfg_ent_L (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Misa_L (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_L r v)

def _get_Pmpcfg_ent_L (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _set_Pmpcfg_ent_L (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Pmpcfg_ent_L r v)

def _get_Misa_M (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_Misa_M (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _set_Misa_M (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_M r v)

def _get_Misa_MXL (v : (BitVec (2 ^ 3 * 8))) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v (((2 ^i 3) *i 8) -i 1) (((2 ^i 3) *i 8) -i 2))

def _update_Misa_MXL (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 2)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v (((2 ^i 3) *i 8) -i 1) (((2 ^i 3) *i 8) -i 2) x)

def _set_Misa_MXL (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_MXL r v)

def _get_Misa_N (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_Misa_N (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PTE_Ext_N (v : (BitVec 10)) (x : (BitVec 1)) : (BitVec 10) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _set_Misa_N (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_N r v)

def _get_PTE_Ext_N (v : (BitVec 10)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _set_PTE_Ext_N (r_ref : (RegisterRef (BitVec 10))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Ext_N r v)

def _get_Misa_O (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_Misa_O (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _set_Misa_O (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_O r v)

def _get_Misa_P (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_Misa_P (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _set_Misa_P (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_P r v)

def _get_Misa_Q (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_Misa_Q (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _set_Misa_Q (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_Q r v)

def _get_Misa_R (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_Misa_R (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PTE_Flags_R (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_Pmpcfg_ent_R (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _set_Misa_R (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_R r v)

def _get_PTE_Flags_R (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_Pmpcfg_ent_R (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _set_PTE_Flags_R (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_R r v)

def _set_Pmpcfg_ent_R (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Pmpcfg_ent_R r v)

def _get_Misa_S (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_Misa_S (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _set_Misa_S (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_S r v)

def _get_Misa_T (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_Misa_T (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _set_Misa_T (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_T r v)

def _get_Misa_U (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_Misa_U (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PTE_Flags_U (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _set_Misa_U (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_U r v)

def _get_PTE_Flags_U (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _set_PTE_Flags_U (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_U r v)

def _get_Misa_V (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_Misa_V (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PTE_Flags_V (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _set_Misa_V (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_V r v)

def _get_PTE_Flags_V (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _set_PTE_Flags_V (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_V r v)

def _get_Misa_W (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_Misa_W (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PTE_Flags_W (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_Pmpcfg_ent_W (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _set_Misa_W (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_W r v)

def _get_PTE_Flags_W (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_Pmpcfg_ent_W (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _set_PTE_Flags_W (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_W r v)

def _set_Pmpcfg_ent_W (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Pmpcfg_ent_W r v)

def _get_Misa_X (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_Misa_X (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PTE_Flags_X (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_Pmpcfg_ent_X (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _set_Misa_X (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_X r v)

def _get_PTE_Flags_X (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_Pmpcfg_ent_X (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _set_PTE_Flags_X (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Flags_X r v)

def _set_Pmpcfg_ent_X (r_ref : (RegisterRef (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Pmpcfg_ent_X r v)

def _get_Misa_Y (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_Misa_Y (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _set_Misa_Y (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_Y r v)

def _get_Misa_Z (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_Misa_Z (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _set_Misa_Z (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Misa_Z r v)

def sys_enable_writable_misa (_ : Unit) : Bool :=
  true

def sys_enable_writable_fiom (_ : Unit) : Bool :=
  true

def sys_pmp_count (_ : Unit) : Int :=
  16

def sys_pmp_grain (_ : Unit) : Nat :=
  0

def sys_writable_hpm_counters (_ : Unit) : (BitVec 32) :=
  (0xFFFFFFFF : (BitVec 32))

def ext_veto_disable_C (_ : Unit) : Bool :=
  false

def legalize_misa (m : (BitVec (2 ^ 3 * 8))) (v : (BitVec (2 ^ 3 * 8))) : SailM (BitVec (2 ^ 3 * 8)) := do
  let v := (Mk_Misa v)
  bif ((not (sys_enable_writable_misa ())) || (((_get_Misa_C v) == (0b0 : (BitVec 1))) && (((BitVec.access
               (← readReg nextPC) 1) == 1#1) || (ext_veto_disable_C ()))))
  then (pure m)
  else
    (pure (_update_Misa_V
        (_update_Misa_U
          (_update_Misa_S
            (_update_Misa_M
              (_update_Misa_I
                (_update_Misa_F
                  (_update_Misa_D
                    (_update_Misa_C
                      (_update_Misa_B
                        (_update_Misa_A m
                          (bif (hartSupports Ext_A)
                          then (_get_Misa_A v)
                          else (0b0 : (BitVec 1))))
                        (bif (hartSupports Ext_B)
                        then (_get_Misa_B v)
                        else (0b0 : (BitVec 1))))
                      (bif (hartSupports Ext_C)
                      then (_get_Misa_C v)
                      else (0b0 : (BitVec 1))))
                    (bif ((hartSupports Ext_D) && ((_get_Misa_F v) == (0b1 : (BitVec 1))))
                    then (_get_Misa_D v)
                    else (0b0 : (BitVec 1))))
                  (bif (hartSupports Ext_F)
                  then (_get_Misa_F v)
                  else (0b0 : (BitVec 1)))) (0b1 : (BitVec 1)))
              (bif (hartSupports Ext_M)
              then (_get_Misa_M v)
              else (0b0 : (BitVec 1))))
            (bif ((hartSupports Ext_S) && ((_get_Misa_U v) == (0b1 : (BitVec 1))))
            then (_get_Misa_S v)
            else (0b0 : (BitVec 1))))
          (bif (hartSupports Ext_U)
          then (_get_Misa_U v)
          else (0b0 : (BitVec 1))))
        (bif ((hartSupports Ext_V) && (((_get_Misa_F v) == (0b1 : (BitVec 1))) && ((_get_Misa_D v) == (0b1 : (BitVec 1)))))
        then (_get_Misa_V v)
        else (0b0 : (BitVec 1)))))

def Mk_Mstatus (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_Mstatus_SXL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 34 x)

def _update_Mstatus_UXL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def _get_Mstatus_FS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 14 13)

def _get_Mstatus_VS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 10 9)

def currentlyEnabled_measure (ext : extension) : Int :=
  match ext with
  | Ext_A => 0
  | Ext_B => 0
  | Ext_C => 0
  | Ext_D => 0
  | Ext_F => 0
  | Ext_M => 0
  | Ext_S => 0
  | Ext_V => 0
  | Ext_Smcntrpmf => 2
  | Ext_Zabha => 2
  | Ext_Zcb => 2
  | Ext_Zcd => 2
  | Ext_Zcf => 2
  | Ext_Zcmop => 2
  | Ext_Zfhmin => 2
  | Ext_Zhinx => 2
  | Ext_Zihpm => 2
  | Ext_Zvkb => 2
  | Ext_Sscofpmf => 3
  | _ => 1

def currentlyEnabled (merge_var : extension) : SailM Bool := do
  match merge_var with
  | Ext_Sstc => (pure (hartSupports Ext_Sstc))
  | Ext_U =>
    (pure ((hartSupports Ext_U) && ((_get_Misa_U (← readReg misa)) == (0b1 : (BitVec 1)))))
  | Ext_S =>
    (pure ((hartSupports Ext_S) && ((_get_Misa_S (← readReg misa)) == (0b1 : (BitVec 1)))))
  | Ext_Svbare => (currentlyEnabled Ext_S)
  | Ext_Sv32 => (pure ((hartSupports Ext_Sv32) && (← (currentlyEnabled Ext_S))))
  | Ext_Sv39 => (pure ((hartSupports Ext_Sv39) && (← (currentlyEnabled Ext_S))))
  | Ext_Sv48 => (pure ((hartSupports Ext_Sv48) && (← (currentlyEnabled Ext_S))))
  | Ext_Sv57 => (pure ((hartSupports Ext_Sv57) && (← (currentlyEnabled Ext_S))))
  | Ext_V =>
    (pure ((hartSupports Ext_V) && (((_get_Misa_V (← readReg misa)) == (0b1 : (BitVec 1))) && ((_get_Mstatus_VS
              (← readReg mstatus)) != (0b00 : (BitVec 2))))))
  | Ext_Zihpm => (pure ((hartSupports Ext_Zihpm) && (← (currentlyEnabled Ext_Zicntr))))
  | Ext_Sscofpmf => (pure ((hartSupports Ext_Sscofpmf) && (← (currentlyEnabled Ext_Zihpm))))
  | Ext_Zkr => (pure (hartSupports Ext_Zkr))
  | Ext_Zicntr => (pure (hartSupports Ext_Zicntr))
  | Ext_F =>
    (pure ((hartSupports Ext_F) && (((_get_Misa_F (← readReg misa)) == (0b1 : (BitVec 1))) && ((_get_Mstatus_FS
              (← readReg mstatus)) != (0b00 : (BitVec 2))))))
  | Ext_D =>
    (pure ((hartSupports Ext_D) && (((_get_Misa_D (← readReg misa)) == (0b1 : (BitVec 1))) && (((_get_Mstatus_FS
                (← readReg mstatus)) != (0b00 : (BitVec 2))) && (flen ≥b 64)))))
  | Ext_Zfinx => (pure (hartSupports Ext_Zfinx))
  | Ext_Smcntrpmf => (pure ((hartSupports Ext_Smcntrpmf) && (← (currentlyEnabled Ext_Zicntr))))
  | Ext_Svnapot => (pure false)
  | Ext_Svpbmt => (pure false)
  | Ext_C =>
    (pure ((hartSupports Ext_C) && ((_get_Misa_C (← readReg misa)) == (0b1 : (BitVec 1)))))
  | Ext_Zca =>
    (pure ((hartSupports Ext_Zca) && ((← (currentlyEnabled Ext_C)) || (not (hartSupports Ext_C)))))
  | Ext_Zifencei => (pure (hartSupports Ext_Zifencei))
  | Ext_A =>
    (pure ((hartSupports Ext_A) && ((_get_Misa_A (← readReg misa)) == (0b1 : (BitVec 1)))))
  | Ext_Zabha => (pure ((hartSupports Ext_Zabha) && (← (currentlyEnabled Ext_Zaamo))))
  | Ext_Zalrsc => (pure ((hartSupports Ext_Zalrsc) || (← (currentlyEnabled Ext_A))))
  | Ext_Zaamo => (pure ((hartSupports Ext_Zaamo) || (← (currentlyEnabled Ext_A))))
  | Ext_M =>
    (pure ((hartSupports Ext_M) && ((_get_Misa_M (← readReg misa)) == (0b1 : (BitVec 1)))))
  | Ext_Zmmul => (pure ((hartSupports Ext_Zmmul) || (← (currentlyEnabled Ext_M))))
  | Ext_Zfh => (pure ((hartSupports Ext_Zfh) && (← (currentlyEnabled Ext_F))))
  | Ext_Zfhmin =>
    (pure (((hartSupports Ext_Zfhmin) && (← (currentlyEnabled Ext_F))) || (← (currentlyEnabled
            Ext_Zfh))))
  | Ext_Zcf =>
    (pure ((hartSupports Ext_Zcf) && ((← (currentlyEnabled Ext_F)) && ((← (currentlyEnabled
                Ext_Zca)) && ((← (currentlyEnabled Ext_C)) || (not (hartSupports Ext_C)))))))
  | Ext_Zdinx => (pure ((hartSupports Ext_Zdinx) && (flen ≥b 64)))
  | Ext_Zcd =>
    (pure ((hartSupports Ext_Zcd) && ((← (currentlyEnabled Ext_D)) && ((← (currentlyEnabled
                Ext_Zca)) && ((← (currentlyEnabled Ext_C)) || (not (hartSupports Ext_C)))))))
  | Ext_Svinval => (pure (hartSupports Ext_Svinval))
  | Ext_B =>
    (pure ((hartSupports Ext_B) && ((_get_Misa_B (← readReg misa)) == (0b1 : (BitVec 1)))))
  | Ext_Zba => (pure ((hartSupports Ext_Zba) || (← (currentlyEnabled Ext_B))))
  | Ext_Zbb => (pure ((hartSupports Ext_Zbb) || (← (currentlyEnabled Ext_B))))
  | Ext_Zbkb => (pure (hartSupports Ext_Zbkb))
  | Ext_Zbc => (pure (hartSupports Ext_Zbc))
  | Ext_Zbkc => (pure (hartSupports Ext_Zbkc))
  | Ext_Zbs => (pure ((hartSupports Ext_Zbs) || (← (currentlyEnabled Ext_B))))
  | Ext_Zcb => (pure ((hartSupports Ext_Zcb) && (← (currentlyEnabled Ext_Zca))))
  | Ext_Zhinx => (pure ((hartSupports Ext_Zhinx) && (← (currentlyEnabled Ext_Zfinx))))
  | Ext_Zfa => (pure ((hartSupports Ext_Zfa) && (← (currentlyEnabled Ext_F))))
  | Ext_Zknh => (pure (hartSupports Ext_Zknh))
  | Ext_Zkne => (pure (hartSupports Ext_Zkne))
  | Ext_Zknd => (pure (hartSupports Ext_Zknd))
  | Ext_Zksh => (pure (hartSupports Ext_Zksh))
  | Ext_Zksed => (pure (hartSupports Ext_Zksed))
  | Ext_Zbkx => (pure (hartSupports Ext_Zbkx))
  | Ext_Zicond => (pure (hartSupports Ext_Zicond))
  | Ext_Zicbom => (pure (hartSupports Ext_Zicbom))
  | Ext_Zicboz => (pure (hartSupports Ext_Zicboz))
  | Ext_Zvbb => (pure ((hartSupports Ext_Zvbb) && (← (currentlyEnabled Ext_V))))
  | Ext_Zvkb =>
    (pure (((hartSupports Ext_Zvkb) || (← (currentlyEnabled Ext_Zvbb))) && (← (currentlyEnabled
            Ext_V))))
  | Ext_Zvbc => (pure ((hartSupports Ext_Zvbc) && (← (currentlyEnabled Ext_V))))
  | Ext_Zvknha => (pure ((hartSupports Ext_Zvknha) && (← (currentlyEnabled Ext_V))))
  | Ext_Zvknhb => (pure ((hartSupports Ext_Zvknhb) && (← (currentlyEnabled Ext_V))))
  | Ext_Zvksh => (pure ((hartSupports Ext_Zvksh) && (← (currentlyEnabled Ext_V))))
  | Ext_Zimop => (pure (hartSupports Ext_Zimop))
  | Ext_Zcmop => (pure ((hartSupports Ext_Zcmop) && (← (currentlyEnabled Ext_Zca))))
termination_by let ext := merge_var; ((currentlyEnabled_measure ext)).toNat

def virtual_memory_supported (_ : Unit) : SailM Bool := do
  (pure ((← (currentlyEnabled Ext_Sv32)) || ((← (currentlyEnabled Ext_Sv39)) || ((← (currentlyEnabled
              Ext_Sv48)) || (← (currentlyEnabled Ext_Sv57))))))

def lowest_supported_privLevel (_ : Unit) : SailM Privilege := do
  bif (← (currentlyEnabled Ext_U))
  then (pure User)
  else (pure Machine)

def have_privLevel (priv : (BitVec 2)) : SailM Bool := do
  match_bv priv with
  | 00 => do (currentlyEnabled Ext_U)
  | 01 => do (currentlyEnabled Ext_S)
  | 10 => do (pure false)
  | _ => do (pure true)

def undefined_Mstatus (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _update_Mstatus_FS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 13 x)

def _update_Sstatus_FS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 13 x)

def _set_Mstatus_FS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_FS r v)

def _get_Sstatus_FS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 14 13)

def _set_Sstatus_FS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_FS r v)

def _get_Mstatus_MBE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)

def _update_Mstatus_MBE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _set_Mstatus_MBE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MBE r v)

def _get_Mstatus_MIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_Mstatus_MIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _set_Mstatus_MIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MIE r v)

def _get_Mstatus_MPIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_Mstatus_MPIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Mstatus_MPIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MPIE r v)

def _get_Mstatus_MPP (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 12 11)

def _update_Mstatus_MPP (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 11 x)

def _set_Mstatus_MPP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MPP r v)

def _get_Mstatus_MPRV (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_Mstatus_MPRV (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _set_Mstatus_MPRV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MPRV r v)

def _get_Mstatus_MXR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_Mstatus_MXR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_Sstatus_MXR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _set_Mstatus_MXR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_MXR r v)

def _get_Sstatus_MXR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _set_Sstatus_MXR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_MXR r v)

def _get_Mstatus_SBE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)

def _update_Mstatus_SBE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _set_Mstatus_SBE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SBE r v)

def _get_Mstatus_SD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v (((2 ^i 3) *i 8) -i 1) (((2 ^i 3) *i 8) -i 1))

def _update_Mstatus_SD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (((2 ^i 3) *i 8) -i 1) (((2 ^i 3) *i 8) -i 1) x)

def _update_Sstatus_SD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (((2 ^i 3) *i 8) -i 1) (((2 ^i 3) *i 8) -i 1) x)

def _set_Mstatus_SD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SD r v)

def _get_Sstatus_SD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v (((2 ^i 3) *i 8) -i 1) (((2 ^i 3) *i 8) -i 1))

def _set_Sstatus_SD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_SD r v)

def _get_Mstatus_SIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_Mstatus_SIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_Sstatus_SIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _set_Mstatus_SIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SIE r v)

def _get_Sstatus_SIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _set_Sstatus_SIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_SIE r v)

def _get_Mstatus_SPIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_Mstatus_SPIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_Sstatus_SPIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _set_Mstatus_SPIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SPIE r v)

def _get_Sstatus_SPIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _set_Sstatus_SPIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_SPIE r v)

def _get_Mstatus_SPP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_Mstatus_SPP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_Sstatus_SPP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _set_Mstatus_SPP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SPP r v)

def _get_Sstatus_SPP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _set_Sstatus_SPP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_SPP r v)

def _get_Mstatus_SUM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_Mstatus_SUM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_Sstatus_SUM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _set_Mstatus_SUM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SUM r v)

def _get_Sstatus_SUM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _set_Sstatus_SUM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_SUM r v)

def _get_Mstatus_SXL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 35 34)

def _set_Mstatus_SXL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_SXL r v)

def _get_Mstatus_TSR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_Mstatus_TSR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _set_Mstatus_TSR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_TSR r v)

def _get_Mstatus_TVM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_Mstatus_TVM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _set_Mstatus_TVM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_TVM r v)

def _get_Mstatus_TW (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_Mstatus_TW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _set_Mstatus_TW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_TW r v)

def _get_Mstatus_UXL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)

def _update_Sstatus_UXL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def _set_Mstatus_UXL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_UXL r v)

def _get_Sstatus_UXL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)

def _set_Sstatus_UXL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_UXL r v)

def _update_Mstatus_VS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 9 x)

def _update_Sstatus_VS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 9 x)

def _set_Mstatus_VS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_VS r v)

def _get_Sstatus_VS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 10 9)

def _set_Sstatus_VS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_VS r v)

def _get_Mstatus_XS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 16 15)

def _update_Mstatus_XS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 15 x)

def _update_Sstatus_XS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 15 x)

def _set_Mstatus_XS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mstatus_XS r v)

def _get_Sstatus_XS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 16 15)

def _set_Sstatus_XS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sstatus_XS r v)

def effectivePrivilege (t : (AccessType Unit)) (m : (BitVec 64)) (priv : Privilege) : SailM Privilege := do
  bif ((bne t (InstructionFetch ())) && ((_get_Mstatus_MPRV m) == (0b1 : (BitVec 1))))
  then (privLevel_of_bits (_get_Mstatus_MPP m))
  else (pure priv)

def get_mstatus_SXL (m : (BitVec 64)) : (BitVec 2) :=
  (_get_Mstatus_SXL m)

def get_mstatus_UXL (m : (BitVec 64)) : (BitVec 2) :=
  (_get_Mstatus_UXL m)

def legalize_mstatus (o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_Mstatus v)
  let o ← do
    (pure (_update_Mstatus_SIE
        (_update_Mstatus_MIE
          (_update_Mstatus_SPIE
            (_update_Mstatus_MPIE
              (_update_Mstatus_VS
                (_update_Mstatus_SPP
                  (_update_Mstatus_MPP
                    (_update_Mstatus_FS
                      (_update_Mstatus_XS
                        (_update_Mstatus_MPRV
                          (_update_Mstatus_SUM
                            (_update_Mstatus_MXR
                              (_update_Mstatus_TVM
                                (_update_Mstatus_TW
                                  (_update_Mstatus_TSR o
                                    (← do
                                      bif (← (currentlyEnabled Ext_S))
                                      then (pure (_get_Mstatus_TSR v))
                                      else (pure (0b0 : (BitVec 1)))))
                                  (← do
                                    bif (← (currentlyEnabled Ext_U))
                                    then (pure (_get_Mstatus_TW v))
                                    else (pure (0b0 : (BitVec 1)))))
                                (← do
                                  bif (← (currentlyEnabled Ext_S))
                                  then (pure (_get_Mstatus_TVM v))
                                  else (pure (0b0 : (BitVec 1)))))
                              (← do
                                bif (← (currentlyEnabled Ext_S))
                                then (pure (_get_Mstatus_MXR v))
                                else (pure (0b0 : (BitVec 1)))))
                            (← do
                              bif (← (virtual_memory_supported ()))
                              then (pure (_get_Mstatus_SUM v))
                              else (pure (0b0 : (BitVec 1)))))
                          (← do
                            bif (← (currentlyEnabled Ext_U))
                            then (pure (_get_Mstatus_MPRV v))
                            else (pure (0b0 : (BitVec 1))))) (extStatus_to_bits Off))
                      (bif (hartSupports Ext_Zfinx)
                      then (extStatus_to_bits Off)
                      else (_get_Mstatus_FS v)))
                    (← do
                      bif (← (have_privLevel (_get_Mstatus_MPP v)))
                      then (pure (_get_Mstatus_MPP v))
                      else (pure (privLevel_to_bits (← (lowest_supported_privLevel ()))))))
                  (← do
                    bif (← (currentlyEnabled Ext_S))
                    then (pure (_get_Mstatus_SPP v))
                    else (pure (0b0 : (BitVec 1))))) (_get_Mstatus_VS v)) (_get_Mstatus_MPIE v))
            (← do
              bif (← (currentlyEnabled Ext_S))
              then (pure (_get_Mstatus_SPIE v))
              else (pure (0b0 : (BitVec 1))))) (_get_Mstatus_MIE v))
        (← do
          bif (← (currentlyEnabled Ext_S))
          then (pure (_get_Mstatus_SIE v))
          else (pure (0b0 : (BitVec 1))))))
  let dirty :=
    (((extStatus_of_bits (_get_Mstatus_FS o)) == Dirty) || (((extStatus_of_bits (_get_Mstatus_XS o)) == Dirty) || ((extStatus_of_bits
            (_get_Mstatus_VS o)) == Dirty)))
  (pure (_update_Mstatus_SD o (bool_to_bits dirty)))

def cur_architecture (_ : Unit) : SailM Architecture := do
  let a ← (( do
    match (← readReg cur_privilege) with
    | Machine => (pure (_get_Misa_MXL (← readReg misa)))
    | Supervisor => (pure (get_mstatus_SXL (← readReg mstatus)))
    | User => (pure (get_mstatus_UXL (← readReg mstatus))) ) : SailM arch_xlen )
  (architecture_backwards a)

def in32BitMode (_ : Unit) : SailM Bool := do
  (pure ((← (cur_architecture ())) == RV32))

def undefined_MEnvcfg (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MEnvcfg (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MEnvcfg_CBCFE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_MEnvcfg_CBCFE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SEnvcfg_CBCFE (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _set_MEnvcfg_CBCFE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_CBCFE r v)

def _get_SEnvcfg_CBCFE (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _set_SEnvcfg_CBCFE (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_CBCFE r v)

def _get_MEnvcfg_CBIE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _update_MEnvcfg_CBIE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _update_SEnvcfg_CBIE (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 2)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _set_MEnvcfg_CBIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_CBIE r v)

def _get_SEnvcfg_CBIE (v : (BitVec (2 ^ 3 * 8))) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _set_SEnvcfg_CBIE (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_CBIE r v)

def _get_MEnvcfg_CBZE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_MEnvcfg_CBZE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SEnvcfg_CBZE (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_MEnvcfg_CBZE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_CBZE r v)

def _get_SEnvcfg_CBZE (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _set_SEnvcfg_CBZE (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_CBZE r v)

def _get_MEnvcfg_FIOM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_MEnvcfg_FIOM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_SEnvcfg_FIOM (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _set_MEnvcfg_FIOM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_FIOM r v)

def _get_SEnvcfg_FIOM (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _set_SEnvcfg_FIOM (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_FIOM r v)

def _get_MEnvcfg_PBMTE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _update_MEnvcfg_PBMTE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _set_MEnvcfg_PBMTE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_PBMTE r v)

def _get_MEnvcfg_STCE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _update_MEnvcfg_STCE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _set_MEnvcfg_STCE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_STCE r v)

def _get_MEnvcfg_wpri_0 (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 3 1)

def _update_MEnvcfg_wpri_0 (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 1 x)

def _update_SEnvcfg_wpri_0 (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 3)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 3 1 x)

def _set_MEnvcfg_wpri_0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_wpri_0 r v)

def _get_SEnvcfg_wpri_0 (v : (BitVec (2 ^ 3 * 8))) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 3 1)

def _set_SEnvcfg_wpri_0 (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SEnvcfg_wpri_0 r v)

def _get_MEnvcfg_wpri_1 (v : (BitVec 64)) : (BitVec 54) :=
  (Sail.BitVec.extractLsb v 61 8)

def _update_MEnvcfg_wpri_1 (v : (BitVec 64)) (x : (BitVec 54)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 8 x)

def _set_MEnvcfg_wpri_1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 54)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MEnvcfg_wpri_1 r v)

def undefined_SEnvcfg (_ : Unit) : SailM (BitVec (2 ^ 3 * 8)) := do
  (undefined_bitvector ((2 ^i 3) *i 8))

def Mk_SEnvcfg (v : (BitVec 64)) : (BitVec (2 ^ 3 * 8)) :=
  v

def legalize_menvcfg (o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_MEnvcfg v)
  (pure (_update_MEnvcfg_STCE
      (_update_MEnvcfg_CBIE
        (_update_MEnvcfg_CBCFE
          (_update_MEnvcfg_CBZE
            (_update_MEnvcfg_FIOM o
              (bif (sys_enable_writable_fiom ())
              then (_get_MEnvcfg_FIOM v)
              else (0b0 : (BitVec 1))))
            (← do
              bif (← (currentlyEnabled Ext_Zicboz))
              then (pure (_get_MEnvcfg_CBZE v))
              else (pure (0b0 : (BitVec 1)))))
          (← do
            bif (← (currentlyEnabled Ext_Zicbom))
            then (pure (_get_MEnvcfg_CBCFE v))
            else (pure (0b0 : (BitVec 1)))))
        (← do
          bif (← (currentlyEnabled Ext_Zicbom))
          then
            (bif ((_get_MEnvcfg_CBIE v) != (0b10 : (BitVec 2)))
            then (pure (_get_MEnvcfg_CBIE v))
            else (pure (0b00 : (BitVec 2))))
          else (pure (0b00 : (BitVec 2)))))
      (← do
        bif (← (currentlyEnabled Ext_Sstc))
        then (pure (_get_MEnvcfg_STCE v))
        else (pure (0b0 : (BitVec 1))))))

def legalize_senvcfg (o : (BitVec (2 ^ 3 * 8))) (v : (BitVec (2 ^ 3 * 8))) : SailM (BitVec (2 ^ 3 * 8)) := do
  let v := (Mk_SEnvcfg v)
  (pure (_update_SEnvcfg_CBIE
      (_update_SEnvcfg_CBCFE
        (_update_SEnvcfg_CBZE
          (_update_SEnvcfg_FIOM o
            (bif (sys_enable_writable_fiom ())
            then (_get_SEnvcfg_FIOM v)
            else (0b0 : (BitVec 1))))
          (← do
            bif (← (currentlyEnabled Ext_Zicboz))
            then (pure (_get_SEnvcfg_CBZE v))
            else (pure (0b0 : (BitVec 1)))))
        (← do
          bif (← (currentlyEnabled Ext_Zicbom))
          then (pure (_get_SEnvcfg_CBCFE v))
          else (pure (0b0 : (BitVec 1)))))
      (← do
        bif (← (currentlyEnabled Ext_Zicbom))
        then
          (bif ((_get_SEnvcfg_CBIE v) != (0b10 : (BitVec 2)))
          then (pure (_get_SEnvcfg_CBIE v))
          else (pure (0b00 : (BitVec 2))))
        else (pure (0b00 : (BitVec 2))))))

def is_fiom_active (_ : Unit) : SailM Bool := do
  match (← readReg cur_privilege) with
  | Machine => (pure false)
  | Supervisor => (pure ((_get_MEnvcfg_FIOM (← readReg menvcfg)) == (0b1 : (BitVec 1))))
  | User =>
    (pure (((_get_MEnvcfg_FIOM (← readReg menvcfg)) ||| (_get_SEnvcfg_FIOM (← readReg senvcfg))) == (0b1 : (BitVec 1))))

def undefined_Minterrupts (_ : Unit) : SailM (BitVec (2 ^ 3 * 8)) := do
  (undefined_bitvector ((2 ^i 3) *i 8))

def Mk_Minterrupts (v : (BitVec 64)) : (BitVec (2 ^ 3 * 8)) :=
  v

def _get_Minterrupts_MEI (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_Minterrupts_MEI (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _set_Minterrupts_MEI (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Minterrupts_MEI r v)

def _get_Minterrupts_MSI (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_Minterrupts_MSI (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _set_Minterrupts_MSI (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Minterrupts_MSI r v)

def _get_Minterrupts_MTI (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_Minterrupts_MTI (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Minterrupts_MTI (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Minterrupts_MTI r v)

def _get_Minterrupts_SEI (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_Minterrupts_SEI (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_Sinterrupts_SEI (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _set_Minterrupts_SEI (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Minterrupts_SEI r v)

def _get_Sinterrupts_SEI (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _set_Sinterrupts_SEI (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sinterrupts_SEI r v)

def _get_Minterrupts_SSI (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_Minterrupts_SSI (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_Sinterrupts_SSI (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _set_Minterrupts_SSI (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Minterrupts_SSI r v)

def _get_Sinterrupts_SSI (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _set_Sinterrupts_SSI (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sinterrupts_SSI r v)

def _get_Minterrupts_STI (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_Minterrupts_STI (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_Sinterrupts_STI (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _set_Minterrupts_STI (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Minterrupts_STI r v)

def _get_Sinterrupts_STI (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _set_Sinterrupts_STI (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Sinterrupts_STI r v)

def legalize_mip (o : (BitVec (2 ^ 3 * 8))) (v : (BitVec (2 ^ 3 * 8))) : SailM (BitVec (2 ^ 3 * 8)) := do
  let v := (Mk_Minterrupts v)
  (pure (_update_Minterrupts_STI
      (_update_Minterrupts_SSI
        (_update_Minterrupts_SEI o
          (← do
            bif (← (currentlyEnabled Ext_S))
            then (pure (_get_Minterrupts_SEI v))
            else (pure (0b0 : (BitVec 1)))))
        (← do
          bif (← (currentlyEnabled Ext_S))
          then (pure (_get_Minterrupts_SSI v))
          else (pure (0b0 : (BitVec 1)))))
      (← do
        bif (← (currentlyEnabled Ext_S))
        then
          (do
            bif ((← (currentlyEnabled Ext_Sstc)) && ((_get_MEnvcfg_STCE (← readReg menvcfg)) == (0b1 : (BitVec 1))))
            then (pure (_get_Minterrupts_STI o))
            else (pure (_get_Minterrupts_STI v)))
        else (pure (0b0 : (BitVec 1))))))

def legalize_mie (o : (BitVec (2 ^ 3 * 8))) (v : (BitVec (2 ^ 3 * 8))) : SailM (BitVec (2 ^ 3 * 8)) := do
  let v := (Mk_Minterrupts v)
  (pure (_update_Minterrupts_SSI
      (_update_Minterrupts_STI
        (_update_Minterrupts_SEI
          (_update_Minterrupts_MSI
            (_update_Minterrupts_MTI (_update_Minterrupts_MEI o (_get_Minterrupts_MEI v))
              (_get_Minterrupts_MTI v)) (_get_Minterrupts_MSI v))
          (← do
            bif (← (currentlyEnabled Ext_S))
            then (pure (_get_Minterrupts_SEI v))
            else (pure (0b0 : (BitVec 1)))))
        (← do
          bif (← (currentlyEnabled Ext_S))
          then (pure (_get_Minterrupts_STI v))
          else (pure (0b0 : (BitVec 1)))))
      (← do
        bif (← (currentlyEnabled Ext_S))
        then (pure (_get_Minterrupts_SSI v))
        else (pure (0b0 : (BitVec 1))))))

def legalize_mideleg (o : (BitVec (2 ^ 3 * 8))) (v : (BitVec (2 ^ 3 * 8))) : (BitVec (2 ^ 3 * 8)) :=
  (_update_Minterrupts_MSI
    (_update_Minterrupts_MTI (_update_Minterrupts_MEI (Mk_Minterrupts v) (0b0 : (BitVec 1)))
      (0b0 : (BitVec 1))) (0b0 : (BitVec 1)))

def undefined_Medeleg (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_Medeleg (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_Medeleg_Breakpoint (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_Medeleg_Breakpoint (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _set_Medeleg_Breakpoint (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Breakpoint r v)

def _get_Medeleg_Fetch_Access_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_Medeleg_Fetch_Access_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _set_Medeleg_Fetch_Access_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Fetch_Access_Fault r v)

def _get_Medeleg_Fetch_Addr_Align (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_Medeleg_Fetch_Addr_Align (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _set_Medeleg_Fetch_Addr_Align (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Fetch_Addr_Align r v)

def _get_Medeleg_Fetch_Page_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_Medeleg_Fetch_Page_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _set_Medeleg_Fetch_Page_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Fetch_Page_Fault r v)

def _get_Medeleg_Illegal_Instr (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_Medeleg_Illegal_Instr (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _set_Medeleg_Illegal_Instr (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Illegal_Instr r v)

def _get_Medeleg_Load_Access_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_Medeleg_Load_Access_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _set_Medeleg_Load_Access_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Load_Access_Fault r v)

def _get_Medeleg_Load_Addr_Align (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_Medeleg_Load_Addr_Align (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _set_Medeleg_Load_Addr_Align (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Load_Addr_Align r v)

def _get_Medeleg_Load_Page_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_Medeleg_Load_Page_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _set_Medeleg_Load_Page_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_Load_Page_Fault r v)

def _get_Medeleg_MEnvCall (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_Medeleg_MEnvCall (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _set_Medeleg_MEnvCall (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_MEnvCall r v)

def _get_Medeleg_SAMO_Access_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_Medeleg_SAMO_Access_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Medeleg_SAMO_Access_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_SAMO_Access_Fault r v)

def _get_Medeleg_SAMO_Addr_Align (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_Medeleg_SAMO_Addr_Align (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _set_Medeleg_SAMO_Addr_Align (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_SAMO_Addr_Align r v)

def _get_Medeleg_SAMO_Page_Fault (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_Medeleg_SAMO_Page_Fault (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _set_Medeleg_SAMO_Page_Fault (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_SAMO_Page_Fault r v)

def _get_Medeleg_SEnvCall (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_Medeleg_SEnvCall (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _set_Medeleg_SEnvCall (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_SEnvCall r v)

def _get_Medeleg_UEnvCall (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_Medeleg_UEnvCall (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _set_Medeleg_UEnvCall (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Medeleg_UEnvCall r v)

def legalize_medeleg (o : (BitVec 64)) (v : (BitVec 64)) : (BitVec 64) :=
  (_update_Medeleg_MEnvCall (Mk_Medeleg v) (0b0 : (BitVec 1)))

def undefined_Mtvec (_ : Unit) : SailM (BitVec (2 ^ 3 * 8)) := do
  (undefined_bitvector ((2 ^i 3) *i 8))

def Mk_Mtvec (v : (BitVec 64)) : (BitVec (2 ^ 3 * 8)) :=
  v

def _get_Mtvec_Base (v : (BitVec (2 ^ 3 * 8))) : (BitVec 62) :=
  (Sail.BitVec.extractLsb v (((2 ^i 3) *i 8) -i 1) 2)

def _update_Mtvec_Base (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 62)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v (((2 ^i 3) *i 8) -i 1) 2 x)

def _set_Mtvec_Base (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 62)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mtvec_Base r v)

def _get_Mtvec_Mode (v : (BitVec (2 ^ 3 * 8))) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _update_Mtvec_Mode (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 2)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _update_Satp32_Mode (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_Satp64_Mode (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _set_Mtvec_Mode (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mtvec_Mode r v)

def _get_Satp32_Mode (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_Satp64_Mode (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _set_Satp32_Mode (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp32_Mode r v)

def _set_Satp64_Mode (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp64_Mode r v)

def legalize_tvec (o : (BitVec (2 ^ 3 * 8))) (v : (BitVec (2 ^ 3 * 8))) : (BitVec (2 ^ 3 * 8)) :=
  let v := (Mk_Mtvec v)
  match (trapVectorMode_of_bits (_get_Mtvec_Mode v)) with
  | TV_Direct => v
  | TV_Vector => v
  | _ => (_update_Mtvec_Mode v (_get_Mtvec_Mode o))

def undefined_Mcause (_ : Unit) : SailM (BitVec (2 ^ 3 * 8)) := do
  (undefined_bitvector ((2 ^i 3) *i 8))

def Mk_Mcause (v : (BitVec 64)) : (BitVec (2 ^ 3 * 8)) :=
  v

def _get_Mcause_Cause (v : (BitVec (2 ^ 3 * 8))) : (BitVec 63) :=
  (Sail.BitVec.extractLsb v (((2 ^i 3) *i 8) -i 2) 0)

def _update_Mcause_Cause (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 63)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v (((2 ^i 3) *i 8) -i 2) 0 x)

def _set_Mcause_Cause (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 63)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mcause_Cause r v)

def _get_Mcause_IsInterrupt (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v (((2 ^i 3) *i 8) -i 1) (((2 ^i 3) *i 8) -i 1))

def _update_Mcause_IsInterrupt (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v (((2 ^i 3) *i 8) -i 1) (((2 ^i 3) *i 8) -i 1) x)

def _set_Mcause_IsInterrupt (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Mcause_IsInterrupt r v)

def tvec_addr (m : (BitVec (2 ^ 3 * 8))) (c : (BitVec (2 ^ 3 * 8))) : (Option (BitVec (2 ^ 3 * 8))) :=
  let base : xlenbits := ((_get_Mtvec_Base m) ++ (0b00 : (BitVec 2)))
  match (trapVectorMode_of_bits (_get_Mtvec_Mode m)) with
  | TV_Direct => (some base)
  | TV_Vector =>
    (bif ((_get_Mcause_IsInterrupt c) == (0b1 : (BitVec 1)))
    then (some (base + (shiftl (zero_extend (m := ((2 ^i 3) *i 8)) (_get_Mcause_Cause c)) 2)))
    else (some base))
  | TV_Reserved => none

def legalize_xepc (v : (BitVec (2 ^ 3 * 8))) : (BitVec (2 ^ 3 * 8)) :=
  bif (hartSupports Ext_C)
  then (BitVec.update v 0 0#1)
  else (Sail.BitVec.updateSubrange v 1 0 (zeros (n := (1 -i (0 -i 1)))))

def align_pc (addr : (BitVec (2 ^ 3 * 8))) : SailM (BitVec (2 ^ 3 * 8)) := do
  bif ((_get_Misa_C (← readReg misa)) == (0b1 : (BitVec 1)))
  then (pure (BitVec.update addr 0 0#1))
  else (pure (Sail.BitVec.updateSubrange addr 1 0 (zeros (n := (1 -i (0 -i 1))))))

def undefined_Counteren (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_Counteren (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_Counteren_CY (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_Counteren_CY (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_Counterin_CY (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _set_Counteren_CY (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counteren_CY r v)

def _get_Counterin_CY (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _set_Counterin_CY (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counterin_CY r v)

def _get_Counteren_HPM (v : (BitVec 32)) : (BitVec 29) :=
  (Sail.BitVec.extractLsb v 31 3)

def _update_Counteren_HPM (v : (BitVec 32)) (x : (BitVec 29)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 3 x)

def _update_Counterin_HPM (v : (BitVec 32)) (x : (BitVec 29)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 3 x)

def _set_Counteren_HPM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 29)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counteren_HPM r v)

def _get_Counterin_HPM (v : (BitVec 32)) : (BitVec 29) :=
  (Sail.BitVec.extractLsb v 31 3)

def _set_Counterin_HPM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 29)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counterin_HPM r v)

def _get_Counteren_IR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_Counteren_IR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_Counterin_IR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _set_Counteren_IR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counteren_IR r v)

def _get_Counterin_IR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _set_Counterin_IR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counterin_IR r v)

def _get_Counteren_TM (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_Counteren_TM (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _set_Counteren_TM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Counteren_TM r v)

def legalize_scounteren (c : (BitVec 32)) (v : (BitVec (2 ^ 3 * 8))) : (BitVec 32) :=
  let supported_counters :=
    ((Sail.BitVec.extractLsb (sys_writable_hpm_counters ()) 31 3) ++ (0b111 : (BitVec 3)))
  (Mk_Counteren ((Sail.BitVec.extractLsb v 31 0) &&& supported_counters))

def legalize_mcounteren (c : (BitVec 32)) (v : (BitVec (2 ^ 3 * 8))) : (BitVec 32) :=
  let supported_counters :=
    ((Sail.BitVec.extractLsb (sys_writable_hpm_counters ()) 31 3) ++ (0b111 : (BitVec 3)))
  (Mk_Counteren ((Sail.BitVec.extractLsb v 31 0) &&& supported_counters))

def undefined_Counterin (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_Counterin (v : (BitVec 32)) : (BitVec 32) :=
  v

def legalize_mcountinhibit (c : (BitVec 32)) (v : (BitVec (2 ^ 3 * 8))) : (BitVec 32) :=
  let supported_counters :=
    ((Sail.BitVec.extractLsb (sys_writable_hpm_counters ()) 31 3) ++ (0b101 : (BitVec 3)))
  (Mk_Counterin ((Sail.BitVec.extractLsb v 31 0) &&& supported_counters))

def undefined_Sstatus (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_Sstatus (v : (BitVec 64)) : (BitVec 64) :=
  v

def lower_mstatus (m : (BitVec 64)) : (BitVec 64) :=
  let s := (Mk_Sstatus (zeros (n := 64)))
  (_update_Sstatus_SIE
    (_update_Sstatus_SPIE
      (_update_Sstatus_SPP
        (_update_Sstatus_VS
          (_update_Sstatus_FS
            (_update_Sstatus_XS
              (_update_Sstatus_SUM
                (_update_Sstatus_MXR
                  (_update_Sstatus_UXL (_update_Sstatus_SD s (_get_Mstatus_SD m))
                    (_get_Mstatus_UXL m)) (_get_Mstatus_MXR m)) (_get_Mstatus_SUM m))
              (_get_Mstatus_XS m)) (_get_Mstatus_FS m)) (_get_Mstatus_VS m)) (_get_Mstatus_SPP m))
      (_get_Mstatus_SPIE m)) (_get_Mstatus_SIE m))

def lift_sstatus (m : (BitVec 64)) (s : (BitVec 64)) : (BitVec 64) :=
  let dirty :=
    (((extStatus_of_bits (_get_Sstatus_FS s)) == Dirty) || (((extStatus_of_bits (_get_Sstatus_XS s)) == Dirty) || ((extStatus_of_bits
            (_get_Sstatus_VS s)) == Dirty)))
  (_update_Mstatus_SIE
    (_update_Mstatus_SPIE
      (_update_Mstatus_SPP
        (_update_Mstatus_VS
          (_update_Mstatus_FS
            (_update_Mstatus_XS
              (_update_Mstatus_SUM
                (_update_Mstatus_MXR
                  (_update_Mstatus_UXL (_update_Mstatus_SD m (bool_to_bits dirty))
                    (_get_Sstatus_UXL s)) (_get_Sstatus_MXR s)) (_get_Sstatus_SUM s))
              (_get_Sstatus_XS s)) (_get_Sstatus_FS s)) (_get_Sstatus_VS s)) (_get_Sstatus_SPP s))
      (_get_Sstatus_SPIE s)) (_get_Sstatus_SIE s))

def legalize_sstatus (m : (BitVec 64)) (v : (BitVec (2 ^ 3 * 8))) : SailM (BitVec 64) := do
  (legalize_mstatus m (lift_sstatus m (Mk_Sstatus (zero_extend (m := 64) v))))

def undefined_Sinterrupts (_ : Unit) : SailM (BitVec (2 ^ 3 * 8)) := do
  (undefined_bitvector ((2 ^i 3) *i 8))

def Mk_Sinterrupts (v : (BitVec 64)) : (BitVec (2 ^ 3 * 8)) :=
  v

def lower_mip (m : (BitVec (2 ^ 3 * 8))) (d : (BitVec (2 ^ 3 * 8))) : (BitVec (2 ^ 3 * 8)) :=
  let s : Sinterrupts := (Mk_Sinterrupts (zeros (n := 64)))
  (_update_Sinterrupts_SSI
    (_update_Sinterrupts_STI
      (_update_Sinterrupts_SEI s ((_get_Minterrupts_SEI m) &&& (_get_Minterrupts_SEI d)))
      ((_get_Minterrupts_STI m) &&& (_get_Minterrupts_STI d)))
    ((_get_Minterrupts_SSI m) &&& (_get_Minterrupts_SSI d)))

def lower_mie (m : (BitVec (2 ^ 3 * 8))) (d : (BitVec (2 ^ 3 * 8))) : (BitVec (2 ^ 3 * 8)) :=
  let s : Sinterrupts := (Mk_Sinterrupts (zeros (n := 64)))
  (_update_Sinterrupts_SSI
    (_update_Sinterrupts_STI
      (_update_Sinterrupts_SEI s ((_get_Minterrupts_SEI m) &&& (_get_Minterrupts_SEI d)))
      ((_get_Minterrupts_STI m) &&& (_get_Minterrupts_STI d)))
    ((_get_Minterrupts_SSI m) &&& (_get_Minterrupts_SSI d)))

def lift_sip (o : (BitVec (2 ^ 3 * 8))) (d : (BitVec (2 ^ 3 * 8))) (s : (BitVec (2 ^ 3 * 8))) : (BitVec (2 ^ 3 * 8)) :=
  let m : Minterrupts := o
  bif ((_get_Minterrupts_SSI d) == (0b1 : (BitVec 1)))
  then (_update_Minterrupts_SSI m (_get_Sinterrupts_SSI s))
  else m

def legalize_sip (m : (BitVec (2 ^ 3 * 8))) (d : (BitVec (2 ^ 3 * 8))) (v : (BitVec (2 ^ 3 * 8))) : (BitVec (2 ^ 3 * 8)) :=
  (lift_sip m d (Mk_Sinterrupts v))

def lift_sie (o : (BitVec (2 ^ 3 * 8))) (d : (BitVec (2 ^ 3 * 8))) (s : (BitVec (2 ^ 3 * 8))) : (BitVec (2 ^ 3 * 8)) :=
  let m : Minterrupts := o
  (_update_Minterrupts_SSI
    (_update_Minterrupts_STI
      (_update_Minterrupts_SEI m
        (bif ((_get_Minterrupts_SEI d) == (0b1 : (BitVec 1)))
        then (_get_Sinterrupts_SEI s)
        else (_get_Minterrupts_SEI m)))
      (bif ((_get_Minterrupts_STI d) == (0b1 : (BitVec 1)))
      then (_get_Sinterrupts_STI s)
      else (_get_Minterrupts_STI m)))
    (bif ((_get_Minterrupts_SSI d) == (0b1 : (BitVec 1)))
    then (_get_Sinterrupts_SSI s)
    else (_get_Minterrupts_SSI m)))

def legalize_sie (m : (BitVec (2 ^ 3 * 8))) (d : (BitVec (2 ^ 3 * 8))) (v : (BitVec (2 ^ 3 * 8))) : (BitVec (2 ^ 3 * 8)) :=
  (lift_sie m d (Mk_Sinterrupts v))

def undefined_Satp64 (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_Satp64 (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_Satp64_Asid (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 59 44)

def _update_Satp64_Asid (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 44 x)

def _update_Satp32_Asid (v : (BitVec 32)) (x : (BitVec 9)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 22 x)

def _set_Satp64_Asid (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp64_Asid r v)

def _get_Satp32_Asid (v : (BitVec 32)) : (BitVec 9) :=
  (Sail.BitVec.extractLsb v 30 22)

def _set_Satp32_Asid (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 9)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp32_Asid r v)

def _get_Satp64_PPN (v : (BitVec 64)) : (BitVec 44) :=
  (Sail.BitVec.extractLsb v 43 0)

def _update_Satp64_PPN (v : (BitVec 64)) (x : (BitVec 44)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 0 x)

def _update_Satp32_PPN (v : (BitVec 32)) (x : (BitVec 22)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 0 x)

def _set_Satp64_PPN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 44)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp64_PPN r v)

def _get_Satp32_PPN (v : (BitVec 32)) : (BitVec 22) :=
  (Sail.BitVec.extractLsb v 21 0)

def _set_Satp32_PPN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 22)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Satp32_PPN r v)

def undefined_Satp32 (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_Satp32 (v : (BitVec 32)) : (BitVec 32) :=
  v

def legalize_satp (arch : Architecture) (prev_value : (BitVec (2 ^ 3 * 8))) (written_value : (BitVec (2 ^ 3 * 8))) : SailM (BitVec (2 ^ 3 * 8)) := do
  let s := (Mk_Satp64 written_value)
  match (satpMode_of_bits arch (_get_Satp64_Mode s)) with
  | none => (pure prev_value)
  | .some Sv_mode =>
    (do
      match Sv_mode with
      | Bare =>
        (do
          bif (← (currentlyEnabled Ext_Svbare))
          then (pure s)
          else (pure prev_value))
      | Sv39 =>
        (do
          bif (← (currentlyEnabled Ext_Sv39))
          then (pure s)
          else (pure prev_value))
      | Sv48 =>
        (do
          bif (← (currentlyEnabled Ext_Sv48))
          then (pure s)
          else (pure prev_value))
      | Sv57 =>
        (do
          bif (← (currentlyEnabled Ext_Sv57))
          then (pure s)
          else (pure prev_value))
      | _ => (pure prev_value))

def get_vlenb (_ : Unit) : (BitVec (2 ^ 3 * 8)) :=
  (to_bits xlen (Int.tdiv (2 ^i (get_vlen_pow ())) 8))

def undefined_Vtype (_ : Unit) : SailM (BitVec (2 ^ 3 * 8)) := do
  (undefined_bitvector ((2 ^i 3) *i 8))

def Mk_Vtype (v : (BitVec 64)) : (BitVec (2 ^ 3 * 8)) :=
  v

def _get_Vtype_reserved (v : (BitVec (2 ^ 3 * 8))) : (BitVec 55) :=
  (Sail.BitVec.extractLsb v (((2 ^i 3) *i 8) -i 2) 8)

def _update_Vtype_reserved (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 55)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v (((2 ^i 3) *i 8) -i 2) 8 x)

def _update_PTE_Ext_reserved (v : (BitVec 10)) (x : (BitVec 7)) : (BitVec 10) :=
  (Sail.BitVec.updateSubrange v 6 0 x)

def _set_Vtype_reserved (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 55)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Vtype_reserved r v)

def _get_PTE_Ext_reserved (v : (BitVec 10)) : (BitVec 7) :=
  (Sail.BitVec.extractLsb v 6 0)

def _set_PTE_Ext_reserved (r_ref : (RegisterRef (BitVec 10))) (v : (BitVec 7)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Ext_reserved r v)

def _get_Vtype_vill (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v (((2 ^i 3) *i 8) -i 1) (((2 ^i 3) *i 8) -i 1))

def _update_Vtype_vill (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v (((2 ^i 3) *i 8) -i 1) (((2 ^i 3) *i 8) -i 1) x)

def _set_Vtype_vill (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Vtype_vill r v)

def _get_Vtype_vlmul (v : (BitVec (2 ^ 3 * 8))) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _update_Vtype_vlmul (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 3)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _set_Vtype_vlmul (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Vtype_vlmul r v)

def _get_Vtype_vma (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_Vtype_vma (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_Vtype_vma (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Vtype_vma r v)

def _get_Vtype_vsew (v : (BitVec (2 ^ 3 * 8))) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 5 3)

def _update_Vtype_vsew (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 3)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 5 3 x)

def _set_Vtype_vsew (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Vtype_vsew r v)

def _get_Vtype_vta (v : (BitVec (2 ^ 3 * 8))) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_Vtype_vta (v : (BitVec (2 ^ 3 * 8))) (x : (BitVec 1)) : (BitVec (2 ^ 3 * 8)) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _set_Vtype_vta (r_ref : (RegisterRef (BitVec (2 ^ 3 * 8)))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Vtype_vta r v)

def get_sew_pow (_ : Unit) : SailM Int := do
  match_bv (_get_Vtype_vsew (← readReg vtype)) with
  | 000 => do (pure 3)
  | 001 => do (pure 4)
  | 010 => do (pure 5)
  | 011 => do (pure 6)
  | _ => do
    (do
      assert false "invalid vsew field in vtype"
      throw Error.Exit)

def get_sew (_ : Unit) : SailM Int := do
  match (← (get_sew_pow ())) with
  | 3 => (pure 8)
  | 4 => (pure 16)
  | 5 => (pure 32)
  | 6 => (pure 64)
  | _ =>
    (do
      (internal_error "riscv_sys_regs.sail" 953 "invalid SEW")
      (pure 8))

def get_sew_bytes (_ : Unit) : SailM Int := do
  match (← (get_sew_pow ())) with
  | 3 => (pure 1)
  | 4 => (pure 2)
  | 5 => (pure 4)
  | 6 => (pure 8)
  | _ =>
    (do
      (internal_error "riscv_sys_regs.sail" 964 "invalid SEW")
      (pure 1))

def get_lmul_pow (_ : Unit) : SailM Int := do
  match_bv (_get_Vtype_vlmul (← readReg vtype)) with
  | 101 => do (pure (-3))
  | 110 => do (pure (-2))
  | 111 => do (pure (-1))
  | 000 => do (pure 0)
  | 001 => do (pure 1)
  | 010 => do (pure 2)
  | 011 => do (pure 3)
  | _ => do
    (do
      assert false "invalid vlmul field in vtype"
      throw Error.Exit)

def undefined_agtype (_ : Unit) : SailM agtype := do
  (internal_pick [UNDISTURBED, AGNOSTIC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def agtype_of_num (arg_ : Nat) : agtype :=
  match arg_ with
  | 0 => UNDISTURBED
  | _ => AGNOSTIC

def num_of_agtype (arg_ : agtype) : Int :=
  match arg_ with
  | UNDISTURBED => 0
  | AGNOSTIC => 1

def decode_agtype (ag : (BitVec 1)) : agtype :=
  match_bv ag with
  | 0 => UNDISTURBED
  | _ => AGNOSTIC

def get_vtype_vma (_ : Unit) : SailM agtype := do
  (pure (decode_agtype (_get_Vtype_vma (← readReg vtype))))

def get_vtype_vta (_ : Unit) : SailM agtype := do
  (pure (decode_agtype (_get_Vtype_vta (← readReg vtype))))

