import LeanRV64D.Common

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

def undefined_Access_variety (_ : Unit) : SailM Access_variety := do
  (internal_pick [AV_plain, AV_exclusive, AV_atomic_rmw])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Access_variety_of_num (arg_ : Nat) : Access_variety :=
  match arg_ with
  | 0 => AV_plain
  | 1 => AV_exclusive
  | _ => AV_atomic_rmw

def num_of_Access_variety (arg_ : Access_variety) : Int :=
  match arg_ with
  | AV_plain => 0
  | AV_exclusive => 1
  | AV_atomic_rmw => 2

def undefined_Access_strength (_ : Unit) : SailM Access_strength := do
  (internal_pick [AS_normal, AS_rel_or_acq, AS_acq_rcpc])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Access_strength_of_num (arg_ : Nat) : Access_strength :=
  match arg_ with
  | 0 => AS_normal
  | 1 => AS_rel_or_acq
  | _ => AS_acq_rcpc

def num_of_Access_strength (arg_ : Access_strength) : Int :=
  match arg_ with
  | AS_normal => 0
  | AS_rel_or_acq => 1
  | AS_acq_rcpc => 2

def undefined_Explicit_access_kind (_ : Unit) : SailM Explicit_access_kind := do
  (pure { variety := (← (undefined_Access_variety ()))
          strength := (← (undefined_Access_strength ())) })

/-- Type quantifiers: k_n : Nat, k_vasize : Nat, k_pa : Type, k_translation_summary : Type, k_arch_ak
  : Type, k_n > 0 ∧ k_vasize > 0 -/
def mem_read_request_is_exclusive (request : (Mem_read_request k_n k_vasize k_pa k_translation_summary k_arch_ak)) : Bool :=
  match request.access_kind with
  | .AK_explicit eak =>
    (match eak.variety with
    | AV_exclusive => true
    | _ => false)
  | _ => false

/-- Type quantifiers: k_n : Nat, k_vasize : Nat, k_pa : Type, k_translation_summary : Type, k_arch_ak
  : Type, k_n > 0 ∧ k_vasize > 0 -/
def mem_read_request_is_ifetch (request : (Mem_read_request k_n k_vasize k_pa k_translation_summary k_arch_ak)) : Bool :=
  match request.access_kind with
  | .AK_ifetch () => true
  | _ => false

def __monomorphize_reads : Bool := false

def __monomorphize_writes : Bool := false

/-- Type quantifiers: k_n : Nat, k_vasize : Nat, k_pa : Type, k_translation_summary : Type, k_arch_ak
  : Type, k_n > 0 ∧ k_vasize > 0 -/
def mem_write_request_is_exclusive (request : (Mem_write_request k_n k_vasize k_pa k_translation_summary k_arch_ak)) : Bool :=
  match request.access_kind with
  | .AK_explicit eak =>
    (match eak.variety with
    | AV_exclusive => true
    | _ => false)
  | _ => false

/-- Type quantifiers: x_0 : Nat, x_0 ∈ {32, 64} -/
def sail_address_announce (x_0 : Nat) (x_1 : (BitVec x_0)) : Unit :=
  ()

