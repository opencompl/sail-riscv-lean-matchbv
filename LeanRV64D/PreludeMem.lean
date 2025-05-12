import LeanRV64D.ReadWrite

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

def undefined_write_kind (_ : Unit) : SailM write_kind := do
  (internal_pick
    [Write_plain, Write_RISCV_release, Write_RISCV_strong_release, Write_RISCV_conditional, Write_RISCV_conditional_release, Write_RISCV_conditional_strong_release])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def write_kind_of_num (arg_ : Nat) : write_kind :=
  match arg_ with
  | 0 => Write_plain
  | 1 => Write_RISCV_release
  | 2 => Write_RISCV_strong_release
  | 3 => Write_RISCV_conditional
  | 4 => Write_RISCV_conditional_release
  | _ => Write_RISCV_conditional_strong_release

def num_of_write_kind (arg_ : write_kind) : Int :=
  match arg_ with
  | Write_plain => 0
  | Write_RISCV_release => 1
  | Write_RISCV_strong_release => 2
  | Write_RISCV_conditional => 3
  | Write_RISCV_conditional_release => 4
  | Write_RISCV_conditional_strong_release => 5

def undefined_read_kind (_ : Unit) : SailM read_kind := do
  (internal_pick
    [Read_plain, Read_ifetch, Read_RISCV_acquire, Read_RISCV_strong_acquire, Read_RISCV_reserved, Read_RISCV_reserved_acquire, Read_RISCV_reserved_strong_acquire])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 6 -/
def read_kind_of_num (arg_ : Nat) : read_kind :=
  match arg_ with
  | 0 => Read_plain
  | 1 => Read_ifetch
  | 2 => Read_RISCV_acquire
  | 3 => Read_RISCV_strong_acquire
  | 4 => Read_RISCV_reserved
  | 5 => Read_RISCV_reserved_acquire
  | _ => Read_RISCV_reserved_strong_acquire

def num_of_read_kind (arg_ : read_kind) : Int :=
  match arg_ with
  | Read_plain => 0
  | Read_ifetch => 1
  | Read_RISCV_acquire => 2
  | Read_RISCV_strong_acquire => 3
  | Read_RISCV_reserved => 4
  | Read_RISCV_reserved_acquire => 5
  | Read_RISCV_reserved_strong_acquire => 6

def undefined_barrier_kind (_ : Unit) : SailM barrier_kind := do
  (internal_pick
    [Barrier_RISCV_rw_rw, Barrier_RISCV_r_rw, Barrier_RISCV_r_r, Barrier_RISCV_rw_w, Barrier_RISCV_w_w, Barrier_RISCV_w_rw, Barrier_RISCV_rw_r, Barrier_RISCV_r_w, Barrier_RISCV_w_r, Barrier_RISCV_tso, Barrier_RISCV_i])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 10 -/
def barrier_kind_of_num (arg_ : Nat) : barrier_kind :=
  match arg_ with
  | 0 => Barrier_RISCV_rw_rw
  | 1 => Barrier_RISCV_r_rw
  | 2 => Barrier_RISCV_r_r
  | 3 => Barrier_RISCV_rw_w
  | 4 => Barrier_RISCV_w_w
  | 5 => Barrier_RISCV_w_rw
  | 6 => Barrier_RISCV_rw_r
  | 7 => Barrier_RISCV_r_w
  | 8 => Barrier_RISCV_w_r
  | 9 => Barrier_RISCV_tso
  | _ => Barrier_RISCV_i

def num_of_barrier_kind (arg_ : barrier_kind) : Int :=
  match arg_ with
  | Barrier_RISCV_rw_rw => 0
  | Barrier_RISCV_r_rw => 1
  | Barrier_RISCV_r_r => 2
  | Barrier_RISCV_rw_w => 3
  | Barrier_RISCV_w_w => 4
  | Barrier_RISCV_w_rw => 5
  | Barrier_RISCV_rw_r => 6
  | Barrier_RISCV_r_w => 7
  | Barrier_RISCV_w_r => 8
  | Barrier_RISCV_tso => 9
  | Barrier_RISCV_i => 10

def undefined_RISCV_strong_access (_ : Unit) : SailM RISCV_strong_access := do
  (pure { variety := (← (undefined_Access_variety ())) })

def physaddrbits_zero_extend (xs : (BitVec 64)) : (BitVec 64) :=
  (zero_extend (m := 64) xs)

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def write_ram (wk : write_kind) (app_1 : physaddr) (width : Nat) (data : (BitVec (8 * width))) (meta : Unit) : SailM Bool := do
  let .Physaddr addr := app_1
  let request : (Mem_write_request width 64 physaddrbits Unit RISCV_strong_access) :=
    { access_kind := match wk with
      | Write_plain =>
        (AK_explicit
          { variety := AV_plain
            strength := AS_normal })
      | Write_RISCV_release =>
        (AK_explicit
          { variety := AV_plain
            strength := AS_rel_or_acq })
      | Write_RISCV_strong_release => (AK_arch { variety := AV_plain })
      | Write_RISCV_conditional =>
        (AK_explicit
          { variety := AV_exclusive
            strength := AS_normal })
      | Write_RISCV_conditional_release =>
        (AK_explicit
          { variety := AV_exclusive
            strength := AS_rel_or_acq })
      | Write_RISCV_conditional_strong_release => (AK_arch { variety := AV_exclusive })
      va := none
      pa := addr
      translation := ()
      size := width
      value := (some data)
      tag := none }
  match (← (sail_mem_write request)) with
  | .Ok _ =>
    (let _ : Unit := (__WriteRAM_Meta addr width meta)
    (pure true))
  | .Err () => (pure false)

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def write_ram_ea (wk : write_kind) (app_1 : physaddr) (width : Nat) : Unit :=
  let .Physaddr addr := app_1
  ()

/-- Type quantifiers: k_ex278831# : Bool, width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def read_ram (rk : read_kind) (app_1 : physaddr) (width : Nat) (read_meta : Bool) : SailM ((BitVec (8 * width)) × Unit) := do
  let .Physaddr addr := app_1
  let meta :=
    bif read_meta
    then (__ReadRAM_Meta addr width)
    else default_meta
  let request : (Mem_read_request width 64 physaddrbits Unit RISCV_strong_access) :=
    { access_kind := match rk with
      | Read_plain =>
        (AK_explicit
          { variety := AV_plain
            strength := AS_normal })
      | Read_ifetch => (AK_ifetch ())
      | Read_RISCV_acquire =>
        (AK_explicit
          { variety := AV_plain
            strength := AS_rel_or_acq })
      | Read_RISCV_strong_acquire => (AK_arch { variety := AV_plain })
      | Read_RISCV_reserved =>
        (AK_explicit
          { variety := AV_exclusive
            strength := AS_normal })
      | Read_RISCV_reserved_acquire =>
        (AK_explicit
          { variety := AV_exclusive
            strength := AS_rel_or_acq })
      | Read_RISCV_reserved_strong_acquire => (AK_arch { variety := AV_exclusive })
      va := none
      pa := addr
      translation := ()
      size := width
      tag := false }
  match (← (sail_mem_read request)) with
  | .Ok (value, _) => (pure (value, meta))
  | .Err () => throw Error.Exit

