import LeanRV64D.RiscvInstRetire

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

def undefined_PTE_Ext (_ : Unit) : SailM (BitVec 10) := do
  (undefined_bitvector 10)

def Mk_PTE_Ext (v : (BitVec 10)) : (BitVec 10) :=
  v

def _get_PTE_Ext_PBMT (v : (BitVec 10)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 8 7)

def _update_PTE_Ext_PBMT (v : (BitVec 10)) (x : (BitVec 2)) : (BitVec 10) :=
  (Sail.BitVec.updateSubrange v 8 7 x)

def _set_PTE_Ext_PBMT (r_ref : (RegisterRef (BitVec 10))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PTE_Ext_PBMT r v)

def default_sv32_ext_pte : pte_ext_bits := (zeros (n := 10))

/-- Type quantifiers: k_pte_size : Nat, k_pte_size ∈ {32, 64} -/
def ext_bits_of_PTE (pte : (BitVec k_pte_size)) : (BitVec 10) :=
  (Mk_PTE_Ext
    (bif ((Sail.BitVec.length pte) == 64)
    then (Sail.BitVec.extractLsb pte 63 54)
    else default_sv32_ext_pte))

/-- Type quantifiers: k_pte_size : Nat, k_pte_size ∈ {32, 64} -/
def PPN_of_PTE (pte : (BitVec k_pte_size)) : (BitVec (bif k_pte_size = 32 then 22 else 44)) :=
  bif ((Sail.BitVec.length pte) == 32)
  then (Sail.BitVec.extractLsb pte 31 10)
  else (Sail.BitVec.extractLsb pte 53 10)

def undefined_PTE_Flags (_ : Unit) : SailM (BitVec 8) := do
  (undefined_bitvector 8)

def Mk_PTE_Flags (v : (BitVec 8)) : (BitVec 8) :=
  v

def pte_is_non_leaf (pte_flags : (BitVec 8)) : Bool :=
  (((_get_PTE_Flags_X pte_flags) == (0b0 : (BitVec 1))) && (((_get_PTE_Flags_W pte_flags) == (0b0 : (BitVec 1))) && ((_get_PTE_Flags_R
          pte_flags) == (0b0 : (BitVec 1)))))

def pte_is_invalid (pte_flags : (BitVec 8)) (pte_ext : (BitVec 10)) : SailM Bool := do
  (pure (((_get_PTE_Flags_V pte_flags) == (0b0 : (BitVec 1))) || ((((_get_PTE_Flags_W pte_flags) == (0b1 : (BitVec 1))) && ((_get_PTE_Flags_R
              pte_flags) == (0b0 : (BitVec 1)))) || ((((_get_PTE_Ext_N pte_ext) != (0b0 : (BitVec 1))) && (not
              (← (currentlyEnabled Ext_Svnapot)))) || ((((_get_PTE_Ext_PBMT pte_ext) != (zeros
                  (n := 2))) && (not (← (currentlyEnabled Ext_Svpbmt)))) || ((_get_PTE_Ext_reserved
                pte_ext) != (zeros (n := 7))))))))

/-- Type quantifiers: k_ex283427# : Bool, k_ex283426# : Bool -/
def check_PTE_permission (ac : (AccessType Unit)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (pte_flags : (BitVec 8)) (ext : (BitVec 10)) (ext_ptw : Unit) : SailM PTE_Check := do
  let pte_U := (_get_PTE_Flags_U pte_flags)
  let pte_R := (_get_PTE_Flags_R pte_flags)
  let pte_W := (_get_PTE_Flags_W pte_flags)
  let pte_X := (_get_PTE_Flags_X pte_flags)
  let success ← (( do
    match (ac, priv) with
    | (.Read _, User) =>
      (pure ((pte_U == (0b1 : (BitVec 1))) && ((pte_R == (0b1 : (BitVec 1))) || ((pte_X == (0b1 : (BitVec 1))) && mxr))))
    | (.Write _, User) => (pure ((pte_U == (0b1 : (BitVec 1))) && (pte_W == (0b1 : (BitVec 1)))))
    | (.ReadWrite (_, _), User) =>
      (pure ((pte_U == (0b1 : (BitVec 1))) && ((pte_W == (0b1 : (BitVec 1))) && ((pte_R == (0b1 : (BitVec 1))) || ((pte_X == (0b1 : (BitVec 1))) && mxr)))))
    | (.InstructionFetch (), User) =>
      (pure ((pte_U == (0b1 : (BitVec 1))) && (pte_X == (0b1 : (BitVec 1)))))
    | (.Read _, Supervisor) =>
      (pure (((pte_U == (0b0 : (BitVec 1))) || do_sum) && ((pte_R == (0b1 : (BitVec 1))) || ((pte_X == (0b1 : (BitVec 1))) && mxr))))
    | (.Write _, Supervisor) =>
      (pure (((pte_U == (0b0 : (BitVec 1))) || do_sum) && (pte_W == (0b1 : (BitVec 1)))))
    | (.ReadWrite (_, _), Supervisor) =>
      (pure (((pte_U == (0b0 : (BitVec 1))) || do_sum) && ((pte_W == (0b1 : (BitVec 1))) && ((pte_R == (0b1 : (BitVec 1))) || ((pte_X == (0b1 : (BitVec 1))) && mxr)))))
    | (.InstructionFetch (), Supervisor) =>
      (pure ((pte_U == (0b0 : (BitVec 1))) && (pte_X == (0b1 : (BitVec 1)))))
    | (_, Machine) => (internal_error "riscv_vmem_pte.sail" 132 "m-mode mem perm check") ) : SailM
    Bool )
  bif success
  then (pure (PTE_Check_Success ()))
  else (pure (PTE_Check_Failure ((), ())))

/-- Type quantifiers: k_pte_size : Nat, k_pte_size ∈ {32, 64} -/
def update_PTE_Bits (pte : (BitVec k_pte_size)) (a : (AccessType Unit)) : (Option (BitVec k_pte_size)) :=
  let pte_flags := (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
  let update_d : Bool :=
    (((_get_PTE_Flags_D pte_flags) == (0b0 : (BitVec 1))) && (match a with
      | .InstructionFetch () => false
      | .Read _ => false
      | .Write _ => true
      | .ReadWrite (_, _) => true : Bool))
  let update_a := ((_get_PTE_Flags_A pte_flags) == (0b0 : (BitVec 1)))
  bif (update_d || update_a)
  then
    (let pte_flags :=
      (_update_PTE_Flags_D (_update_PTE_Flags_A pte_flags (0b1 : (BitVec 1)))
        (bif update_d
        then (0b1 : (BitVec 1))
        else (_get_PTE_Flags_D pte_flags)))
    (some (Sail.BitVec.updateSubrange pte 7 0 pte_flags)))
  else none

