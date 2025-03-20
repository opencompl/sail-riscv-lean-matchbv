import LeanRV64DLEAN.RiscvPmpRegs

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

def pmpAddrRange (cfg : (BitVec 8)) (pmpaddr : (BitVec (2 ^ 3 * 8))) (prev_pmpaddr : (BitVec (2 ^ 3 * 8))) : SailM (Option ((BitVec (2 ^ 3 * 8)) × (BitVec (2 ^ 3 * 8)))) := do
  match (pmpAddrMatchType_of_bits (_get_Pmpcfg_ent_A cfg)) with
  | OFF => (pure none)
  | TOR => (pure (some (prev_pmpaddr, pmpaddr)))
  | NA4 =>
    assert ((sys_pmp_grain ()) <b 1) "NA4 cannot be selected when PMP grain G >= 1."
    let lo := pmpaddr
    (pure (some (lo, (BitVec.addInt lo 1))))
  | NAPOT =>
    let mask := (pmpaddr ^^^ (BitVec.addInt pmpaddr 1))
    let lo := (pmpaddr &&& (Complement.complement mask))
    let len := (BitVec.addInt mask 1)
    (pure (some (lo, (lo + len))))

def pmpCheckRWX (ent : (BitVec 8)) (acc : (AccessType Unit)) : Bool :=
  match acc with
  | .Read _ => (BEq.beq (_get_Pmpcfg_ent_R ent) (0b1 : (BitVec 1)))
  | .Write _ => (BEq.beq (_get_Pmpcfg_ent_W ent) (0b1 : (BitVec 1)))
  | .ReadWrite _ =>
    (Bool.and (BEq.beq (_get_Pmpcfg_ent_R ent) (0b1 : (BitVec 1)))
      (BEq.beq (_get_Pmpcfg_ent_W ent) (0b1 : (BitVec 1))))
  | .Execute () => (BEq.beq (_get_Pmpcfg_ent_X ent) (0b1 : (BitVec 1)))

def undefined_pmpAddrMatch (_ : Unit) : SailM pmpAddrMatch := do
  (internal_pick [PMP_NoMatch, PMP_PartialMatch, PMP_Match])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def pmpAddrMatch_of_num (arg_ : Nat) : pmpAddrMatch :=
  match arg_ with
  | 0 => PMP_NoMatch
  | 1 => PMP_PartialMatch
  | _ => PMP_Match

def num_of_pmpAddrMatch (arg_ : pmpAddrMatch) : Int :=
  match arg_ with
  | PMP_NoMatch => 0
  | PMP_PartialMatch => 1
  | PMP_Match => 2

def pmpMatchAddr (typ_0 : physaddr) (width : (BitVec (2 ^ 3 * 8))) (rng : (Option ((BitVec (2 ^ 3 * 8)) × (BitVec (2 ^ 3 * 8))))) : pmpAddrMatch :=
  let .physaddr addr : physaddr := typ_0
  match rng with
  | none => PMP_NoMatch
  | .some (lo, hi) =>
    let addr := (BitVec.toNat addr)
    let width := (BitVec.toNat width)
    let lo := ((BitVec.toNat lo) *i 4)
    let hi := ((BitVec.toNat hi) *i 4)
    if (hi ≤b lo)
    then PMP_NoMatch
    else
      if (Bool.or ((addr +i width) ≤b lo) (hi ≤b addr))
      then PMP_NoMatch
      else
        if (Bool.and (lo ≤b addr) ((addr +i width) ≤b hi))
        then PMP_Match
        else PMP_PartialMatch

def undefined_pmpMatch (_ : Unit) : SailM pmpMatch := do
  (internal_pick [PMP_Success, PMP_Continue, PMP_Fail])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def pmpMatch_of_num (arg_ : Nat) : pmpMatch :=
  match arg_ with
  | 0 => PMP_Success
  | 1 => PMP_Continue
  | _ => PMP_Fail

def num_of_pmpMatch (arg_ : pmpMatch) : Int :=
  match arg_ with
  | PMP_Success => 0
  | PMP_Continue => 1
  | PMP_Fail => 2

def pmpMatchEntry (addr : physaddr) (width : (BitVec (2 ^ 3 * 8))) (acc : (AccessType Unit)) (priv : Privilege) (ent : (BitVec 8)) (pmpaddr : (BitVec (2 ^ 3 * 8))) (prev_pmpaddr : (BitVec (2 ^ 3 * 8))) : SailM pmpMatch := do
  let rng ← do (pmpAddrRange ent pmpaddr prev_pmpaddr)
  match (pmpMatchAddr addr width rng) with
  | PMP_NoMatch => (pure PMP_Continue)
  | PMP_PartialMatch => (pure PMP_Fail)
  | PMP_Match =>
    if (Bool.or (pmpCheckRWX ent acc) (Bool.and (BEq.beq priv Machine) (not (pmpLocked ent))))
    then (pure PMP_Success)
    else (pure PMP_Fail)

def accessToFault (acc : (AccessType Unit)) : ExceptionType :=
  match acc with
  | .Read _ => (E_Load_Access_Fault ())
  | .Write _ => (E_SAMO_Access_Fault ())
  | .ReadWrite _ => (E_SAMO_Access_Fault ())
  | .Execute () => (E_Fetch_Access_Fault ())

/-- Type quantifiers: width : Nat, width > 0 -/
def pmpCheck (addr : physaddr) (width : Nat) (acc : (AccessType Unit)) (priv : Privilege) : SailM (Option ExceptionType) := SailME.run do
  let width : xlenbits := (to_bits xlen width)
  let loop_i_lower := 0
  let loop_i_upper := 63
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper + 1:1]i do
    let () := loop_vars
    loop_vars ← do
      let prev_pmpaddr ← do
        if (i >b 0)
        then (pmpReadAddrReg (i -i 1))
        else (pure (zeros_implicit (n := ((2 ^i 3) *i 8))))
      match (← (pmpMatchEntry addr width acc priv (GetElem?.getElem! (← readReg pmpcfg_n) i)
          (← (pmpReadAddrReg i)) prev_pmpaddr)) with
      | PMP_Success => throw (none : (Option ExceptionType))
      | PMP_Fail => throw ((some (accessToFault acc)) : (Option ExceptionType))
      | PMP_Continue => (pure ())
  (pure loop_vars)
  if (BEq.beq priv Machine)
  then (pure none)
  else (pure (some (accessToFault acc)))

def reset_pmp (_ : Unit) : SailM Unit := do
  assert (Bool.or (BEq.beq (sys_pmp_count ()) 0)
    ((Bool.or (BEq.beq (sys_pmp_count ()) 16) ((BEq.beq (sys_pmp_count ()) 64) : Bool)) : Bool)) "sys_pmp_count() must be 0, 16, or 64"
  let loop_i_lower := 0
  let loop_i_upper := 63
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper + 1:1]i do
    let () := loop_vars
    loop_vars ← do
      writeReg pmpcfg_n (vectorUpdate (← readReg pmpcfg_n) i
        (_update_Pmpcfg_ent_L
          (_update_Pmpcfg_ent_A (GetElem?.getElem! (← readReg pmpcfg_n) i)
            (pmpAddrMatchType_to_bits OFF)) (0b0 : (BitVec 1))))
  (pure loop_vars)

