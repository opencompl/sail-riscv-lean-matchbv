import LeanRV64D.RiscvVmemPtw

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

def tlb_vpn_bits := (57 -i 12)

def tlb_ppn_bits := 44

/-- Type quantifiers: pte_width : Nat, pte_width ∈ {4, 8} -/
def tlb_get_pte (pte_width : Nat) (ent : TLB_Entry) : (BitVec (pte_width * 8)) :=
  (Sail.BitVec.extractLsb ent.pte ((pte_width *i 8) -i 1) 0)

/-- Type quantifiers: k_n : Nat, k_n ∈ {4, 8} -/
def tlb_set_pte (ent : TLB_Entry) (pte : (BitVec (k_n * 8))) : TLB_Entry :=
  { ent with pte := (zero_extend (m := 64) pte) }

/-- Type quantifiers: sv_width : Nat, is_sv_mode(sv_width) -/
def tlb_get_ppn (sv_width : Nat) (ent : TLB_Entry) (vpn : (BitVec (sv_width - 12))) : (BitVec (bif sv_width
  = 32 then 22 else 44)) :=
  let vpn : (BitVec 64) := (sign_extend (m := 64) vpn)
  let levelMask : (BitVec 64) := (zero_extend (m := 64) ent.levelMask)
  let ppn : (BitVec 64) := (zero_extend (m := 64) ent.ppn)
  (trunc
    (m := (bif (sv_width == 32)
    then 22
    else 44)) (ppn ||| (vpn &&& levelMask)))

/-- Type quantifiers: sv_mode : Nat, is_sv_mode(sv_mode) -/
def tlb_hash (sv_mode : Nat) (vpn : (BitVec (sv_mode - 12))) : Nat :=
  (BitVec.toNat (Sail.BitVec.extractLsb vpn 5 0))

def reset_TLB (_ : Unit) : SailM Unit := do
  writeReg tlb (vectorInit none)

/-- Type quantifiers: index : Nat, 0 ≤ index ∧ index ≤ (64 - 1) -/
def write_TLB (index : Nat) (entry : TLB_Entry) : SailM Unit := do
  writeReg tlb (vectorUpdate (← readReg tlb) index (some entry))

def match_TLB_Entry (ent : TLB_Entry) (asid : (BitVec 16)) (vpn : (BitVec (57 - 12))) : Bool :=
  ((ent.global || (ent.asid == asid)) && (ent.vpn == (vpn &&& (Complement.complement ent.levelMask))))

def flush_TLB_Entry (ent : TLB_Entry) (asid : (Option (BitVec 16))) (vaddr : (Option (BitVec (2 ^ 3 * 8)))) : Bool :=
  let asid_matches : Bool :=
    match asid with
    | .some asid => ((ent.asid == asid) && (not ent.global))
    | none => true
  let addr_matches : Bool :=
    match vaddr with
    | .some vaddr =>
      (let vaddr : (BitVec 64) := (sign_extend (m := 64) vaddr)
      (ent.vpn == ((Sail.BitVec.extractLsb vaddr 56 pagesize_bits) &&& (Complement.complement
            ent.levelMask))))
    | none => true
  (asid_matches && addr_matches)

/-- Type quantifiers: sv_width : Nat, is_sv_mode(sv_width) -/
def lookup_TLB (sv_width : Nat) (asid : (BitVec 16)) (vpn : (BitVec (sv_width - 12))) : SailM (Option (Nat × TLB_Entry)) := do
  let index := (tlb_hash sv_width vpn)
  match (GetElem?.getElem! (← readReg tlb) index) with
  | none => (pure none)
  | .some entry =>
    (bif (match_TLB_Entry entry asid (sign_extend (m := (57 -i 12)) vpn))
    then (pure (some (index, entry)))
    else (pure none))

/-- Type quantifiers: k_ex283859# : Bool, level : Nat, sv_width : Nat, is_sv_mode(sv_width), 0 ≤
  level ∧
  level ≤
  (bif sv_width = 32 then 1 else (bif sv_width = 39 then 2 else (bif sv_width = 48 then 3 else 4))) -/
def add_to_TLB (sv_width : Nat) (asid : (BitVec 16)) (vpn : (BitVec (sv_width - 12))) (ppn : (BitVec (bif sv_width
  = 32 then 22 else 44))) (pte : (BitVec (bif sv_width = 32 then 32 else 64))) (pteAddr : physaddr) (level : Nat) (global : Bool) : SailM Unit := do
  let shift :=
    (level *i (bif (sv_width == 32)
      then 10
      else 9))
  let levelMask := (ones (n := shift))
  let vpn := (vpn &&& (Complement.complement (zero_extend (m := (sv_width -i 12)) levelMask)))
  let ppn :=
    (ppn &&& (Complement.complement
        (zero_extend
          (m := (bif (sv_width == 32)
          then 22
          else 44)) levelMask)))
  let entry : TLB_Entry :=
    { asid := asid
      global := global
      pte := (zero_extend (m := 64) pte)
      pteAddr := pteAddr
      levelMask := (zero_extend (m := (57 -i 12)) levelMask)
      vpn := (sign_extend (m := (57 -i 12)) vpn)
      ppn := (zero_extend (m := 44) ppn) }
  let index := (tlb_hash sv_width vpn)
  writeReg tlb (vectorUpdate (← readReg tlb) index (some entry))

def flush_TLB (asid : (Option (BitVec 16))) (addr : (Option (BitVec (2 ^ 3 * 8)))) : SailM Unit := do
  let loop_i_lower := 0
  let loop_i_upper ← do (pure ((Vector.length (← readReg tlb)) -i 1))
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      match (GetElem?.getElem! (← readReg tlb) i) with
      | none => (pure ())
      | .some entry =>
        (do
          bif (flush_TLB_Entry entry asid addr)
          then writeReg tlb (vectorUpdate (← readReg tlb) i none)
          else (pure ()))
  (pure loop_vars)

