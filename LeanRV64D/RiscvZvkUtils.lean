import LeanRV64D.RiscvTypesKext

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
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
open Retire_Failure
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

/-- Type quantifiers: emul_pow : Int -/
def zvk_valid_reg_overlap (rs : vregidx) (rd : vregidx) (emul_pow : Int) : Bool :=
  let reg_group_size :=
    bif (emul_pow >b 0)
    then (2 ^i emul_pow)
    else 1
  let rs_int := (BitVec.toNat (vregidx_bits rs))
  let rd_int := (BitVec.toNat (vregidx_bits rd))
  (Bool.or ((rs_int +i reg_group_size) ≤b rd_int) ((rd_int +i reg_group_size) ≤b rs_int))

/-- Type quantifiers: EGS : Int, EGW : Int -/
def zvk_check_encdec (EGW : Int) (EGS : Int) : SailM Bool := do
  (pure (Bool.and (BEq.beq (Int.emod (BitVec.toNat (← readReg vl)) EGS) 0)
      (← do
        (pure (Bool.and (BEq.beq (Int.emod (BitVec.toNat (← readReg vstart)) EGS) 0)
            (← do
              (pure (((2 ^i (← (get_lmul_pow ()))) *i VLEN) ≥b EGW))))))))

def undefined_zvkfunct6 (_ : Unit) : SailM zvkfunct6 := do
  (internal_pick [ZVK_VSHA2CH, ZVK_VSHA2CL])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def zvkfunct6_of_num (arg_ : Nat) : zvkfunct6 :=
  match arg_ with
  | 0 => ZVK_VSHA2CH
  | _ => ZVK_VSHA2CL

def num_of_zvkfunct6 (arg_ : zvkfunct6) : Int :=
  match arg_ with
  | ZVK_VSHA2CH => 0
  | ZVK_VSHA2CL => 1

def zvknhab_check_encdec (vs2 : vregidx) (vs1 : vregidx) (vd : vregidx) : SailM Bool := do
  let SEW ← do (get_sew ())
  let LMUL_pow ← do (get_lmul_pow ())
  (pure (Bool.and (← (zvk_check_encdec SEW 4))
      (Bool.and (zvk_valid_reg_overlap vs1 vd LMUL_pow) (zvk_valid_reg_overlap vs2 vd LMUL_pow))))

/-- Type quantifiers: k_n : Nat, SEW : Nat, k_n = SEW ∧ SEW = 32 ∨ SEW = 64 -/
def zvk_sig0 (x : (BitVec k_n)) (SEW : Nat) : (BitVec k_n) :=
  match SEW with
  | 32 => ((rotater x 7) ^^^ ((rotater x 18) ^^^ (shift_bits_right x
          (to_bits (Sail.BitVec.length x) 3))))
  | _ => ((rotater x 1) ^^^ ((rotater x 8) ^^^ (shift_bits_right x (to_bits xlen_val 7))))

/-- Type quantifiers: k_n : Nat, SEW : Nat, k_n = SEW ∧ SEW = 32 ∨ SEW = 64 -/
def zvk_sig1 (x : (BitVec k_n)) (SEW : Nat) : (BitVec k_n) :=
  match SEW with
  | 32 => ((rotater x 17) ^^^ ((rotater x 19) ^^^ (shift_bits_right x
          (to_bits (Sail.BitVec.length x) 10))))
  | _ => ((rotater x 19) ^^^ ((rotater x 61) ^^^ (shift_bits_right x (to_bits xlen_val 6))))

/-- Type quantifiers: k_n : Nat, SEW : Nat, k_n = SEW ∧ SEW = 32 ∨ SEW = 64 -/
def zvk_sum0 (x : (BitVec k_n)) (SEW : Nat) : (BitVec k_n) :=
  match SEW with
  | 32 => ((rotater x 2) ^^^ ((rotater x 13) ^^^ (rotater x 22)))
  | _ => ((rotater x 28) ^^^ ((rotater x 34) ^^^ (rotater x 39)))

/-- Type quantifiers: k_n : Nat, SEW : Nat, k_n = SEW ∧ SEW = 32 ∨ SEW = 64 -/
def zvk_sum1 (x : (BitVec k_n)) (SEW : Nat) : (BitVec k_n) :=
  match SEW with
  | 32 => ((rotater x 6) ^^^ ((rotater x 11) ^^^ (rotater x 25)))
  | _ => ((rotater x 14) ^^^ ((rotater x 18) ^^^ (rotater x 41)))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def zvk_ch (x : (BitVec k_n)) (y : (BitVec k_n)) (z : (BitVec k_n)) : (BitVec k_n) :=
  ((x &&& y) ^^^ ((Complement.complement x) &&& z))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def zvk_maj (x : (BitVec k_n)) (y : (BitVec k_n)) (z : (BitVec k_n)) : (BitVec k_n) :=
  ((x &&& y) ^^^ ((x &&& z) ^^^ (y &&& z)))

