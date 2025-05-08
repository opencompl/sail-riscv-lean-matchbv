import LeanRV64D.RiscvInstsZicsr

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

def encdec_rounding_mode_forwards (arg_ : rounding_mode) : (BitVec 3) :=
  match arg_ with
  | RM_RNE => (0b000 : (BitVec 3))
  | RM_RTZ => (0b001 : (BitVec 3))
  | RM_RDN => (0b010 : (BitVec 3))
  | RM_RUP => (0b011 : (BitVec 3))
  | RM_RMM => (0b100 : (BitVec 3))
  | RM_DYN => (0b111 : (BitVec 3))

def encdec_rounding_mode_backwards (arg_ : (BitVec 3)) : SailM rounding_mode := do
  match_bv arg_ with
  | 000 => do (pure RM_RNE)
  | 001 => do (pure RM_RTZ)
  | 010 => do (pure RM_RDN)
  | 011 => do (pure RM_RUP)
  | 100 => do (pure RM_RMM)
  | 111 => do (pure RM_DYN)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_rounding_mode_forwards_matches (arg_ : rounding_mode) : Bool :=
  match arg_ with
  | RM_RNE => true
  | RM_RTZ => true
  | RM_RDN => true
  | RM_RUP => true
  | RM_RMM => true
  | RM_DYN => true
  | _ => false

def encdec_rounding_mode_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  match_bv arg_ with
  | 000 => true
  | 001 => true
  | 010 => true
  | 011 => true
  | 100 => true
  | 111 => true
  | _ => false

def frm_mnemonic_backwards (arg_ : String) : SailM rounding_mode := do
  match arg_ with
  | "rne" => (pure RM_RNE)
  | "rtz" => (pure RM_RTZ)
  | "rdn" => (pure RM_RDN)
  | "rup" => (pure RM_RUP)
  | "rmm" => (pure RM_RMM)
  | "dyn" => (pure RM_DYN)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def frm_mnemonic_forwards_matches (arg_ : rounding_mode) : Bool :=
  match arg_ with
  | RM_RNE => true
  | RM_RTZ => true
  | RM_RDN => true
  | RM_RUP => true
  | RM_RMM => true
  | RM_DYN => true
  | _ => false

def frm_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "rne" => true
  | "rtz" => true
  | "rdn" => true
  | "rup" => true
  | "rmm" => true
  | "dyn" => true
  | _ => false

def valid_rounding_mode (rm : (BitVec 3)) : Bool :=
  ((rm != (0b101 : (BitVec 3))) && (rm != (0b110 : (BitVec 3))))

def select_instr_or_fcsr_rm (instr_rm : rounding_mode) : SailM (Option rounding_mode) := do
  bif (instr_rm == RM_DYN)
  then
    (do
      let fcsr_rm ← do (pure (_get_Fcsr_FRM (← readReg fcsr)))
      bif ((valid_rounding_mode fcsr_rm) && (fcsr_rm != (encdec_rounding_mode_forwards RM_DYN)))
      then (pure (some (← (encdec_rounding_mode_backwards fcsr_rm))))
      else (pure none))
  else (pure (some instr_rm))

def nxFlag (_ : Unit) : (BitVec 5) :=
  (0b00001 : (BitVec 5))

def ufFlag (_ : Unit) : (BitVec 5) :=
  (0b00010 : (BitVec 5))

def ofFlag (_ : Unit) : (BitVec 5) :=
  (0b00100 : (BitVec 5))

def dzFlag (_ : Unit) : (BitVec 5) :=
  (0b01000 : (BitVec 5))

def nvFlag (_ : Unit) : (BitVec 5) :=
  (0b10000 : (BitVec 5))

def fsplit_S (x32 : (BitVec 32)) : ((BitVec 1) × (BitVec 8) × (BitVec 23)) :=
  ((Sail.BitVec.extractLsb x32 31 31), (Sail.BitVec.extractLsb x32 30 23), (Sail.BitVec.extractLsb
    x32 22 0))

def fmake_S (sign : (BitVec 1)) (exp : (BitVec 8)) (mant : (BitVec 23)) : (BitVec 32) :=
  (sign ++ (exp ++ mant))

def f_is_neg_inf_S (x32 : (BitVec 32)) : Bool :=
  let (sign, exp, mant) := (fsplit_S x32)
  ((sign == (0b1 : (BitVec 1))) && ((exp == (ones (n := 8))) && (mant == (zeros (n := 23)))))

def f_is_neg_norm_S (x32 : (BitVec 32)) : Bool :=
  let (sign, exp, mant) := (fsplit_S x32)
  ((sign == (0b1 : (BitVec 1))) && ((exp != (zeros (n := 8))) && (exp != (ones (n := 8)))))

def f_is_neg_subnorm_S (x32 : (BitVec 32)) : Bool :=
  let (sign, exp, mant) := (fsplit_S x32)
  ((sign == (0b1 : (BitVec 1))) && ((exp == (zeros (n := 8))) && (mant != (zeros (n := 23)))))

def f_is_neg_zero_S (x32 : (BitVec 32)) : Bool :=
  let (sign, exp, mant) := (fsplit_S x32)
  ((sign == (ones (n := 1))) && ((exp == (zeros (n := 8))) && (mant == (zeros (n := 23)))))

def f_is_pos_zero_S (x32 : (BitVec 32)) : Bool :=
  let (sign, exp, mant) := (fsplit_S x32)
  ((sign == (zeros (n := 1))) && ((exp == (zeros (n := 8))) && (mant == (zeros (n := 23)))))

def f_is_pos_subnorm_S (x32 : (BitVec 32)) : Bool :=
  let (sign, exp, mant) := (fsplit_S x32)
  ((sign == (zeros (n := 1))) && ((exp == (zeros (n := 8))) && (mant != (zeros (n := 23)))))

def f_is_pos_norm_S (x32 : (BitVec 32)) : Bool :=
  let (sign, exp, mant) := (fsplit_S x32)
  ((sign == (zeros (n := 1))) && ((exp != (zeros (n := 8))) && (exp != (ones (n := 8)))))

def f_is_pos_inf_S (x32 : (BitVec 32)) : Bool :=
  let (sign, exp, mant) := (fsplit_S x32)
  ((sign == (zeros (n := 1))) && ((exp == (ones (n := 8))) && (mant == (zeros (n := 23)))))

def f_is_SNaN_S (x32 : (BitVec 32)) : Bool :=
  let (sign, exp, mant) := (fsplit_S x32)
  ((exp == (ones (n := 8))) && (((BitVec.access mant 22) == 0#1) && (mant != (zeros (n := 23)))))

def f_is_QNaN_S (x32 : (BitVec 32)) : Bool :=
  let (sign, exp, mant) := (fsplit_S x32)
  ((exp == (ones (n := 8))) && ((BitVec.access mant 22) == 1#1))

def f_is_NaN_S (x32 : (BitVec 32)) : Bool :=
  let (sign, exp, mant) := (fsplit_S x32)
  ((exp == (ones (n := 8))) && (mant != (zeros (n := 23))))

def negate_S (x32 : (BitVec 32)) : (BitVec 32) :=
  let (sign, exp, mant) := (fsplit_S x32)
  let new_sign :=
    bif (sign == (0b0 : (BitVec 1)))
    then (0b1 : (BitVec 1))
    else (0b0 : (BitVec 1))
  (fmake_S new_sign exp mant)

def feq_quiet_S (v1 : (BitVec 32)) (v2 : (BitVec 32)) : (Bool × (BitVec 5)) :=
  let (s1, e1, m1) := (fsplit_S v1)
  let (s2, e2, m2) := (fsplit_S v2)
  let v1Is0 := ((f_is_neg_zero_S v1) || (f_is_pos_zero_S v1))
  let v2Is0 := ((f_is_neg_zero_S v2) || (f_is_pos_zero_S v2))
  let result := ((v1 == v2) || (v1Is0 && v2Is0))
  let fflags :=
    bif ((f_is_SNaN_S v1) || (f_is_SNaN_S v2))
    then (nvFlag ())
    else (zeros (n := 5))
  (result, fflags)

/-- Type quantifiers: k_ex298908# : Bool -/
def flt_S (v1 : (BitVec 32)) (v2 : (BitVec 32)) (is_quiet : Bool) : (Bool × (BitVec 5)) :=
  let (s1, e1, m1) := (fsplit_S v1)
  let (s2, e2, m2) := (fsplit_S v2)
  let result : Bool :=
    bif ((s1 == (0b0 : (BitVec 1))) && (s2 == (0b0 : (BitVec 1))))
    then
      (bif (e1 == e2)
      then ((BitVec.toNat m1) <b (BitVec.toNat m2))
      else ((BitVec.toNat e1) <b (BitVec.toNat e2)))
    else
      (bif ((s1 == (0b0 : (BitVec 1))) && (s2 == (0b1 : (BitVec 1))))
      then false
      else
        (bif ((s1 == (0b1 : (BitVec 1))) && (s2 == (0b0 : (BitVec 1))))
        then true
        else
          (bif (e1 == e2)
          then ((BitVec.toNat m1) >b (BitVec.toNat m2))
          else ((BitVec.toNat e1) >b (BitVec.toNat e2)))))
  let fflags :=
    bif is_quiet
    then
      (bif ((f_is_SNaN_S v1) || (f_is_SNaN_S v2))
      then (nvFlag ())
      else (zeros (n := 5)))
    else
      (bif ((f_is_NaN_S v1) || (f_is_NaN_S v2))
      then (nvFlag ())
      else (zeros (n := 5)))
  (result, fflags)

/-- Type quantifiers: k_ex298976# : Bool -/
def fle_S (v1 : (BitVec 32)) (v2 : (BitVec 32)) (is_quiet : Bool) : (Bool × (BitVec 5)) :=
  let (s1, e1, m1) := (fsplit_S v1)
  let (s2, e2, m2) := (fsplit_S v2)
  let v1Is0 := ((f_is_neg_zero_S v1) || (f_is_pos_zero_S v1))
  let v2Is0 := ((f_is_neg_zero_S v2) || (f_is_pos_zero_S v2))
  let result : Bool :=
    bif ((s1 == (0b0 : (BitVec 1))) && (s2 == (0b0 : (BitVec 1))))
    then
      (bif (e1 == e2)
      then ((BitVec.toNat m1) ≤b (BitVec.toNat m2))
      else ((BitVec.toNat e1) <b (BitVec.toNat e2)))
    else
      (bif ((s1 == (0b0 : (BitVec 1))) && (s2 == (0b1 : (BitVec 1))))
      then (v1Is0 && v2Is0)
      else
        (bif ((s1 == (0b1 : (BitVec 1))) && (s2 == (0b0 : (BitVec 1))))
        then true
        else
          (bif (e1 == e2)
          then ((BitVec.toNat m1) ≥b (BitVec.toNat m2))
          else ((BitVec.toNat e1) >b (BitVec.toNat e2)))))
  let fflags :=
    bif is_quiet
    then
      (bif ((f_is_SNaN_S v1) || (f_is_SNaN_S v2))
      then (nvFlag ())
      else (zeros (n := 5)))
    else
      (bif ((f_is_NaN_S v1) || (f_is_NaN_S v2))
      then (nvFlag ())
      else (zeros (n := 5)))
  (result, fflags)

def haveSingleFPU (_ : Unit) : SailM Bool := do
  (pure ((← (currentlyEnabled Ext_F)) || (← (currentlyEnabled Ext_Zfinx))))

def f_madd_type_mnemonic_S_backwards (arg_ : String) : SailM f_madd_op_S := do
  match arg_ with
  | "fmadd.s" => (pure FMADD_S)
  | "fmsub.s" => (pure FMSUB_S)
  | "fnmsub.s" => (pure FNMSUB_S)
  | "fnmadd.s" => (pure FNMADD_S)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_madd_type_mnemonic_S_forwards_matches (arg_ : f_madd_op_S) : Bool :=
  match arg_ with
  | FMADD_S => true
  | FMSUB_S => true
  | FNMSUB_S => true
  | FNMADD_S => true
  | _ => false

def f_madd_type_mnemonic_S_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fmadd.s" => true
  | "fmsub.s" => true
  | "fnmsub.s" => true
  | "fnmadd.s" => true
  | _ => false

def f_bin_rm_type_mnemonic_S_backwards (arg_ : String) : SailM f_bin_rm_op_S := do
  match arg_ with
  | "fadd.s" => (pure FADD_S)
  | "fsub.s" => (pure FSUB_S)
  | "fmul.s" => (pure FMUL_S)
  | "fdiv.s" => (pure FDIV_S)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_bin_rm_type_mnemonic_S_forwards_matches (arg_ : f_bin_rm_op_S) : Bool :=
  match arg_ with
  | FADD_S => true
  | FSUB_S => true
  | FMUL_S => true
  | FDIV_S => true
  | _ => false

def f_bin_rm_type_mnemonic_S_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fadd.s" => true
  | "fsub.s" => true
  | "fmul.s" => true
  | "fdiv.s" => true
  | _ => false

def f_un_rm_fx_type_mnemonic_S_backwards (arg_ : String) : SailM f_un_rm_fx_op_S := do
  match arg_ with
  | "fcvt.w.s" => (pure FCVT_W_S)
  | "fcvt.wu.s" => (pure FCVT_WU_S)
  | "fcvt.l.s" => (pure FCVT_L_S)
  | "fcvt.lu.s" => (pure FCVT_LU_S)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_un_rm_fx_type_mnemonic_S_forwards_matches (arg_ : f_un_rm_fx_op_S) : Bool :=
  match arg_ with
  | FCVT_W_S => true
  | FCVT_WU_S => true
  | FCVT_L_S => true
  | FCVT_LU_S => true
  | _ => false

def f_un_rm_fx_type_mnemonic_S_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fcvt.w.s" => true
  | "fcvt.wu.s" => true
  | "fcvt.l.s" => true
  | "fcvt.lu.s" => true
  | _ => false

def f_un_rm_xf_type_mnemonic_S_backwards (arg_ : String) : SailM f_un_rm_xf_op_S := do
  match arg_ with
  | "fcvt.s.w" => (pure FCVT_S_W)
  | "fcvt.s.wu" => (pure FCVT_S_WU)
  | "fcvt.s.l" => (pure FCVT_S_L)
  | "fcvt.s.lu" => (pure FCVT_S_LU)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_un_rm_xf_type_mnemonic_S_forwards_matches (arg_ : f_un_rm_xf_op_S) : Bool :=
  match arg_ with
  | FCVT_S_W => true
  | FCVT_S_WU => true
  | FCVT_S_L => true
  | FCVT_S_LU => true
  | _ => false

def f_un_rm_xf_type_mnemonic_S_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fcvt.s.w" => true
  | "fcvt.s.wu" => true
  | "fcvt.s.l" => true
  | "fcvt.s.lu" => true
  | _ => false

def f_bin_type_mnemonic_f_S_backwards (arg_ : String) : SailM f_bin_op_f_S := do
  match arg_ with
  | "fsgnj.s" => (pure FSGNJ_S)
  | "fsgnjn.s" => (pure FSGNJN_S)
  | "fsgnjx.s" => (pure FSGNJX_S)
  | "fmin.s" => (pure FMIN_S)
  | "fmax.s" => (pure FMAX_S)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_bin_type_mnemonic_f_S_forwards_matches (arg_ : f_bin_op_f_S) : Bool :=
  match arg_ with
  | FSGNJ_S => true
  | FSGNJN_S => true
  | FSGNJX_S => true
  | FMIN_S => true
  | FMAX_S => true
  | _ => false

def f_bin_type_mnemonic_f_S_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fsgnj.s" => true
  | "fsgnjn.s" => true
  | "fsgnjx.s" => true
  | "fmin.s" => true
  | "fmax.s" => true
  | _ => false

def f_bin_type_mnemonic_x_S_backwards (arg_ : String) : SailM f_bin_op_x_S := do
  match arg_ with
  | "feq.s" => (pure FEQ_S)
  | "flt.s" => (pure FLT_S)
  | "fle.s" => (pure FLE_S)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_bin_type_mnemonic_x_S_forwards_matches (arg_ : f_bin_op_x_S) : Bool :=
  match arg_ with
  | FEQ_S => true
  | FLT_S => true
  | FLE_S => true
  | _ => false

def f_bin_type_mnemonic_x_S_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "feq.s" => true
  | "flt.s" => true
  | "fle.s" => true
  | _ => false

def f_un_type_mnemonic_x_S_backwards (arg_ : String) : SailM f_un_op_x_S := do
  match arg_ with
  | "fclass.s" => (pure FCLASS_S)
  | "fmv.x.w" => (pure FMV_X_W)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_un_type_mnemonic_x_S_forwards_matches (arg_ : f_un_op_x_S) : Bool :=
  match arg_ with
  | FCLASS_S => true
  | FMV_X_W => true
  | _ => false

def f_un_type_mnemonic_x_S_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fclass.s" => true
  | "fmv.x.w" => true
  | _ => false

def f_un_type_mnemonic_f_S_backwards (arg_ : String) : SailM f_un_op_f_S := do
  match arg_ with
  | "fmv.w.x" => (pure FMV_W_X)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_un_type_mnemonic_f_S_forwards_matches (arg_ : f_un_op_f_S) : Bool :=
  match arg_ with
  | FMV_W_X => true
  | _ => false

def f_un_type_mnemonic_f_S_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fmv.w.x" => true
  | _ => false

