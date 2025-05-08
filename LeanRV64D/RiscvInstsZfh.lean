import LeanRV64D.RiscvInstsZbs

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

def fsplit_H (xf16 : (BitVec 16)) : ((BitVec 1) × (BitVec 5) × (BitVec 10)) :=
  ((Sail.BitVec.extractLsb xf16 15 15), (Sail.BitVec.extractLsb xf16 14 10), (Sail.BitVec.extractLsb
    xf16 9 0))

def fmake_H (sign : (BitVec 1)) (exp : (BitVec 5)) (mant : (BitVec 10)) : (BitVec 16) :=
  (sign ++ (exp ++ mant))

def negate_H (xf16 : (BitVec 16)) : (BitVec 16) :=
  let (sign, exp, mant) := (fsplit_H xf16)
  let new_sign :=
    bif (sign == (0b0 : (BitVec 1)))
    then (0b1 : (BitVec 1))
    else (0b0 : (BitVec 1))
  (fmake_H new_sign exp mant)

def f_is_neg_inf_H (xf16 : (BitVec 16)) : Bool :=
  let (sign, exp, mant) := (fsplit_H xf16)
  ((sign == (0b1 : (BitVec 1))) && ((exp == (ones (n := 5))) && (mant == (zeros (n := 10)))))

def f_is_neg_norm_H (xf16 : (BitVec 16)) : Bool :=
  let (sign, exp, mant) := (fsplit_H xf16)
  ((sign == (0b1 : (BitVec 1))) && ((exp != (zeros (n := 5))) && (exp != (ones (n := 5)))))

def f_is_neg_subnorm_H (xf16 : (BitVec 16)) : Bool :=
  let (sign, exp, mant) := (fsplit_H xf16)
  ((sign == (0b1 : (BitVec 1))) && ((exp == (zeros (n := 5))) && (mant != (zeros (n := 10)))))

def f_is_pos_subnorm_H (xf16 : (BitVec 16)) : Bool :=
  let (sign, exp, mant) := (fsplit_H xf16)
  ((sign == (zeros (n := 1))) && ((exp == (zeros (n := 5))) && (mant != (zeros (n := 10)))))

def f_is_pos_norm_H (xf16 : (BitVec 16)) : Bool :=
  let (sign, exp, mant) := (fsplit_H xf16)
  ((sign == (zeros (n := 1))) && ((exp != (zeros (n := 5))) && (exp != (ones (n := 5)))))

def f_is_pos_inf_H (xf16 : (BitVec 16)) : Bool :=
  let (sign, exp, mant) := (fsplit_H xf16)
  ((sign == (zeros (n := 1))) && ((exp == (ones (n := 5))) && (mant == (zeros (n := 10)))))

def f_is_neg_zero_H (xf16 : (BitVec 16)) : Bool :=
  let (sign, exp, mant) := (fsplit_H xf16)
  ((sign == (ones (n := 1))) && ((exp == (zeros (n := 5))) && (mant == (zeros (n := 10)))))

def f_is_pos_zero_H (xf16 : (BitVec 16)) : Bool :=
  let (sign, exp, mant) := (fsplit_H xf16)
  ((sign == (zeros (n := 1))) && ((exp == (zeros (n := 5))) && (mant == (zeros (n := 10)))))

def f_is_SNaN_H (xf16 : (BitVec 16)) : Bool :=
  let (sign, exp, mant) := (fsplit_H xf16)
  ((exp == (ones (n := 5))) && (((BitVec.access mant 9) == 0#1) && (mant != (zeros (n := 10)))))

def f_is_QNaN_H (xf16 : (BitVec 16)) : Bool :=
  let (sign, exp, mant) := (fsplit_H xf16)
  ((exp == (ones (n := 5))) && ((BitVec.access mant 9) == 1#1))

def f_is_NaN_H (xf16 : (BitVec 16)) : Bool :=
  let (sign, exp, mant) := (fsplit_H xf16)
  ((exp == (ones (n := 5))) && (mant != (zeros (n := 10))))

/-- Type quantifiers: k_ex299405# : Bool -/
def fle_H (v1 : (BitVec 16)) (v2 : (BitVec 16)) (is_quiet : Bool) : (Bool × (BitVec 5)) :=
  let (s1, e1, m1) := (fsplit_H v1)
  let (s2, e2, m2) := (fsplit_H v2)
  let v1Is0 := ((f_is_neg_zero_H v1) || (f_is_pos_zero_H v1))
  let v2Is0 := ((f_is_neg_zero_H v2) || (f_is_pos_zero_H v2))
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
      (bif ((f_is_SNaN_H v1) || (f_is_SNaN_H v2))
      then (nvFlag ())
      else (zeros (n := 5)))
    else
      (bif ((f_is_NaN_H v1) || (f_is_NaN_H v2))
      then (nvFlag ())
      else (zeros (n := 5)))
  (result, fflags)

def haveHalfFPU (_ : Unit) : SailM Bool := do
  (pure ((← (currentlyEnabled Ext_Zfh)) || (← (currentlyEnabled Ext_Zhinx))))

def haveHalfMin (_ : Unit) : SailM Bool := do
  (pure ((← (haveHalfFPU ())) || (← (currentlyEnabled Ext_Zfhmin))))

def f_bin_rm_type_mnemonic_H_backwards (arg_ : String) : SailM f_bin_rm_op_H := do
  match arg_ with
  | "fadd.h" => (pure FADD_H)
  | "fsub.h" => (pure FSUB_H)
  | "fmul.h" => (pure FMUL_H)
  | "fdiv.h" => (pure FDIV_H)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_bin_rm_type_mnemonic_H_forwards_matches (arg_ : f_bin_rm_op_H) : Bool :=
  match arg_ with
  | FADD_H => true
  | FSUB_H => true
  | FMUL_H => true
  | FDIV_H => true
  | _ => false

def f_bin_rm_type_mnemonic_H_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fadd.h" => true
  | "fsub.h" => true
  | "fmul.h" => true
  | "fdiv.h" => true
  | _ => false

def f_madd_type_mnemonic_H_backwards (arg_ : String) : SailM f_madd_op_H := do
  match arg_ with
  | "fmadd.h" => (pure FMADD_H)
  | "fmsub.h" => (pure FMSUB_H)
  | "fnmsub.h" => (pure FNMSUB_H)
  | "fnmadd.h" => (pure FNMADD_H)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_madd_type_mnemonic_H_forwards_matches (arg_ : f_madd_op_H) : Bool :=
  match arg_ with
  | FMADD_H => true
  | FMSUB_H => true
  | FNMSUB_H => true
  | FNMADD_H => true
  | _ => false

def f_madd_type_mnemonic_H_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fmadd.h" => true
  | "fmsub.h" => true
  | "fnmsub.h" => true
  | "fnmadd.h" => true
  | _ => false

def f_bin_f_type_mnemonic_H_backwards (arg_ : String) : SailM f_bin_f_op_H := do
  match arg_ with
  | "fsgnj.h" => (pure FSGNJ_H)
  | "fsgnjn.h" => (pure FSGNJN_H)
  | "fsgnjx.h" => (pure FSGNJX_H)
  | "fmin.h" => (pure FMIN_H)
  | "fmax.h" => (pure FMAX_H)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_bin_f_type_mnemonic_H_forwards_matches (arg_ : f_bin_f_op_H) : Bool :=
  match arg_ with
  | FSGNJ_H => true
  | FSGNJN_H => true
  | FSGNJX_H => true
  | FMIN_H => true
  | FMAX_H => true
  | _ => false

def f_bin_f_type_mnemonic_H_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fsgnj.h" => true
  | "fsgnjn.h" => true
  | "fsgnjx.h" => true
  | "fmin.h" => true
  | "fmax.h" => true
  | _ => false

def f_bin_x_type_mnemonic_H_backwards (arg_ : String) : SailM f_bin_x_op_H := do
  match arg_ with
  | "feq.h" => (pure FEQ_H)
  | "flt.h" => (pure FLT_H)
  | "fle.h" => (pure FLE_H)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_bin_x_type_mnemonic_H_forwards_matches (arg_ : f_bin_x_op_H) : Bool :=
  match arg_ with
  | FEQ_H => true
  | FLT_H => true
  | FLE_H => true
  | _ => false

def f_bin_x_type_mnemonic_H_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "feq.h" => true
  | "flt.h" => true
  | "fle.h" => true
  | _ => false

def f_un_rm_ff_type_mnemonic_H_backwards (arg_ : String) : SailM f_un_rm_ff_op_H := do
  match arg_ with
  | "fsqrt.h" => (pure FSQRT_H)
  | "fcvt.h.s" => (pure FCVT_H_S)
  | "fcvt.h.d" => (pure FCVT_H_D)
  | "fcvt.s.h" => (pure FCVT_S_H)
  | "fcvt.d.h" => (pure FCVT_D_H)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_un_rm_ff_type_mnemonic_H_forwards_matches (arg_ : f_un_rm_ff_op_H) : Bool :=
  match arg_ with
  | FSQRT_H => true
  | FCVT_H_S => true
  | FCVT_H_D => true
  | FCVT_S_H => true
  | FCVT_D_H => true
  | _ => false

def f_un_rm_ff_type_mnemonic_H_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fsqrt.h" => true
  | "fcvt.h.s" => true
  | "fcvt.h.d" => true
  | "fcvt.s.h" => true
  | "fcvt.d.h" => true
  | _ => false

def f_un_rm_fx_type_mnemonic_H_backwards (arg_ : String) : SailM f_un_rm_fx_op_H := do
  match arg_ with
  | "fcvt.w.h" => (pure FCVT_W_H)
  | "fcvt.wu.h" => (pure FCVT_WU_H)
  | "fcvt.l.h" => (pure FCVT_L_H)
  | "fcvt.lu.h" => (pure FCVT_LU_H)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_un_rm_fx_type_mnemonic_H_forwards_matches (arg_ : f_un_rm_fx_op_H) : Bool :=
  match arg_ with
  | FCVT_W_H => true
  | FCVT_WU_H => true
  | FCVT_L_H => true
  | FCVT_LU_H => true
  | _ => false

def f_un_rm_fx_type_mnemonic_H_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fcvt.w.h" => true
  | "fcvt.wu.h" => true
  | "fcvt.l.h" => true
  | "fcvt.lu.h" => true
  | _ => false

def f_un_rm_xf_type_mnemonic_H_backwards (arg_ : String) : SailM f_un_rm_xf_op_H := do
  match arg_ with
  | "fcvt.h.w" => (pure FCVT_H_W)
  | "fcvt.h.wu" => (pure FCVT_H_WU)
  | "fcvt.h.l" => (pure FCVT_H_L)
  | "fcvt.h.lu" => (pure FCVT_H_LU)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_un_rm_xf_type_mnemonic_H_forwards_matches (arg_ : f_un_rm_xf_op_H) : Bool :=
  match arg_ with
  | FCVT_H_W => true
  | FCVT_H_WU => true
  | FCVT_H_L => true
  | FCVT_H_LU => true
  | _ => false

def f_un_rm_xf_type_mnemonic_H_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fcvt.h.w" => true
  | "fcvt.h.wu" => true
  | "fcvt.h.l" => true
  | "fcvt.h.lu" => true
  | _ => false

def f_un_f_type_mnemonic_H_backwards (arg_ : String) : SailM f_un_f_op_H := do
  match arg_ with
  | "fmv.h.x" => (pure FMV_H_X)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_un_f_type_mnemonic_H_forwards_matches (arg_ : f_un_f_op_H) : Bool :=
  match arg_ with
  | FMV_H_X => true
  | _ => false

def f_un_f_type_mnemonic_H_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fmv.h.x" => true
  | _ => false

def f_un_x_type_mnemonic_H_backwards (arg_ : String) : SailM f_un_x_op_H := do
  match arg_ with
  | "fmv.x.h" => (pure FMV_X_H)
  | "fclass.h" => (pure FCLASS_H)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def f_un_x_type_mnemonic_H_forwards_matches (arg_ : f_un_x_op_H) : Bool :=
  match arg_ with
  | FMV_X_H => true
  | FCLASS_H => true
  | _ => false

def f_un_x_type_mnemonic_H_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "fmv.x.h" => true
  | "fclass.h" => true
  | _ => false

