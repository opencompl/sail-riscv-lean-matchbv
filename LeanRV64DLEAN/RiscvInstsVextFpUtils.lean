import LeanRV64DLEAN.RiscvInstsVextUtils

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

/-- Type quantifiers: SEW : Nat, SEW ∈ {8, 16, 32, 64} -/
def valid_fp_op (SEW : Nat) (rm_3b : (BitVec 3)) : Bool :=
  let valid_sew := (Bool.and (SEW ≥b 16) (SEW ≤b 128))
  let valid_rm :=
    (not
      (Bool.or (BEq.beq rm_3b (0b101 : (BitVec 3)))
        (Bool.or (BEq.beq rm_3b (0b110 : (BitVec 3))) (BEq.beq rm_3b (0b111 : (BitVec 3))))))
  (Bool.and valid_sew valid_rm)

/-- Type quantifiers: SEW : Nat, SEW ∈ {8, 16, 32, 64} -/
def illegal_fp_normal (vd : vregidx) (vm : (BitVec 1)) (SEW : Nat) (rm_3b : (BitVec 3)) : SailM Bool := do
  (pure (Bool.or (not (← (valid_vtype ())))
      (Bool.or (not (valid_rd_mask vd vm)) (not (valid_fp_op SEW rm_3b)))))

/-- Type quantifiers: SEW : Nat, SEW ∈ {8, 16, 32, 64} -/
def illegal_fp_vd_masked (vd : vregidx) (SEW : Nat) (rm_3b : (BitVec 3)) : SailM Bool := do
  (pure (Bool.or (not (← (valid_vtype ())))
      (Bool.or (BEq.beq vd zvreg) (not (valid_fp_op SEW rm_3b)))))

/-- Type quantifiers: SEW : Nat, SEW ∈ {8, 16, 32, 64} -/
def illegal_fp_vd_unmasked (SEW : Nat) (rm_3b : (BitVec 3)) : SailM Bool := do
  (pure (Bool.or (not (← (valid_vtype ()))) (not (valid_fp_op SEW rm_3b))))

/-- Type quantifiers: LMUL_pow_new : Int, SEW_new : Int, SEW : Nat, SEW ∈ {8, 16, 32, 64} -/
def illegal_fp_variable_width (vd : vregidx) (vm : (BitVec 1)) (SEW : Nat) (rm_3b : (BitVec 3)) (SEW_new : Int) (LMUL_pow_new : Int) : SailM Bool := do
  (pure (Bool.or (not (← (valid_vtype ())))
      (Bool.or (not (valid_rd_mask vd vm))
        (Bool.or (not (valid_fp_op SEW rm_3b)) (not (valid_eew_emul SEW_new LMUL_pow_new))))))

/-- Type quantifiers: SEW : Nat, SEW ∈ {8, 16, 32, 64} -/
def illegal_fp_reduction (SEW : Nat) (rm_3b : (BitVec 3)) : SailM Bool := do
  (pure (Bool.or (not (← (valid_vtype ())))
      (Bool.or (not (← (assert_vstart 0))) (not (valid_fp_op SEW rm_3b)))))

/-- Type quantifiers: LMUL_pow_widen : Int, SEW_widen : Int, SEW : Nat, SEW ∈ {8, 16, 32, 64} -/
def illegal_fp_reduction_widen (SEW : Nat) (rm_3b : (BitVec 3)) (SEW_widen : Int) (LMUL_pow_widen : Int) : SailM Bool := do
  (pure (Bool.or (not (← (valid_vtype ())))
      (Bool.or (not (← (assert_vstart 0)))
        (Bool.or (not (valid_fp_op SEW rm_3b)) (not (valid_eew_emul SEW_widen LMUL_pow_widen))))))

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def f_is_neg_inf (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_neg_inf_H xf)
  | 32 => (f_is_neg_inf_S xf)
  | _ => (f_is_neg_inf_D xf)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def f_is_neg_norm (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_neg_norm_H xf)
  | 32 => (f_is_neg_norm_S xf)
  | _ => (f_is_neg_norm_D xf)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def f_is_neg_subnorm (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_neg_subnorm_H xf)
  | 32 => (f_is_neg_subnorm_S xf)
  | _ => (f_is_neg_subnorm_D xf)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def f_is_neg_zero (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_neg_zero_H xf)
  | 32 => (f_is_neg_zero_S xf)
  | _ => (f_is_neg_zero_D xf)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def f_is_pos_zero (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_pos_zero_H xf)
  | 32 => (f_is_pos_zero_S xf)
  | _ => (f_is_pos_zero_D xf)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def f_is_pos_subnorm (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_pos_subnorm_H xf)
  | 32 => (f_is_pos_subnorm_S xf)
  | _ => (f_is_pos_subnorm_D xf)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def f_is_pos_norm (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_pos_norm_H xf)
  | 32 => (f_is_pos_norm_S xf)
  | _ => (f_is_pos_norm_D xf)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def f_is_pos_inf (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_pos_inf_H xf)
  | 32 => (f_is_pos_inf_S xf)
  | _ => (f_is_pos_inf_D xf)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def f_is_SNaN (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_SNaN_H xf)
  | 32 => (f_is_SNaN_S xf)
  | _ => (f_is_SNaN_D xf)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def f_is_QNaN (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_QNaN_H xf)
  | 32 => (f_is_QNaN_S xf)
  | _ => (f_is_QNaN_D xf)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def f_is_NaN (xf : (BitVec k_m)) : Bool :=
  match (Sail.BitVec.length xf) with
  | 16 => (f_is_NaN_H xf)
  | 32 => (f_is_NaN_S xf)
  | _ => (f_is_NaN_D xf)

/-- Type quantifiers: SEW : Nat, SEW ∈ {16, 32, 64} -/
def get_scalar_fp (rs1 : fregidx) (SEW : Nat) : SailM (BitVec SEW) := do
  assert (flen ≥b SEW) "invalid vector floating-point type width: FLEN < SEW"
  match SEW with
  | 16 => (rF_H rs1)
  | 32 => (rF_S rs1)
  | _ => (rF_D rs1)

def get_fp_rounding_mode (_ : Unit) : SailM rounding_mode := do
  (encdec_rounding_mode_backwards (_get_Fcsr_FRM (← readReg fcsr)))

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def negate_fp (xf : (BitVec k_m)) : (BitVec k_m) :=
  match (Sail.BitVec.length xf) with
  | 16 => (negate_H xf)
  | 32 => (negate_S xf)
  | _ => (negate_D xf)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def fp_add (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Add rm_3b op1 op2)
    | 32 => (riscv_f32Add rm_3b op1 op2)
    | _ => (riscv_f64Add rm_3b op1 op2) ) : SailM (bits_fflags × (BitVec k_m)) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def fp_sub (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Sub rm_3b op1 op2)
    | 32 => (riscv_f32Sub rm_3b op1 op2)
    | _ => (riscv_f64Sub rm_3b op1 op2) ) : SailM (bits_fflags × (BitVec k_m)) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def fp_min (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, op1_lt_op2) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Lt_quiet op1 op2)
    | 32 => (riscv_f32Lt_quiet op1 op2)
    | _ => (riscv_f64Lt_quiet op1 op2) ) : SailM (bits_fflags × Bool) )
  let result_val :=
    if (Bool.and (f_is_NaN op1) (f_is_NaN op2))
    then (canonical_NaN (n := (Sail.BitVec.length op2)))
    else
      if (f_is_NaN op1)
      then op2
      else
        if (f_is_NaN op2)
        then op1
        else
          if (Bool.and (f_is_neg_zero op1) (f_is_pos_zero op2))
          then op1
          else
            if (Bool.and (f_is_neg_zero op2) (f_is_pos_zero op1))
            then op2
            else
              if op1_lt_op2
              then op1
              else op2
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def fp_max (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, op1_lt_op2) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Lt_quiet op1 op2)
    | 32 => (riscv_f32Lt_quiet op1 op2)
    | _ => (riscv_f64Lt_quiet op1 op2) ) : SailM (bits_fflags × Bool) )
  let result_val :=
    if (Bool.and (f_is_NaN op1) (f_is_NaN op2))
    then (canonical_NaN (n := (Sail.BitVec.length op2)))
    else
      if (f_is_NaN op1)
      then op2
      else
        if (f_is_NaN op2)
        then op1
        else
          if (Bool.and (f_is_neg_zero op1) (f_is_pos_zero op2))
          then op2
          else
            if (Bool.and (f_is_neg_zero op2) (f_is_pos_zero op1))
            then op1
            else
              if op1_lt_op2
              then op2
              else op1
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def fp_eq (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM Bool := do
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Eq op1 op2)
    | 32 => (riscv_f32Eq op1 op2)
    | _ => (riscv_f64Eq op1 op2) ) : SailM (bits_fflags × Bool) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def fp_gt (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM Bool := do
  let (fflags, temp_val) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Le op1 op2)
    | 32 => (riscv_f32Le op1 op2)
    | _ => (riscv_f64Le op1 op2) ) : SailM (bits_fflags × Bool) )
  let result_val :=
    if (BEq.beq fflags (0b10000 : (BitVec 5)))
    then false
    else (not temp_val)
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def fp_ge (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM Bool := do
  let (fflags, temp_val) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Lt op1 op2)
    | 32 => (riscv_f32Lt op1 op2)
    | _ => (riscv_f64Lt op1 op2) ) : SailM (bits_fflags × Bool) )
  let result_val :=
    if (BEq.beq fflags (0b10000 : (BitVec 5)))
    then false
    else (not temp_val)
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def fp_lt (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM Bool := do
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Lt op1 op2)
    | 32 => (riscv_f32Lt op1 op2)
    | _ => (riscv_f64Lt op1 op2) ) : SailM (bits_fflags × Bool) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def fp_le (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM Bool := do
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Le op1 op2)
    | 32 => (riscv_f32Le op1 op2)
    | _ => (riscv_f64Le op1 op2) ) : SailM (bits_fflags × Bool) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def fp_mul (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Mul rm_3b op1 op2)
    | 32 => (riscv_f32Mul rm_3b op1 op2)
    | _ => (riscv_f64Mul rm_3b op1 op2) ) : SailM (bits_fflags × (BitVec k_m)) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def fp_div (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length op2) with
    | 16 => (riscv_f16Div rm_3b op1 op2)
    | 32 => (riscv_f32Div rm_3b op1 op2)
    | _ => (riscv_f64Div rm_3b op1 op2) ) : SailM (bits_fflags × (BitVec k_m)) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def fp_muladd (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) (opadd : (BitVec k_m)) : SailM (BitVec k_m) := do
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length opadd) with
    | 16 => (riscv_f16MulAdd rm_3b op1 op2 opadd)
    | 32 => (riscv_f32MulAdd rm_3b op1 op2 opadd)
    | _ => (riscv_f64MulAdd rm_3b op1 op2 opadd) ) : SailM (bits_fflags × (BitVec k_m)) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def fp_nmuladd (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) (opadd : (BitVec k_m)) : SailM (BitVec k_m) := do
  let op1 := (negate_fp op1)
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length opadd) with
    | 16 => (riscv_f16MulAdd rm_3b op1 op2 opadd)
    | 32 => (riscv_f32MulAdd rm_3b op1 op2 opadd)
    | _ => (riscv_f64MulAdd rm_3b op1 op2 opadd) ) : SailM (bits_fflags × (BitVec k_m)) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def fp_mulsub (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) (opsub : (BitVec k_m)) : SailM (BitVec k_m) := do
  let opsub := (negate_fp opsub)
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length opsub) with
    | 16 => (riscv_f16MulAdd rm_3b op1 op2 opsub)
    | 32 => (riscv_f32MulAdd rm_3b op1 op2 opsub)
    | _ => (riscv_f64MulAdd rm_3b op1 op2 opsub) ) : SailM (bits_fflags × (BitVec k_m)) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def fp_nmulsub (rm_3b : (BitVec 3)) (op1 : (BitVec k_m)) (op2 : (BitVec k_m)) (opsub : (BitVec k_m)) : SailM (BitVec k_m) := do
  let opsub := (negate_fp opsub)
  let op1 := (negate_fp op1)
  let (fflags, result_val) ← (( do
    match (Sail.BitVec.length opsub) with
    | 16 => (riscv_f16MulAdd rm_3b op1 op2 opsub)
    | 32 => (riscv_f32MulAdd rm_3b op1 op2 opsub)
    | _ => (riscv_f64MulAdd rm_3b op1 op2 opsub) ) : SailM (bits_fflags × (BitVec k_m)) )
  (accrue_fflags fflags)
  (pure result_val)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32, 64} -/
def fp_class (xf : (BitVec k_m)) : (BitVec k_m) :=
  let result_val_10b : (BitVec 10) :=
    if (f_is_neg_inf xf)
    then (0b0000000001 : (BitVec 10))
    else
      if (f_is_neg_norm xf)
      then (0b0000000010 : (BitVec 10))
      else
        if (f_is_neg_subnorm xf)
        then (0b0000000100 : (BitVec 10))
        else
          if (f_is_neg_zero xf)
          then (0b0000001000 : (BitVec 10))
          else
            if (f_is_pos_zero xf)
            then (0b0000010000 : (BitVec 10))
            else
              if (f_is_pos_subnorm xf)
              then (0b0000100000 : (BitVec 10))
              else
                if (f_is_pos_norm xf)
                then (0b0001000000 : (BitVec 10))
                else
                  if (f_is_pos_inf xf)
                  then (0b0010000000 : (BitVec 10))
                  else
                    if (f_is_SNaN xf)
                    then (0b0100000000 : (BitVec 10))
                    else
                      if (f_is_QNaN xf)
                      then (0b1000000000 : (BitVec 10))
                      else (zeros_implicit (n := 10))
  (zero_extend (m := (Sail.BitVec.length xf)) result_val_10b)

/-- Type quantifiers: k_m : Nat, k_m ∈ {16, 32} -/
def fp_widen (nval : (BitVec k_m)) : SailM (BitVec (k_m * 2)) := do
  let rm_3b ← do (pure (_get_Fcsr_FRM (← readReg fcsr)))
  let (fflags, wval) ← (( do
    match (Sail.BitVec.length nval) with
    | 16 => (riscv_f16ToF32 rm_3b nval)
    | _ => (riscv_f32ToF64 rm_3b nval) ) : SailM (bits_fflags × (BitVec (k_m * 2))) )
  (accrue_fflags fflags)
  (pure wval)

def riscv_f16ToI16 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let (_, sig32) ← do (riscv_f16ToI32 rm v)
  if ((BitVec.toInt sig32) >b (BitVec.toInt ((0b0 : (BitVec 1)) ++ (ones (n := 15)))))
  then
    let t__3779 := (nvFlag ())
    let t__3780 := ((0b0 : (BitVec 1)) ++ (ones (n := 15)))
    (pure (t__3779, t__3780))
  else
    if ((BitVec.toInt sig32) <b (BitVec.toInt ((0b1 : (BitVec 1)) ++ (zeros_implicit (n := 15)))))
    then
      let t__3777 := (nvFlag ())
      let t__3778 := ((0b1 : (BitVec 1)) ++ (zeros_implicit (n := 15)))
      (pure (t__3777, t__3778))
    else
      let t__3775 := (zeros_implicit (n := 5))
      let t__3776 := (Sail.BitVec.extractLsb sig32 15 0)
      (pure (t__3775, t__3776))

def riscv_f16ToI8 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 8)) := do
  let (_, sig32) ← do (riscv_f16ToI32 rm v)
  if ((BitVec.toInt sig32) >b (BitVec.toInt ((0b0 : (BitVec 1)) ++ (ones (n := 7)))))
  then
    let t__3771 := (nvFlag ())
    let t__3772 := ((0b0 : (BitVec 1)) ++ (ones (n := 7)))
    (pure (t__3771, t__3772))
  else
    if ((BitVec.toInt sig32) <b (BitVec.toInt ((0b1 : (BitVec 1)) ++ (zeros_implicit (n := 7)))))
    then
      let t__3769 := (nvFlag ())
      let t__3770 := ((0b1 : (BitVec 1)) ++ (zeros_implicit (n := 7)))
      (pure (t__3769, t__3770))
    else
      let t__3767 := (zeros_implicit (n := 5))
      let t__3768 := (Sail.BitVec.extractLsb sig32 7 0)
      (pure (t__3767, t__3768))

def riscv_f32ToI16 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let (_, sig32) ← do (riscv_f32ToI32 rm v)
  if ((BitVec.toInt sig32) >b (BitVec.toInt ((0b0 : (BitVec 1)) ++ (ones (n := 15)))))
  then
    let t__3763 := (nvFlag ())
    let t__3764 := ((0b0 : (BitVec 1)) ++ (ones (n := 15)))
    (pure (t__3763, t__3764))
  else
    if ((BitVec.toInt sig32) <b (BitVec.toInt ((0b1 : (BitVec 1)) ++ (zeros_implicit (n := 15)))))
    then
      let t__3761 := (nvFlag ())
      let t__3762 := ((0b1 : (BitVec 1)) ++ (zeros_implicit (n := 15)))
      (pure (t__3761, t__3762))
    else
      let t__3759 := (zeros_implicit (n := 5))
      let t__3760 := (Sail.BitVec.extractLsb sig32 15 0)
      (pure (t__3759, t__3760))

def riscv_f16ToUi16 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let (_, sig32) ← do (riscv_f16ToUi32 rm v)
  if ((BitVec.toNat sig32) >b (BitVec.toNat (ones (n := 16))))
  then
    let t__3755 := (nvFlag ())
    let t__3756 := (ones (n := 16))
    (pure (t__3755, t__3756))
  else
    let t__3753 := (zeros_implicit (n := 5))
    let t__3754 := (Sail.BitVec.extractLsb sig32 15 0)
    (pure (t__3753, t__3754))

def riscv_f16ToUi8 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 8)) := do
  let (_, sig32) ← do (riscv_f16ToUi32 rm v)
  if ((BitVec.toNat sig32) >b (BitVec.toNat (ones (n := 8))))
  then
    let t__3750 := (nvFlag ())
    let t__3751 := (ones (n := 8))
    (pure (t__3750, t__3751))
  else
    let t__3748 := (zeros_implicit (n := 5))
    let t__3749 := (Sail.BitVec.extractLsb sig32 7 0)
    (pure (t__3748, t__3749))

def riscv_f32ToUi16 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let (_, sig32) ← do (riscv_f32ToUi32 rm v)
  if ((BitVec.toNat sig32) >b (BitVec.toNat (ones (n := 16))))
  then
    let t__3745 := (nvFlag ())
    let t__3746 := (ones (n := 16))
    (pure (t__3745, t__3746))
  else
    let t__3743 := (zeros_implicit (n := 5))
    let t__3744 := (Sail.BitVec.extractLsb sig32 15 0)
    (pure (t__3743, t__3744))

/-- Type quantifiers: k_ex316110# : Bool, k_m : Nat, k_m ∈ {16, 32, 64} -/
def rsqrt7 (v : (BitVec k_m)) (sub : Bool) : SailM (BitVec 64) := do
  let (sig, exp, sign, e, s) : ((BitVec 64) × (BitVec 64) × (BitVec 1) × Nat × Nat) :=
    match (Sail.BitVec.length v) with
    | 16 =>
      let t__3727 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 9 0))
      let t__3728 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 14 10))
      let t__3729 := (BitVec.join1 [(BitVec.access v 15)])
      (t__3727, t__3728, t__3729, 5, 10)
    | 32 =>
      let t__3732 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 22 0))
      let t__3733 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 30 23))
      let t__3734 := (BitVec.join1 [(BitVec.access v 31)])
      (t__3732, t__3733, t__3734, 8, 23)
    | _ =>
      let t__3737 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 51 0))
      let t__3738 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 62 52))
      let t__3739 := (BitVec.join1 [(BitVec.access v 63)])
      (t__3737, t__3738, t__3739, 11, 52)
  assert (Bool.or (Bool.and (BEq.beq s 10) (BEq.beq e 5))
    (Bool.or (Bool.and (BEq.beq s 23) (BEq.beq e 8)) (Bool.and (BEq.beq s 52) (BEq.beq e 11)))) "riscv_insts_vext_fp_utils.sail:458.64-458.65"
  let table : (Vector Int 128) :=
    #v[53, 54, 55, 56, 56, 57, 58, 59, 59, 60, 61, 62, 63, 63, 64, 65, 66, 67, 68, 69, 70, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 88, 90, 91, 92, 93, 95, 96, 97, 99, 100, 102, 103, 105, 106, 108, 109, 111, 113, 114, 116, 118, 119, 121, 123, 125, 127, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 6, 6, 7, 7, 8, 9, 9, 10, 10, 11, 12, 12, 13, 14, 14, 15, 16, 16, 17, 18, 19, 19, 20, 21, 22, 23, 23, 24, 25, 26, 27, 28, 29, 30, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 43, 44, 46, 47, 48, 50, 51, 52]
  let (normalized_exp, normalized_sig) ← do
    if sub
    then
      let nr_leadingzeros ← do (count_leadingzeros sig s)
      assert (nr_leadingzeros ≥b 0) "riscv_insts_vext_fp_utils.sail:480.35-480.36"
      let t__3725 := (to_bits 64 (0 -i nr_leadingzeros))
      let t__3726 :=
        (zero_extend (m := 64)
          (shiftl (Sail.BitVec.extractLsb sig (s -i 1) 0) (1 +i nr_leadingzeros)))
      (pure (t__3725, t__3726))
    else (pure (exp, sig))
  let idx : Nat :=
    match (Sail.BitVec.length v) with
    | 16 =>
      (BitVec.toNat
        ((BitVec.join1 [(BitVec.access normalized_exp 0)]) ++ (Sail.BitVec.extractLsb normalized_sig
            9 4)))
    | 32 =>
      (BitVec.toNat
        ((BitVec.join1 [(BitVec.access normalized_exp 0)]) ++ (Sail.BitVec.extractLsb normalized_sig
            22 17)))
    | _ =>
      (BitVec.toNat
        ((BitVec.join1 [(BitVec.access normalized_exp 0)]) ++ (Sail.BitVec.extractLsb normalized_sig
            51 46)))
  assert (Bool.and (idx ≥b 0) (idx <b 128)) "riscv_insts_vext_fp_utils.sail:491.29-491.30"
  let out_sig := (shiftl (to_bits s (GetElem?.getElem! table (127 -i idx))) (s -i 7))
  let out_exp :=
    (to_bits e (Int.tdiv (((3 *i ((2 ^i (e -i 1)) -i 1)) -i 1) -i (BitVec.toInt normalized_exp)) 2))
  (pure (zero_extend (m := 64) (sign ++ (out_exp ++ out_sig))))

def riscv_f16Rsqrte7 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let b__0 := (fp_class v)
  if (BEq.beq b__0 (0x0001 : (BitVec 16)))
  then
    let t__3723 := (nvFlag ())
    let t__3724 := (0x7E00 : (BitVec 16))
    (pure (t__3723, t__3724))
  else
    if (BEq.beq b__0 (0x0002 : (BitVec 16)))
    then
      let t__3721 := (nvFlag ())
      let t__3722 := (0x7E00 : (BitVec 16))
      (pure (t__3721, t__3722))
    else
      if (BEq.beq b__0 (0x0004 : (BitVec 16)))
      then
        let t__3719 := (nvFlag ())
        let t__3720 := (0x7E00 : (BitVec 16))
        (pure (t__3719, t__3720))
      else
        if (BEq.beq b__0 (0x0100 : (BitVec 16)))
        then
          let t__3717 := (nvFlag ())
          let t__3718 := (0x7E00 : (BitVec 16))
          (pure (t__3717, t__3718))
        else
          if (BEq.beq b__0 (0x0200 : (BitVec 16)))
          then
            let t__3715 := (zeros_implicit (n := 5))
            let t__3716 := (0x7E00 : (BitVec 16))
            (pure (t__3715, t__3716))
          else
            if (BEq.beq b__0 (0x0008 : (BitVec 16)))
            then
              let t__3713 := (dzFlag ())
              let t__3714 := (0xFC00 : (BitVec 16))
              (pure (t__3713, t__3714))
            else
              if (BEq.beq b__0 (0x0010 : (BitVec 16)))
              then
                let t__3711 := (dzFlag ())
                let t__3712 := (0x7C00 : (BitVec 16))
                (pure (t__3711, t__3712))
              else
                if (BEq.beq b__0 (0x0080 : (BitVec 16)))
                then
                  let t__3709 := (zeros_implicit (n := 5))
                  let t__3710 := (0x0000 : (BitVec 16))
                  (pure (t__3709, t__3710))
                else
                  if (BEq.beq b__0 (0x0020 : (BitVec 16)))
                  then
                    let t__3707 := (zeros_implicit (n := 5))
                    let t__3708 ← do (pure (Sail.BitVec.extractLsb (← (rsqrt7 v true)) 15 0))
                    (pure (t__3707, t__3708))
                  else
                    let t__3705 := (zeros_implicit (n := 5))
                    let t__3706 ← do (pure (Sail.BitVec.extractLsb (← (rsqrt7 v false)) 15 0))
                    (pure (t__3705, t__3706))

def riscv_f32Rsqrte7 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let b__0 := (Sail.BitVec.extractLsb (fp_class v) 15 0)
  if (BEq.beq b__0 (0x0001 : (BitVec 16)))
  then
    let t__3694 := (nvFlag ())
    let t__3695 := (0x7FC00000 : (BitVec 32))
    (pure (t__3694, t__3695))
  else
    if (BEq.beq b__0 (0x0002 : (BitVec 16)))
    then
      let t__3692 := (nvFlag ())
      let t__3693 := (0x7FC00000 : (BitVec 32))
      (pure (t__3692, t__3693))
    else
      if (BEq.beq b__0 (0x0004 : (BitVec 16)))
      then
        let t__3690 := (nvFlag ())
        let t__3691 := (0x7FC00000 : (BitVec 32))
        (pure (t__3690, t__3691))
      else
        if (BEq.beq b__0 (0x0100 : (BitVec 16)))
        then
          let t__3688 := (nvFlag ())
          let t__3689 := (0x7FC00000 : (BitVec 32))
          (pure (t__3688, t__3689))
        else
          if (BEq.beq b__0 (0x0200 : (BitVec 16)))
          then
            let t__3686 := (zeros_implicit (n := 5))
            let t__3687 := (0x7FC00000 : (BitVec 32))
            (pure (t__3686, t__3687))
          else
            if (BEq.beq b__0 (0x0008 : (BitVec 16)))
            then
              let t__3684 := (dzFlag ())
              let t__3685 := (0xFF800000 : (BitVec 32))
              (pure (t__3684, t__3685))
            else
              if (BEq.beq b__0 (0x0010 : (BitVec 16)))
              then
                let t__3682 := (dzFlag ())
                let t__3683 := (0x7F800000 : (BitVec 32))
                (pure (t__3682, t__3683))
              else
                if (BEq.beq b__0 (0x0080 : (BitVec 16)))
                then
                  let t__3680 := (zeros_implicit (n := 5))
                  let t__3681 := (0x00000000 : (BitVec 32))
                  (pure (t__3680, t__3681))
                else
                  if (BEq.beq b__0 (0x0020 : (BitVec 16)))
                  then
                    let t__3678 := (zeros_implicit (n := 5))
                    let t__3679 ← do (pure (Sail.BitVec.extractLsb (← (rsqrt7 v true)) 31 0))
                    (pure (t__3678, t__3679))
                  else
                    let t__3676 := (zeros_implicit (n := 5))
                    let t__3677 ← do (pure (Sail.BitVec.extractLsb (← (rsqrt7 v false)) 31 0))
                    (pure (t__3676, t__3677))

def riscv_f64Rsqrte7 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let b__0 := (Sail.BitVec.extractLsb (fp_class v) 15 0)
  if (BEq.beq b__0 (0x0001 : (BitVec 16)))
  then
    let t__3665 := (nvFlag ())
    let t__3666 := (0x7FF8000000000000 : (BitVec 64))
    (pure (t__3665, t__3666))
  else
    if (BEq.beq b__0 (0x0002 : (BitVec 16)))
    then
      let t__3663 := (nvFlag ())
      let t__3664 := (0x7FF8000000000000 : (BitVec 64))
      (pure (t__3663, t__3664))
    else
      if (BEq.beq b__0 (0x0004 : (BitVec 16)))
      then
        let t__3661 := (nvFlag ())
        let t__3662 := (0x7FF8000000000000 : (BitVec 64))
        (pure (t__3661, t__3662))
      else
        if (BEq.beq b__0 (0x0100 : (BitVec 16)))
        then
          let t__3659 := (nvFlag ())
          let t__3660 := (0x7FF8000000000000 : (BitVec 64))
          (pure (t__3659, t__3660))
        else
          if (BEq.beq b__0 (0x0200 : (BitVec 16)))
          then
            let t__3657 := (zeros_implicit (n := 5))
            let t__3658 := (0x7FF8000000000000 : (BitVec 64))
            (pure (t__3657, t__3658))
          else
            if (BEq.beq b__0 (0x0008 : (BitVec 16)))
            then
              let t__3655 := (dzFlag ())
              let t__3656 := (0xFFF0000000000000 : (BitVec 64))
              (pure (t__3655, t__3656))
            else
              if (BEq.beq b__0 (0x0010 : (BitVec 16)))
              then
                let t__3653 := (dzFlag ())
                let t__3654 := (0x7FF0000000000000 : (BitVec 64))
                (pure (t__3653, t__3654))
              else
                if (BEq.beq b__0 (0x0080 : (BitVec 16)))
                then
                  let t__3651 := (zeros_implicit (n := 5))
                  let t__3652 := (zeros_implicit (n := 64))
                  (pure (t__3651, t__3652))
                else
                  if (BEq.beq b__0 (0x0020 : (BitVec 16)))
                  then
                    let t__3649 := (zeros_implicit (n := 5))
                    let t__3650 ← do (pure (Sail.BitVec.extractLsb (← (rsqrt7 v true)) 63 0))
                    (pure (t__3649, t__3650))
                  else
                    let t__3647 := (zeros_implicit (n := 5))
                    let t__3648 ← do (pure (Sail.BitVec.extractLsb (← (rsqrt7 v false)) 63 0))
                    (pure (t__3647, t__3648))

/-- Type quantifiers: k_ex316349# : Bool, k_m : Nat, k_m ∈ {16, 32, 64} -/
def recip7 (v : (BitVec k_m)) (rm_3b : (BitVec 3)) (sub : Bool) : SailM (Bool × (BitVec 64)) := do
  let (sig, exp, sign, e, s) : ((BitVec 64) × (BitVec 64) × (BitVec 1) × Nat × Nat) :=
    match (Sail.BitVec.length v) with
    | 16 =>
      let t__3623 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 9 0))
      let t__3624 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 14 10))
      let t__3625 := (BitVec.join1 [(BitVec.access v 15)])
      (t__3623, t__3624, t__3625, 5, 10)
    | 32 =>
      let t__3628 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 22 0))
      let t__3629 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 30 23))
      let t__3630 := (BitVec.join1 [(BitVec.access v 31)])
      (t__3628, t__3629, t__3630, 8, 23)
    | _ =>
      let t__3633 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 51 0))
      let t__3634 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 62 52))
      let t__3635 := (BitVec.join1 [(BitVec.access v 63)])
      (t__3633, t__3634, t__3635, 11, 52)
  assert (Bool.or (Bool.and (BEq.beq s 10) (BEq.beq e 5))
    (Bool.or (Bool.and (BEq.beq s 23) (BEq.beq e 8)) (Bool.and (BEq.beq s 52) (BEq.beq e 11)))) "riscv_insts_vext_fp_utils.sail:552.64-552.65"
  let table : (Vector Int 128) :=
    #v[0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 7, 8, 8, 9, 9, 10, 11, 11, 12, 12, 13, 14, 14, 15, 15, 16, 17, 17, 18, 19, 19, 20, 21, 21, 22, 23, 23, 24, 25, 25, 26, 27, 28, 28, 29, 30, 31, 31, 32, 33, 34, 35, 35, 36, 37, 38, 39, 40, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 69, 70, 71, 72, 74, 75, 76, 77, 79, 80, 81, 83, 84, 85, 87, 88, 90, 91, 93, 94, 96, 97, 99, 100, 102, 104, 105, 107, 109, 110, 112, 114, 116, 117, 119, 121, 123, 125, 127]
  let nr_leadingzeros ← do (count_leadingzeros sig s)
  assert (nr_leadingzeros ≥b 0) "riscv_insts_vext_fp_utils.sail:572.29-572.30"
  let (normalized_exp, normalized_sig) :=
    if sub
    then
      let t__3621 := (to_bits 64 (0 -i nr_leadingzeros))
      let t__3622 :=
        (zero_extend (m := 64)
          (shiftl (Sail.BitVec.extractLsb sig (s -i 1) 0) (1 +i nr_leadingzeros)))
      (t__3621, t__3622)
    else (exp, sig)
  let idx : Nat :=
    match (Sail.BitVec.length v) with
    | 16 => (BitVec.toNat (Sail.BitVec.extractLsb normalized_sig 9 3))
    | 32 => (BitVec.toNat (Sail.BitVec.extractLsb normalized_sig 22 16))
    | _ => (BitVec.toNat (Sail.BitVec.extractLsb normalized_sig 51 45))
  assert (Bool.and (idx ≥b 0) (idx <b 128)) "riscv_insts_vext_fp_utils.sail:585.29-585.30"
  let mid_exp := (to_bits e (((2 *i ((2 ^i (e -i 1)) -i 1)) -i 1) -i (BitVec.toInt normalized_exp)))
  let mid_sig := (shiftl (to_bits s (GetElem?.getElem! table (127 -i idx))) (s -i 7))
  let (out_exp, out_sig) :=
    if (BEq.beq mid_exp (zeros_implicit (n := e)))
    then
      let t__3620 :=
        ((shiftr mid_sig 1) ||| ((0b1 : (BitVec 1)) ++ (zeros_implicit (n := (s -i 1)))))
      (mid_exp, t__3620)
    else
      if (BEq.beq mid_exp (ones (n := e)))
      then
        let t__3617 := (zeros_implicit (n := e))
        let t__3618 :=
          ((shiftr mid_sig 2) ||| ((0b01 : (BitVec 2)) ++ (zeros_implicit (n := (s -i 2)))))
        (t__3617, t__3618)
      else (mid_exp, mid_sig)
  if (Bool.and sub (nr_leadingzeros >b 1))
  then
    if (Bool.or (BEq.beq rm_3b (0b001 : (BitVec 3)))
         (Bool.or (Bool.and (BEq.beq rm_3b (0b010 : (BitVec 3))) (BEq.beq sign (0b0 : (BitVec 1))))
           (Bool.and (BEq.beq rm_3b (0b011 : (BitVec 3))) (BEq.beq sign (0b1 : (BitVec 1))))))
    then
      let t__3615 :=
        (zero_extend (m := 64)
          (sign ++ ((ones (n := (e -i 1))) ++ ((0b0 : (BitVec 1)) ++ (ones (n := s))))))
      (pure (true, t__3615))
    else
      let t__3613 :=
        (zero_extend (m := 64) (sign ++ ((ones (n := e)) ++ (zeros_implicit (n := s)))))
      (pure (true, t__3613))
  else
    let t__3610 := (zero_extend (m := 64) (sign ++ (out_exp ++ out_sig)))
    (pure (false, t__3610))

def riscv_f16Recip7 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let (round_abnormal_true, res_true) ← do (recip7 v rm true)
  let (round_abnormal_false, res_false) ← do (recip7 v rm false)
  let b__0 := (fp_class v)
  if (BEq.beq b__0 (0x0001 : (BitVec 16)))
  then
    let t__3606 := (zeros_implicit (n := 5))
    let t__3607 := (0x8000 : (BitVec 16))
    (pure (t__3606, t__3607))
  else
    if (BEq.beq b__0 (0x0080 : (BitVec 16)))
    then
      let t__3604 := (zeros_implicit (n := 5))
      let t__3605 := (0x0000 : (BitVec 16))
      (pure (t__3604, t__3605))
    else
      if (BEq.beq b__0 (0x0008 : (BitVec 16)))
      then
        let t__3602 := (dzFlag ())
        let t__3603 := (0xFC00 : (BitVec 16))
        (pure (t__3602, t__3603))
      else
        if (BEq.beq b__0 (0x0010 : (BitVec 16)))
        then
          let t__3600 := (dzFlag ())
          let t__3601 := (0x7C00 : (BitVec 16))
          (pure (t__3600, t__3601))
        else
          if (BEq.beq b__0 (0x0100 : (BitVec 16)))
          then
            let t__3598 := (nvFlag ())
            let t__3599 := (0x7E00 : (BitVec 16))
            (pure (t__3598, t__3599))
          else
            if (BEq.beq b__0 (0x0200 : (BitVec 16)))
            then
              let t__3596 := (zeros_implicit (n := 5))
              let t__3597 := (0x7E00 : (BitVec 16))
              (pure (t__3596, t__3597))
            else
              if (BEq.beq b__0 (0x0004 : (BitVec 16)))
              then
                if round_abnormal_true
                then
                  let t__3594 := ((nxFlag ()) ||| (ofFlag ()))
                  let t__3595 := (Sail.BitVec.extractLsb res_true 15 0)
                  (pure (t__3594, t__3595))
                else
                  let t__3592 := (zeros_implicit (n := 5))
                  let t__3593 := (Sail.BitVec.extractLsb res_true 15 0)
                  (pure (t__3592, t__3593))
              else
                if (BEq.beq b__0 (0x0020 : (BitVec 16)))
                then
                  if round_abnormal_true
                  then
                    let t__3589 := ((nxFlag ()) ||| (ofFlag ()))
                    let t__3590 := (Sail.BitVec.extractLsb res_true 15 0)
                    (pure (t__3589, t__3590))
                  else
                    let t__3587 := (zeros_implicit (n := 5))
                    let t__3588 := (Sail.BitVec.extractLsb res_true 15 0)
                    (pure (t__3587, t__3588))
                else
                  if round_abnormal_false
                  then
                    let t__3584 := ((nxFlag ()) ||| (ofFlag ()))
                    let t__3585 := (Sail.BitVec.extractLsb res_false 15 0)
                    (pure (t__3584, t__3585))
                  else
                    let t__3582 := (zeros_implicit (n := 5))
                    let t__3583 := (Sail.BitVec.extractLsb res_false 15 0)
                    (pure (t__3582, t__3583))

def riscv_f32Recip7 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let (round_abnormal_true, res_true) ← do (recip7 v rm true)
  let (round_abnormal_false, res_false) ← do (recip7 v rm false)
  let b__0 := (Sail.BitVec.extractLsb (fp_class v) 15 0)
  if (BEq.beq b__0 (0x0001 : (BitVec 16)))
  then
    let t__3571 := (zeros_implicit (n := 5))
    let t__3572 := (0x80000000 : (BitVec 32))
    (pure (t__3571, t__3572))
  else
    if (BEq.beq b__0 (0x0080 : (BitVec 16)))
    then
      let t__3569 := (zeros_implicit (n := 5))
      let t__3570 := (0x00000000 : (BitVec 32))
      (pure (t__3569, t__3570))
    else
      if (BEq.beq b__0 (0x0008 : (BitVec 16)))
      then
        let t__3567 := (dzFlag ())
        let t__3568 := (0xFF800000 : (BitVec 32))
        (pure (t__3567, t__3568))
      else
        if (BEq.beq b__0 (0x0010 : (BitVec 16)))
        then
          let t__3565 := (dzFlag ())
          let t__3566 := (0x7F800000 : (BitVec 32))
          (pure (t__3565, t__3566))
        else
          if (BEq.beq b__0 (0x0100 : (BitVec 16)))
          then
            let t__3563 := (nvFlag ())
            let t__3564 := (0x7FC00000 : (BitVec 32))
            (pure (t__3563, t__3564))
          else
            if (BEq.beq b__0 (0x0200 : (BitVec 16)))
            then
              let t__3561 := (zeros_implicit (n := 5))
              let t__3562 := (0x7FC00000 : (BitVec 32))
              (pure (t__3561, t__3562))
            else
              if (BEq.beq b__0 (0x0004 : (BitVec 16)))
              then
                if round_abnormal_true
                then
                  let t__3559 := ((nxFlag ()) ||| (ofFlag ()))
                  let t__3560 := (Sail.BitVec.extractLsb res_true 31 0)
                  (pure (t__3559, t__3560))
                else
                  let t__3557 := (zeros_implicit (n := 5))
                  let t__3558 := (Sail.BitVec.extractLsb res_true 31 0)
                  (pure (t__3557, t__3558))
              else
                if (BEq.beq b__0 (0x0020 : (BitVec 16)))
                then
                  if round_abnormal_true
                  then
                    let t__3554 := ((nxFlag ()) ||| (ofFlag ()))
                    let t__3555 := (Sail.BitVec.extractLsb res_true 31 0)
                    (pure (t__3554, t__3555))
                  else
                    let t__3552 := (zeros_implicit (n := 5))
                    let t__3553 := (Sail.BitVec.extractLsb res_true 31 0)
                    (pure (t__3552, t__3553))
                else
                  if round_abnormal_false
                  then
                    let t__3549 := ((nxFlag ()) ||| (ofFlag ()))
                    let t__3550 := (Sail.BitVec.extractLsb res_false 31 0)
                    (pure (t__3549, t__3550))
                  else
                    let t__3547 := (zeros_implicit (n := 5))
                    let t__3548 := (Sail.BitVec.extractLsb res_false 31 0)
                    (pure (t__3547, t__3548))

def riscv_f64Recip7 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let (round_abnormal_true, res_true) ← do (recip7 v rm true)
  let (round_abnormal_false, res_false) ← do (recip7 v rm false)
  let b__0 := (Sail.BitVec.extractLsb (fp_class v) 15 0)
  if (BEq.beq b__0 (0x0001 : (BitVec 16)))
  then
    let t__3536 := (zeros_implicit (n := 5))
    let t__3537 := (0x8000000000000000 : (BitVec 64))
    (pure (t__3536, t__3537))
  else
    if (BEq.beq b__0 (0x0080 : (BitVec 16)))
    then
      let t__3534 := (zeros_implicit (n := 5))
      let t__3535 := (0x0000000000000000 : (BitVec 64))
      (pure (t__3534, t__3535))
    else
      if (BEq.beq b__0 (0x0008 : (BitVec 16)))
      then
        let t__3532 := (dzFlag ())
        let t__3533 := (0xFFF0000000000000 : (BitVec 64))
        (pure (t__3532, t__3533))
      else
        if (BEq.beq b__0 (0x0010 : (BitVec 16)))
        then
          let t__3530 := (dzFlag ())
          let t__3531 := (0x7FF0000000000000 : (BitVec 64))
          (pure (t__3530, t__3531))
        else
          if (BEq.beq b__0 (0x0100 : (BitVec 16)))
          then
            let t__3528 := (nvFlag ())
            let t__3529 := (0x7FF8000000000000 : (BitVec 64))
            (pure (t__3528, t__3529))
          else
            if (BEq.beq b__0 (0x0200 : (BitVec 16)))
            then
              let t__3526 := (zeros_implicit (n := 5))
              let t__3527 := (0x7FF8000000000000 : (BitVec 64))
              (pure (t__3526, t__3527))
            else
              if (BEq.beq b__0 (0x0004 : (BitVec 16)))
              then
                if round_abnormal_true
                then
                  let t__3524 := ((nxFlag ()) ||| (ofFlag ()))
                  let t__3525 := (Sail.BitVec.extractLsb res_true 63 0)
                  (pure (t__3524, t__3525))
                else
                  let t__3522 := (zeros_implicit (n := 5))
                  let t__3523 := (Sail.BitVec.extractLsb res_true 63 0)
                  (pure (t__3522, t__3523))
              else
                if (BEq.beq b__0 (0x0020 : (BitVec 16)))
                then
                  if round_abnormal_true
                  then
                    let t__3519 := ((nxFlag ()) ||| (ofFlag ()))
                    let t__3520 := (Sail.BitVec.extractLsb res_true 63 0)
                    (pure (t__3519, t__3520))
                  else
                    let t__3517 := (zeros_implicit (n := 5))
                    let t__3518 := (Sail.BitVec.extractLsb res_true 63 0)
                    (pure (t__3517, t__3518))
                else
                  if round_abnormal_false
                  then
                    let t__3514 := ((nxFlag ()) ||| (ofFlag ()))
                    let t__3515 := (Sail.BitVec.extractLsb res_false 63 0)
                    (pure (t__3514, t__3515))
                  else
                    let t__3512 := (zeros_implicit (n := 5))
                    let t__3513 := (Sail.BitVec.extractLsb res_false 63 0)
                    (pure (t__3512, t__3513))

