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
    bif (Bool.and (f_is_NaN op1) (f_is_NaN op2))
    then (canonical_NaN (n := (Sail.BitVec.length op2)))
    else
      (bif (f_is_NaN op1)
      then op2
      else
        (bif (f_is_NaN op2)
        then op1
        else
          (bif (Bool.and (f_is_neg_zero op1) (f_is_pos_zero op2))
          then op1
          else
            (bif (Bool.and (f_is_neg_zero op2) (f_is_pos_zero op1))
            then op2
            else
              (bif op1_lt_op2
              then op1
              else op2)))))
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
    bif (Bool.and (f_is_NaN op1) (f_is_NaN op2))
    then (canonical_NaN (n := (Sail.BitVec.length op2)))
    else
      (bif (f_is_NaN op1)
      then op2
      else
        (bif (f_is_NaN op2)
        then op1
        else
          (bif (Bool.and (f_is_neg_zero op1) (f_is_pos_zero op2))
          then op2
          else
            (bif (Bool.and (f_is_neg_zero op2) (f_is_pos_zero op1))
            then op1
            else
              (bif op1_lt_op2
              then op2
              else op1)))))
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
    bif (BEq.beq fflags (0b10000 : (BitVec 5)))
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
    bif (BEq.beq fflags (0b10000 : (BitVec 5)))
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
    bif (f_is_neg_inf xf)
    then (0b0000000001 : (BitVec 10))
    else
      (bif (f_is_neg_norm xf)
      then (0b0000000010 : (BitVec 10))
      else
        (bif (f_is_neg_subnorm xf)
        then (0b0000000100 : (BitVec 10))
        else
          (bif (f_is_neg_zero xf)
          then (0b0000001000 : (BitVec 10))
          else
            (bif (f_is_pos_zero xf)
            then (0b0000010000 : (BitVec 10))
            else
              (bif (f_is_pos_subnorm xf)
              then (0b0000100000 : (BitVec 10))
              else
                (bif (f_is_pos_norm xf)
                then (0b0001000000 : (BitVec 10))
                else
                  (bif (f_is_pos_inf xf)
                  then (0b0010000000 : (BitVec 10))
                  else
                    (bif (f_is_SNaN xf)
                    then (0b0100000000 : (BitVec 10))
                    else
                      (bif (f_is_QNaN xf)
                      then (0b1000000000 : (BitVec 10))
                      else (zeros_implicit (n := 10)))))))))))
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
  bif ((BitVec.toInt sig32) >b (BitVec.toInt ((0b0 : (BitVec 1)) ++ (ones (n := 15)))))
  then
    (let t__3654 := (nvFlag ())
    let t__3655 := ((0b0 : (BitVec 1)) ++ (ones (n := 15)))
    (pure (t__3654, t__3655)))
  else
    (bif ((BitVec.toInt sig32) <b (BitVec.toInt ((0b1 : (BitVec 1)) ++ (zeros_implicit (n := 15)))))
    then
      (let t__3652 := (nvFlag ())
      let t__3653 := ((0b1 : (BitVec 1)) ++ (zeros_implicit (n := 15)))
      (pure (t__3652, t__3653)))
    else
      (let t__3650 := (zeros_implicit (n := 5))
      let t__3651 := (Sail.BitVec.extractLsb sig32 15 0)
      (pure (t__3650, t__3651))))

def riscv_f16ToI8 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 8)) := do
  let (_, sig32) ← do (riscv_f16ToI32 rm v)
  bif ((BitVec.toInt sig32) >b (BitVec.toInt ((0b0 : (BitVec 1)) ++ (ones (n := 7)))))
  then
    (let t__3646 := (nvFlag ())
    let t__3647 := ((0b0 : (BitVec 1)) ++ (ones (n := 7)))
    (pure (t__3646, t__3647)))
  else
    (bif ((BitVec.toInt sig32) <b (BitVec.toInt ((0b1 : (BitVec 1)) ++ (zeros_implicit (n := 7)))))
    then
      (let t__3644 := (nvFlag ())
      let t__3645 := ((0b1 : (BitVec 1)) ++ (zeros_implicit (n := 7)))
      (pure (t__3644, t__3645)))
    else
      (let t__3642 := (zeros_implicit (n := 5))
      let t__3643 := (Sail.BitVec.extractLsb sig32 7 0)
      (pure (t__3642, t__3643))))

def riscv_f32ToI16 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let (_, sig32) ← do (riscv_f32ToI32 rm v)
  bif ((BitVec.toInt sig32) >b (BitVec.toInt ((0b0 : (BitVec 1)) ++ (ones (n := 15)))))
  then
    (let t__3638 := (nvFlag ())
    let t__3639 := ((0b0 : (BitVec 1)) ++ (ones (n := 15)))
    (pure (t__3638, t__3639)))
  else
    (bif ((BitVec.toInt sig32) <b (BitVec.toInt ((0b1 : (BitVec 1)) ++ (zeros_implicit (n := 15)))))
    then
      (let t__3636 := (nvFlag ())
      let t__3637 := ((0b1 : (BitVec 1)) ++ (zeros_implicit (n := 15)))
      (pure (t__3636, t__3637)))
    else
      (let t__3634 := (zeros_implicit (n := 5))
      let t__3635 := (Sail.BitVec.extractLsb sig32 15 0)
      (pure (t__3634, t__3635))))

def riscv_f16ToUi16 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let (_, sig32) ← do (riscv_f16ToUi32 rm v)
  bif ((BitVec.toNat sig32) >b (BitVec.toNat (ones (n := 16))))
  then
    (let t__3630 := (nvFlag ())
    let t__3631 := (ones (n := 16))
    (pure (t__3630, t__3631)))
  else
    (let t__3628 := (zeros_implicit (n := 5))
    let t__3629 := (Sail.BitVec.extractLsb sig32 15 0)
    (pure (t__3628, t__3629)))

def riscv_f16ToUi8 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 8)) := do
  let (_, sig32) ← do (riscv_f16ToUi32 rm v)
  bif ((BitVec.toNat sig32) >b (BitVec.toNat (ones (n := 8))))
  then
    (let t__3625 := (nvFlag ())
    let t__3626 := (ones (n := 8))
    (pure (t__3625, t__3626)))
  else
    (let t__3623 := (zeros_implicit (n := 5))
    let t__3624 := (Sail.BitVec.extractLsb sig32 7 0)
    (pure (t__3623, t__3624)))

def riscv_f32ToUi16 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let (_, sig32) ← do (riscv_f32ToUi32 rm v)
  bif ((BitVec.toNat sig32) >b (BitVec.toNat (ones (n := 16))))
  then
    (let t__3620 := (nvFlag ())
    let t__3621 := (ones (n := 16))
    (pure (t__3620, t__3621)))
  else
    (let t__3618 := (zeros_implicit (n := 5))
    let t__3619 := (Sail.BitVec.extractLsb sig32 15 0)
    (pure (t__3618, t__3619)))

/-- Type quantifiers: k_ex319893# : Bool, k_m : Nat, k_m ∈ {16, 32, 64} -/
def rsqrt7 (v : (BitVec k_m)) (sub : Bool) : SailM (BitVec 64) := do
  let (sig, exp, sign, e, s) : ((BitVec 64) × (BitVec 64) × (BitVec 1) × Nat × Nat) :=
    match (Sail.BitVec.length v) with
    | 16 => (let t__3602 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 9 0))
      let t__3603 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 14 10))
      let t__3604 := (BitVec.join1 [(BitVec.access v 15)])
      (t__3602, t__3603, t__3604, 5, 10))
    | 32 => (let t__3607 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 22 0))
      let t__3608 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 30 23))
      let t__3609 := (BitVec.join1 [(BitVec.access v 31)])
      (t__3607, t__3608, t__3609, 8, 23))
    | _ => (let t__3612 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 51 0))
      let t__3613 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 62 52))
      let t__3614 := (BitVec.join1 [(BitVec.access v 63)])
      (t__3612, t__3613, t__3614, 11, 52))
  assert (Bool.or (Bool.and (BEq.beq s 10) (BEq.beq e 5))
    (Bool.or (Bool.and (BEq.beq s 23) (BEq.beq e 8)) (Bool.and (BEq.beq s 52) (BEq.beq e 11)))) "riscv_insts_vext_fp_utils.sail:458.64-458.65"
  let table : (Vector Int 128) :=
    #v[53, 54, 55, 56, 56, 57, 58, 59, 59, 60, 61, 62, 63, 63, 64, 65, 66, 67, 68, 69, 70, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 88, 90, 91, 92, 93, 95, 96, 97, 99, 100, 102, 103, 105, 106, 108, 109, 111, 113, 114, 116, 118, 119, 121, 123, 125, 127, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 6, 6, 7, 7, 8, 9, 9, 10, 10, 11, 12, 12, 13, 14, 14, 15, 16, 16, 17, 18, 19, 19, 20, 21, 22, 23, 23, 24, 25, 26, 27, 28, 29, 30, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 43, 44, 46, 47, 48, 50, 51, 52]
  let (normalized_exp, normalized_sig) ← do
    bif sub
    then
      (do
        let nr_leadingzeros ← do (count_leadingzeros sig s)
        assert (nr_leadingzeros ≥b 0) "riscv_insts_vext_fp_utils.sail:480.35-480.36"
        let t__3600 := (to_bits 64 (0 -i nr_leadingzeros))
        let t__3601 :=
          (zero_extend (m := 64)
            (shiftl (Sail.BitVec.extractLsb sig (s -i 1) 0) (1 +i nr_leadingzeros)))
        (pure (t__3600, t__3601)))
    else (pure (exp, sig))
  let idx : Nat :=
    match (Sail.BitVec.length v) with
    | 16 => (BitVec.toNat
        ((BitVec.join1 [(BitVec.access normalized_exp 0)]) ++ (Sail.BitVec.extractLsb normalized_sig
            9 4)))
    | 32 => (BitVec.toNat
        ((BitVec.join1 [(BitVec.access normalized_exp 0)]) ++ (Sail.BitVec.extractLsb normalized_sig
            22 17)))
    | _ => (BitVec.toNat
        ((BitVec.join1 [(BitVec.access normalized_exp 0)]) ++ (Sail.BitVec.extractLsb normalized_sig
            51 46)))
  assert (Bool.and (idx ≥b 0) (idx <b 128)) "riscv_insts_vext_fp_utils.sail:491.29-491.30"
  let out_sig := (shiftl (to_bits s (GetElem?.getElem! table (127 -i idx))) (s -i 7))
  let out_exp :=
    (to_bits e (Int.tdiv (((3 *i ((2 ^i (e -i 1)) -i 1)) -i 1) -i (BitVec.toInt normalized_exp)) 2))
  (pure (zero_extend (m := 64) (sign ++ (out_exp ++ out_sig))))

def riscv_f16Rsqrte7 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let b__0 := (fp_class v)
  bif (BEq.beq b__0 (0x0001 : (BitVec 16)))
  then
    (let t__3598 := (nvFlag ())
    let t__3599 := (0x7E00 : (BitVec 16))
    (pure (t__3598, t__3599)))
  else
    (do
      bif (BEq.beq b__0 (0x0002 : (BitVec 16)))
      then
        (let t__3596 := (nvFlag ())
        let t__3597 := (0x7E00 : (BitVec 16))
        (pure (t__3596, t__3597)))
      else
        (do
          bif (BEq.beq b__0 (0x0004 : (BitVec 16)))
          then
            (let t__3594 := (nvFlag ())
            let t__3595 := (0x7E00 : (BitVec 16))
            (pure (t__3594, t__3595)))
          else
            (do
              bif (BEq.beq b__0 (0x0100 : (BitVec 16)))
              then
                (let t__3592 := (nvFlag ())
                let t__3593 := (0x7E00 : (BitVec 16))
                (pure (t__3592, t__3593)))
              else
                (do
                  bif (BEq.beq b__0 (0x0200 : (BitVec 16)))
                  then
                    (let t__3590 := (zeros_implicit (n := 5))
                    let t__3591 := (0x7E00 : (BitVec 16))
                    (pure (t__3590, t__3591)))
                  else
                    (do
                      bif (BEq.beq b__0 (0x0008 : (BitVec 16)))
                      then
                        (let t__3588 := (dzFlag ())
                        let t__3589 := (0xFC00 : (BitVec 16))
                        (pure (t__3588, t__3589)))
                      else
                        (do
                          bif (BEq.beq b__0 (0x0010 : (BitVec 16)))
                          then
                            (let t__3586 := (dzFlag ())
                            let t__3587 := (0x7C00 : (BitVec 16))
                            (pure (t__3586, t__3587)))
                          else
                            (do
                              bif (BEq.beq b__0 (0x0080 : (BitVec 16)))
                              then
                                (let t__3584 := (zeros_implicit (n := 5))
                                let t__3585 := (0x0000 : (BitVec 16))
                                (pure (t__3584, t__3585)))
                              else
                                (do
                                  bif (BEq.beq b__0 (0x0020 : (BitVec 16)))
                                  then
                                    (do
                                      let t__3582 := (zeros_implicit (n := 5))
                                      let t__3583 ← do
                                        (pure (Sail.BitVec.extractLsb (← (rsqrt7 v true)) 15 0))
                                      (pure (t__3582, t__3583)))
                                  else
                                    (do
                                      let t__3580 := (zeros_implicit (n := 5))
                                      let t__3581 ← do
                                        (pure (Sail.BitVec.extractLsb (← (rsqrt7 v false)) 15 0))
                                      (pure (t__3580, t__3581)))))))))))

def riscv_f32Rsqrte7 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let b__0 := (Sail.BitVec.extractLsb (fp_class v) 15 0)
  bif (BEq.beq b__0 (0x0001 : (BitVec 16)))
  then
    (let t__3569 := (nvFlag ())
    let t__3570 := (0x7FC00000 : (BitVec 32))
    (pure (t__3569, t__3570)))
  else
    (do
      bif (BEq.beq b__0 (0x0002 : (BitVec 16)))
      then
        (let t__3567 := (nvFlag ())
        let t__3568 := (0x7FC00000 : (BitVec 32))
        (pure (t__3567, t__3568)))
      else
        (do
          bif (BEq.beq b__0 (0x0004 : (BitVec 16)))
          then
            (let t__3565 := (nvFlag ())
            let t__3566 := (0x7FC00000 : (BitVec 32))
            (pure (t__3565, t__3566)))
          else
            (do
              bif (BEq.beq b__0 (0x0100 : (BitVec 16)))
              then
                (let t__3563 := (nvFlag ())
                let t__3564 := (0x7FC00000 : (BitVec 32))
                (pure (t__3563, t__3564)))
              else
                (do
                  bif (BEq.beq b__0 (0x0200 : (BitVec 16)))
                  then
                    (let t__3561 := (zeros_implicit (n := 5))
                    let t__3562 := (0x7FC00000 : (BitVec 32))
                    (pure (t__3561, t__3562)))
                  else
                    (do
                      bif (BEq.beq b__0 (0x0008 : (BitVec 16)))
                      then
                        (let t__3559 := (dzFlag ())
                        let t__3560 := (0xFF800000 : (BitVec 32))
                        (pure (t__3559, t__3560)))
                      else
                        (do
                          bif (BEq.beq b__0 (0x0010 : (BitVec 16)))
                          then
                            (let t__3557 := (dzFlag ())
                            let t__3558 := (0x7F800000 : (BitVec 32))
                            (pure (t__3557, t__3558)))
                          else
                            (do
                              bif (BEq.beq b__0 (0x0080 : (BitVec 16)))
                              then
                                (let t__3555 := (zeros_implicit (n := 5))
                                let t__3556 := (0x00000000 : (BitVec 32))
                                (pure (t__3555, t__3556)))
                              else
                                (do
                                  bif (BEq.beq b__0 (0x0020 : (BitVec 16)))
                                  then
                                    (do
                                      let t__3553 := (zeros_implicit (n := 5))
                                      let t__3554 ← do
                                        (pure (Sail.BitVec.extractLsb (← (rsqrt7 v true)) 31 0))
                                      (pure (t__3553, t__3554)))
                                  else
                                    (do
                                      let t__3551 := (zeros_implicit (n := 5))
                                      let t__3552 ← do
                                        (pure (Sail.BitVec.extractLsb (← (rsqrt7 v false)) 31 0))
                                      (pure (t__3551, t__3552)))))))))))

def riscv_f64Rsqrte7 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let b__0 := (Sail.BitVec.extractLsb (fp_class v) 15 0)
  bif (BEq.beq b__0 (0x0001 : (BitVec 16)))
  then
    (let t__3540 := (nvFlag ())
    let t__3541 := (0x7FF8000000000000 : (BitVec 64))
    (pure (t__3540, t__3541)))
  else
    (do
      bif (BEq.beq b__0 (0x0002 : (BitVec 16)))
      then
        (let t__3538 := (nvFlag ())
        let t__3539 := (0x7FF8000000000000 : (BitVec 64))
        (pure (t__3538, t__3539)))
      else
        (do
          bif (BEq.beq b__0 (0x0004 : (BitVec 16)))
          then
            (let t__3536 := (nvFlag ())
            let t__3537 := (0x7FF8000000000000 : (BitVec 64))
            (pure (t__3536, t__3537)))
          else
            (do
              bif (BEq.beq b__0 (0x0100 : (BitVec 16)))
              then
                (let t__3534 := (nvFlag ())
                let t__3535 := (0x7FF8000000000000 : (BitVec 64))
                (pure (t__3534, t__3535)))
              else
                (do
                  bif (BEq.beq b__0 (0x0200 : (BitVec 16)))
                  then
                    (let t__3532 := (zeros_implicit (n := 5))
                    let t__3533 := (0x7FF8000000000000 : (BitVec 64))
                    (pure (t__3532, t__3533)))
                  else
                    (do
                      bif (BEq.beq b__0 (0x0008 : (BitVec 16)))
                      then
                        (let t__3530 := (dzFlag ())
                        let t__3531 := (0xFFF0000000000000 : (BitVec 64))
                        (pure (t__3530, t__3531)))
                      else
                        (do
                          bif (BEq.beq b__0 (0x0010 : (BitVec 16)))
                          then
                            (let t__3528 := (dzFlag ())
                            let t__3529 := (0x7FF0000000000000 : (BitVec 64))
                            (pure (t__3528, t__3529)))
                          else
                            (do
                              bif (BEq.beq b__0 (0x0080 : (BitVec 16)))
                              then
                                (let t__3526 := (zeros_implicit (n := 5))
                                let t__3527 := (zeros_implicit (n := 64))
                                (pure (t__3526, t__3527)))
                              else
                                (do
                                  bif (BEq.beq b__0 (0x0020 : (BitVec 16)))
                                  then
                                    (do
                                      let t__3524 := (zeros_implicit (n := 5))
                                      let t__3525 ← do
                                        (pure (Sail.BitVec.extractLsb (← (rsqrt7 v true)) 63 0))
                                      (pure (t__3524, t__3525)))
                                  else
                                    (do
                                      let t__3522 := (zeros_implicit (n := 5))
                                      let t__3523 ← do
                                        (pure (Sail.BitVec.extractLsb (← (rsqrt7 v false)) 63 0))
                                      (pure (t__3522, t__3523)))))))))))

/-- Type quantifiers: k_ex320132# : Bool, k_m : Nat, k_m ∈ {16, 32, 64} -/
def recip7 (v : (BitVec k_m)) (rm_3b : (BitVec 3)) (sub : Bool) : SailM (Bool × (BitVec 64)) := do
  let (sig, exp, sign, e, s) : ((BitVec 64) × (BitVec 64) × (BitVec 1) × Nat × Nat) :=
    match (Sail.BitVec.length v) with
    | 16 => (let t__3498 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 9 0))
      let t__3499 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 14 10))
      let t__3500 := (BitVec.join1 [(BitVec.access v 15)])
      (t__3498, t__3499, t__3500, 5, 10))
    | 32 => (let t__3503 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 22 0))
      let t__3504 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 30 23))
      let t__3505 := (BitVec.join1 [(BitVec.access v 31)])
      (t__3503, t__3504, t__3505, 8, 23))
    | _ => (let t__3508 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 51 0))
      let t__3509 := (zero_extend (m := 64) (Sail.BitVec.extractLsb v 62 52))
      let t__3510 := (BitVec.join1 [(BitVec.access v 63)])
      (t__3508, t__3509, t__3510, 11, 52))
  assert (Bool.or (Bool.and (BEq.beq s 10) (BEq.beq e 5))
    (Bool.or (Bool.and (BEq.beq s 23) (BEq.beq e 8)) (Bool.and (BEq.beq s 52) (BEq.beq e 11)))) "riscv_insts_vext_fp_utils.sail:552.64-552.65"
  let table : (Vector Int 128) :=
    #v[0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 7, 8, 8, 9, 9, 10, 11, 11, 12, 12, 13, 14, 14, 15, 15, 16, 17, 17, 18, 19, 19, 20, 21, 21, 22, 23, 23, 24, 25, 25, 26, 27, 28, 28, 29, 30, 31, 31, 32, 33, 34, 35, 35, 36, 37, 38, 39, 40, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 69, 70, 71, 72, 74, 75, 76, 77, 79, 80, 81, 83, 84, 85, 87, 88, 90, 91, 93, 94, 96, 97, 99, 100, 102, 104, 105, 107, 109, 110, 112, 114, 116, 117, 119, 121, 123, 125, 127]
  let nr_leadingzeros ← do (count_leadingzeros sig s)
  assert (nr_leadingzeros ≥b 0) "riscv_insts_vext_fp_utils.sail:572.29-572.30"
  let (normalized_exp, normalized_sig) :=
    bif sub
    then
      (let t__3496 := (to_bits 64 (0 -i nr_leadingzeros))
      let t__3497 :=
        (zero_extend (m := 64)
          (shiftl (Sail.BitVec.extractLsb sig (s -i 1) 0) (1 +i nr_leadingzeros)))
      (t__3496, t__3497))
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
    bif (BEq.beq mid_exp (zeros_implicit (n := e)))
    then
      (let t__3495 :=
        ((shiftr mid_sig 1) ||| ((0b1 : (BitVec 1)) ++ (zeros_implicit (n := (s -i 1)))))
      (mid_exp, t__3495))
    else
      (bif (BEq.beq mid_exp (ones (n := e)))
      then
        (let t__3492 := (zeros_implicit (n := e))
        let t__3493 :=
          ((shiftr mid_sig 2) ||| ((0b01 : (BitVec 2)) ++ (zeros_implicit (n := (s -i 2)))))
        (t__3492, t__3493))
      else (mid_exp, mid_sig))
  bif (Bool.and sub (nr_leadingzeros >b 1))
  then
    (bif (Bool.or (BEq.beq rm_3b (0b001 : (BitVec 3)))
         (Bool.or (Bool.and (BEq.beq rm_3b (0b010 : (BitVec 3))) (BEq.beq sign (0b0 : (BitVec 1))))
           (Bool.and (BEq.beq rm_3b (0b011 : (BitVec 3))) (BEq.beq sign (0b1 : (BitVec 1))))))
    then
      (let t__3490 :=
        (zero_extend (m := 64)
          (sign ++ ((ones (n := (e -i 1))) ++ ((0b0 : (BitVec 1)) ++ (ones (n := s))))))
      (pure (true, t__3490)))
    else
      (let t__3488 :=
        (zero_extend (m := 64) (sign ++ ((ones (n := e)) ++ (zeros_implicit (n := s)))))
      (pure (true, t__3488))))
  else
    (let t__3485 := (zero_extend (m := 64) (sign ++ (out_exp ++ out_sig)))
    (pure (false, t__3485)))

def riscv_f16Recip7 (rm : (BitVec 3)) (v : (BitVec 16)) : SailM ((BitVec 5) × (BitVec 16)) := do
  let (round_abnormal_true, res_true) ← do (recip7 v rm true)
  let (round_abnormal_false, res_false) ← do (recip7 v rm false)
  let b__0 := (fp_class v)
  bif (BEq.beq b__0 (0x0001 : (BitVec 16)))
  then
    (let t__3481 := (zeros_implicit (n := 5))
    let t__3482 := (0x8000 : (BitVec 16))
    (pure (t__3481, t__3482)))
  else
    (bif (BEq.beq b__0 (0x0080 : (BitVec 16)))
    then
      (let t__3479 := (zeros_implicit (n := 5))
      let t__3480 := (0x0000 : (BitVec 16))
      (pure (t__3479, t__3480)))
    else
      (bif (BEq.beq b__0 (0x0008 : (BitVec 16)))
      then
        (let t__3477 := (dzFlag ())
        let t__3478 := (0xFC00 : (BitVec 16))
        (pure (t__3477, t__3478)))
      else
        (bif (BEq.beq b__0 (0x0010 : (BitVec 16)))
        then
          (let t__3475 := (dzFlag ())
          let t__3476 := (0x7C00 : (BitVec 16))
          (pure (t__3475, t__3476)))
        else
          (bif (BEq.beq b__0 (0x0100 : (BitVec 16)))
          then
            (let t__3473 := (nvFlag ())
            let t__3474 := (0x7E00 : (BitVec 16))
            (pure (t__3473, t__3474)))
          else
            (bif (BEq.beq b__0 (0x0200 : (BitVec 16)))
            then
              (let t__3471 := (zeros_implicit (n := 5))
              let t__3472 := (0x7E00 : (BitVec 16))
              (pure (t__3471, t__3472)))
            else
              (bif (BEq.beq b__0 (0x0004 : (BitVec 16)))
              then
                (bif round_abnormal_true
                then
                  (let t__3469 := ((nxFlag ()) ||| (ofFlag ()))
                  let t__3470 := (Sail.BitVec.extractLsb res_true 15 0)
                  (pure (t__3469, t__3470)))
                else
                  (let t__3467 := (zeros_implicit (n := 5))
                  let t__3468 := (Sail.BitVec.extractLsb res_true 15 0)
                  (pure (t__3467, t__3468))))
              else
                (bif (BEq.beq b__0 (0x0020 : (BitVec 16)))
                then
                  (bif round_abnormal_true
                  then
                    (let t__3464 := ((nxFlag ()) ||| (ofFlag ()))
                    let t__3465 := (Sail.BitVec.extractLsb res_true 15 0)
                    (pure (t__3464, t__3465)))
                  else
                    (let t__3462 := (zeros_implicit (n := 5))
                    let t__3463 := (Sail.BitVec.extractLsb res_true 15 0)
                    (pure (t__3462, t__3463))))
                else
                  (bif round_abnormal_false
                  then
                    (let t__3459 := ((nxFlag ()) ||| (ofFlag ()))
                    let t__3460 := (Sail.BitVec.extractLsb res_false 15 0)
                    (pure (t__3459, t__3460)))
                  else
                    (let t__3457 := (zeros_implicit (n := 5))
                    let t__3458 := (Sail.BitVec.extractLsb res_false 15 0)
                    (pure (t__3457, t__3458)))))))))))

def riscv_f32Recip7 (rm : (BitVec 3)) (v : (BitVec 32)) : SailM ((BitVec 5) × (BitVec 32)) := do
  let (round_abnormal_true, res_true) ← do (recip7 v rm true)
  let (round_abnormal_false, res_false) ← do (recip7 v rm false)
  let b__0 := (Sail.BitVec.extractLsb (fp_class v) 15 0)
  bif (BEq.beq b__0 (0x0001 : (BitVec 16)))
  then
    (let t__3446 := (zeros_implicit (n := 5))
    let t__3447 := (0x80000000 : (BitVec 32))
    (pure (t__3446, t__3447)))
  else
    (bif (BEq.beq b__0 (0x0080 : (BitVec 16)))
    then
      (let t__3444 := (zeros_implicit (n := 5))
      let t__3445 := (0x00000000 : (BitVec 32))
      (pure (t__3444, t__3445)))
    else
      (bif (BEq.beq b__0 (0x0008 : (BitVec 16)))
      then
        (let t__3442 := (dzFlag ())
        let t__3443 := (0xFF800000 : (BitVec 32))
        (pure (t__3442, t__3443)))
      else
        (bif (BEq.beq b__0 (0x0010 : (BitVec 16)))
        then
          (let t__3440 := (dzFlag ())
          let t__3441 := (0x7F800000 : (BitVec 32))
          (pure (t__3440, t__3441)))
        else
          (bif (BEq.beq b__0 (0x0100 : (BitVec 16)))
          then
            (let t__3438 := (nvFlag ())
            let t__3439 := (0x7FC00000 : (BitVec 32))
            (pure (t__3438, t__3439)))
          else
            (bif (BEq.beq b__0 (0x0200 : (BitVec 16)))
            then
              (let t__3436 := (zeros_implicit (n := 5))
              let t__3437 := (0x7FC00000 : (BitVec 32))
              (pure (t__3436, t__3437)))
            else
              (bif (BEq.beq b__0 (0x0004 : (BitVec 16)))
              then
                (bif round_abnormal_true
                then
                  (let t__3434 := ((nxFlag ()) ||| (ofFlag ()))
                  let t__3435 := (Sail.BitVec.extractLsb res_true 31 0)
                  (pure (t__3434, t__3435)))
                else
                  (let t__3432 := (zeros_implicit (n := 5))
                  let t__3433 := (Sail.BitVec.extractLsb res_true 31 0)
                  (pure (t__3432, t__3433))))
              else
                (bif (BEq.beq b__0 (0x0020 : (BitVec 16)))
                then
                  (bif round_abnormal_true
                  then
                    (let t__3429 := ((nxFlag ()) ||| (ofFlag ()))
                    let t__3430 := (Sail.BitVec.extractLsb res_true 31 0)
                    (pure (t__3429, t__3430)))
                  else
                    (let t__3427 := (zeros_implicit (n := 5))
                    let t__3428 := (Sail.BitVec.extractLsb res_true 31 0)
                    (pure (t__3427, t__3428))))
                else
                  (bif round_abnormal_false
                  then
                    (let t__3424 := ((nxFlag ()) ||| (ofFlag ()))
                    let t__3425 := (Sail.BitVec.extractLsb res_false 31 0)
                    (pure (t__3424, t__3425)))
                  else
                    (let t__3422 := (zeros_implicit (n := 5))
                    let t__3423 := (Sail.BitVec.extractLsb res_false 31 0)
                    (pure (t__3422, t__3423)))))))))))

def riscv_f64Recip7 (rm : (BitVec 3)) (v : (BitVec 64)) : SailM ((BitVec 5) × (BitVec 64)) := do
  let (round_abnormal_true, res_true) ← do (recip7 v rm true)
  let (round_abnormal_false, res_false) ← do (recip7 v rm false)
  let b__0 := (Sail.BitVec.extractLsb (fp_class v) 15 0)
  bif (BEq.beq b__0 (0x0001 : (BitVec 16)))
  then
    (let t__3411 := (zeros_implicit (n := 5))
    let t__3412 := (0x8000000000000000 : (BitVec 64))
    (pure (t__3411, t__3412)))
  else
    (bif (BEq.beq b__0 (0x0080 : (BitVec 16)))
    then
      (let t__3409 := (zeros_implicit (n := 5))
      let t__3410 := (0x0000000000000000 : (BitVec 64))
      (pure (t__3409, t__3410)))
    else
      (bif (BEq.beq b__0 (0x0008 : (BitVec 16)))
      then
        (let t__3407 := (dzFlag ())
        let t__3408 := (0xFFF0000000000000 : (BitVec 64))
        (pure (t__3407, t__3408)))
      else
        (bif (BEq.beq b__0 (0x0010 : (BitVec 16)))
        then
          (let t__3405 := (dzFlag ())
          let t__3406 := (0x7FF0000000000000 : (BitVec 64))
          (pure (t__3405, t__3406)))
        else
          (bif (BEq.beq b__0 (0x0100 : (BitVec 16)))
          then
            (let t__3403 := (nvFlag ())
            let t__3404 := (0x7FF8000000000000 : (BitVec 64))
            (pure (t__3403, t__3404)))
          else
            (bif (BEq.beq b__0 (0x0200 : (BitVec 16)))
            then
              (let t__3401 := (zeros_implicit (n := 5))
              let t__3402 := (0x7FF8000000000000 : (BitVec 64))
              (pure (t__3401, t__3402)))
            else
              (bif (BEq.beq b__0 (0x0004 : (BitVec 16)))
              then
                (bif round_abnormal_true
                then
                  (let t__3399 := ((nxFlag ()) ||| (ofFlag ()))
                  let t__3400 := (Sail.BitVec.extractLsb res_true 63 0)
                  (pure (t__3399, t__3400)))
                else
                  (let t__3397 := (zeros_implicit (n := 5))
                  let t__3398 := (Sail.BitVec.extractLsb res_true 63 0)
                  (pure (t__3397, t__3398))))
              else
                (bif (BEq.beq b__0 (0x0020 : (BitVec 16)))
                then
                  (bif round_abnormal_true
                  then
                    (let t__3394 := ((nxFlag ()) ||| (ofFlag ()))
                    let t__3395 := (Sail.BitVec.extractLsb res_true 63 0)
                    (pure (t__3394, t__3395)))
                  else
                    (let t__3392 := (zeros_implicit (n := 5))
                    let t__3393 := (Sail.BitVec.extractLsb res_true 63 0)
                    (pure (t__3392, t__3393))))
                else
                  (bif round_abnormal_false
                  then
                    (let t__3389 := ((nxFlag ()) ||| (ofFlag ()))
                    let t__3390 := (Sail.BitVec.extractLsb res_false 63 0)
                    (pure (t__3389, t__3390)))
                  else
                    (let t__3387 := (zeros_implicit (n := 5))
                    let t__3388 := (Sail.BitVec.extractLsb res_false 63 0)
                    (pure (t__3387, t__3388)))))))))))

