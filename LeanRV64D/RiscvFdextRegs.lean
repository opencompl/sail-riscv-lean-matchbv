import LeanRV64D.RiscvSoftfloatInterface

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

/-- Type quantifiers: n : Nat, n ∈ {16, 32, 64, 128} -/
def canonical_NaN {n : _} : (BitVec n) :=
  match n with
  | 16 => ((0b0 : (BitVec 1)) ++ ((ones (n := 5)) ++ ((0b1 : (BitVec 1)) ++ (zeros (n := 9)))))
  | 32 => ((0b0 : (BitVec 1)) ++ ((ones (n := 8)) ++ ((0b1 : (BitVec 1)) ++ (zeros (n := 22)))))
  | 64 => ((0b0 : (BitVec 1)) ++ ((ones (n := 11)) ++ ((0b1 : (BitVec 1)) ++ (zeros (n := 51)))))
  | _ => ((0b0 : (BitVec 1)) ++ ((ones (n := 15)) ++ ((0b1 : (BitVec 1)) ++ (zeros (n := 111)))))

def canonical_NaN_H (_ : Unit) : (BitVec 16) :=
  (canonical_NaN (n := 16))

def canonical_NaN_S (_ : Unit) : (BitVec 32) :=
  (canonical_NaN (n := 32))

def canonical_NaN_D (_ : Unit) : (BitVec 64) :=
  (canonical_NaN (n := 64))

def canonical_NaN_Q (_ : Unit) : (BitVec 128) :=
  (canonical_NaN (n := 128))

/-- Type quantifiers: k_n : Int, n : Int, k_n ≤ n -/
def nan_box {n : _} (x : (BitVec k_n)) : (BitVec n) :=
  ((ones (n := (n -i (Sail.BitVec.length x)))) ++ x)

/-- Type quantifiers: k_n : Nat, m : Nat, m ∈ {16, 32, 64, 128} ∧ k_n ≥ m -/
def nan_unbox {m : _} (x : (BitVec k_n)) : (BitVec m) :=
  bif ((Sail.BitVec.length x) == m)
  then x
  else
    (bif ((Sail.BitVec.extractLsb x ((Sail.BitVec.length x) -i 1) m) == (ones
           (n := ((((Sail.BitVec.length x) -i 1) -i m) +i 1))))
    then (Sail.BitVec.extractLsb x (m -i 1) 0)
    else (canonical_NaN (n := m)))

def fregidx_to_fregno (app_0 : fregidx) : fregno :=
  let .Fregidx b := app_0
  (Fregno (BitVec.toNat b))

def fregno_to_fregidx (app_0 : fregno) : fregidx :=
  let .Fregno b := app_0
  (Fregidx (to_bits 5 b))

def fregidx_offset (typ_0 : fregidx) (o : (BitVec 5)) : fregidx :=
  let .Fregidx r : fregidx := typ_0
  (Fregidx (r + o))

def fregidx_bits (app_0 : fregidx) : (BitVec 5) :=
  let .Fregidx r := app_0
  r

def cregidx_to_fregidx (app_0 : cregidx) : fregidx :=
  let .Cregidx b := app_0
  (Fregidx ((0b01 : (BitVec 2)) ++ b))

def encdec_freg_forwards (arg_ : fregidx) : (BitVec 5) :=
  match arg_ with
  | .Fregidx r => r

def encdec_freg_backwards (arg_ : (BitVec 5)) : fregidx :=
  match arg_ with
  | r => (Fregidx r)

def encdec_freg_forwards_matches (arg_ : fregidx) : Bool :=
  match arg_ with
  | .Fregidx r => true
  | _ => false

def encdec_freg_backwards_matches (arg_ : (BitVec 5)) : Bool :=
  match arg_ with
  | r => true
  | _ => false

def freg_write_callback (x_0 : fregidx) (x_1 : (BitVec (8 * 8))) : Unit :=
  ()

def dirty_fd_context (_ : Unit) : SailM Unit := do
  assert (hartSupports Ext_F) "riscv_fdext_regs.sail:110.28-110.29"
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 14 13 (extStatus_to_bits Dirty))
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) (((2 ^i 3) *i 8) -i 1)
    (((2 ^i 3) *i 8) -i 1) (0b1 : (BitVec 1)))
  (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))

def dirty_fd_context_if_present (_ : Unit) : SailM Unit := do
  assert (neq_bool (hartSupports Ext_F) (hartSupports Ext_Zfinx)) "riscv_fdext_regs.sail:117.55-117.56"
  bif (hartSupports Ext_F)
  then (dirty_fd_context ())
  else (pure ())

def rF (app_0 : fregno) : SailM (BitVec (8 * 8)) := do
  let .Fregno r := app_0
  assert (hartSupports Ext_F) "riscv_fdext_regs.sail:122.28-122.29"
  let v ← (( do
    match r with
    | 0 => readReg f0
    | 1 => readReg f1
    | 2 => readReg f2
    | 3 => readReg f3
    | 4 => readReg f4
    | 5 => readReg f5
    | 6 => readReg f6
    | 7 => readReg f7
    | 8 => readReg f8
    | 9 => readReg f9
    | 10 => readReg f10
    | 11 => readReg f11
    | 12 => readReg f12
    | 13 => readReg f13
    | 14 => readReg f14
    | 15 => readReg f15
    | 16 => readReg f16
    | 17 => readReg f17
    | 18 => readReg f18
    | 19 => readReg f19
    | 20 => readReg f20
    | 21 => readReg f21
    | 22 => readReg f22
    | 23 => readReg f23
    | 24 => readReg f24
    | 25 => readReg f25
    | 26 => readReg f26
    | 27 => readReg f27
    | 28 => readReg f28
    | 29 => readReg f29
    | 30 => readReg f30
    | 31 => readReg f31
    | _ =>
      (do
        assert false "invalid floating point register number"
        throw Error.Exit) ) : SailM fregtype )
  (pure (fregval_from_freg v))

def wF (typ_0 : fregno) (in_v : (BitVec (8 * 8))) : SailM Unit := do
  let .Fregno r : fregno := typ_0
  assert (hartSupports Ext_F) "riscv_fdext_regs.sail:163.28-163.29"
  let v := (fregval_into_freg in_v)
  match r with
  | 0 => writeReg f0 v
  | 1 => writeReg f1 v
  | 2 => writeReg f2 v
  | 3 => writeReg f3 v
  | 4 => writeReg f4 v
  | 5 => writeReg f5 v
  | 6 => writeReg f6 v
  | 7 => writeReg f7 v
  | 8 => writeReg f8 v
  | 9 => writeReg f9 v
  | 10 => writeReg f10 v
  | 11 => writeReg f11 v
  | 12 => writeReg f12 v
  | 13 => writeReg f13 v
  | 14 => writeReg f14 v
  | 15 => writeReg f15 v
  | 16 => writeReg f16 v
  | 17 => writeReg f17 v
  | 18 => writeReg f18 v
  | 19 => writeReg f19 v
  | 20 => writeReg f20 v
  | 21 => writeReg f21 v
  | 22 => writeReg f22 v
  | 23 => writeReg f23 v
  | 24 => writeReg f24 v
  | 25 => writeReg f25 v
  | 26 => writeReg f26 v
  | 27 => writeReg f27 v
  | 28 => writeReg f28 v
  | 29 => writeReg f29 v
  | 30 => writeReg f30 v
  | 31 => writeReg f31 v
  | _ => assert false "invalid floating point register number"
  let _ : Unit := (freg_write_callback (fregno_to_fregidx (Fregno r)) in_v)
  (dirty_fd_context ())

def rF_bits (i : fregidx) : SailM (BitVec (8 * 8)) := do
  (rF (fregidx_to_fregno i))

def wF_bits (i : fregidx) (data : (BitVec (8 * 8))) : SailM Unit := do
  (wF (fregidx_to_fregno i) data)

def rF_H (i : fregidx) : SailM (BitVec 16) := do
  assert (flen ≥b 16) "riscv_fdext_regs.sail:215.19-215.20"
  assert ((hartSupports Ext_F) && (not (hartSupports Ext_Zfinx))) "riscv_fdext_regs.sail:216.59-216.60"
  (pure (nan_unbox (m := 16) (← (rF_bits i))))

def wF_H (i : fregidx) (data : (BitVec 16)) : SailM Unit := do
  assert (flen ≥b 16) "riscv_fdext_regs.sail:222.19-222.20"
  assert ((hartSupports Ext_F) && (not (hartSupports Ext_Zfinx))) "riscv_fdext_regs.sail:223.59-223.60"
  (wF_bits i (nan_box (n := (8 *i 8)) data))

def rF_S (i : fregidx) : SailM (BitVec 32) := do
  assert (flen ≥b 32) "riscv_fdext_regs.sail:229.19-229.20"
  assert ((hartSupports Ext_F) && (not (hartSupports Ext_Zfinx))) "riscv_fdext_regs.sail:230.59-230.60"
  (pure (nan_unbox (m := 32) (← (rF_bits i))))

def wF_S (i : fregidx) (data : (BitVec 32)) : SailM Unit := do
  assert (flen ≥b 32) "riscv_fdext_regs.sail:236.19-236.20"
  assert ((hartSupports Ext_F) && (not (hartSupports Ext_Zfinx))) "riscv_fdext_regs.sail:237.59-237.60"
  (wF_bits i (nan_box (n := (8 *i 8)) data))

def rF_D (i : fregidx) : SailM (BitVec 64) := do
  assert (flen ≥b 64) "riscv_fdext_regs.sail:243.19-243.20"
  assert ((hartSupports Ext_F) && (not (hartSupports Ext_Zfinx))) "riscv_fdext_regs.sail:244.59-244.60"
  (rF_bits i)

def wF_D (i : fregidx) (data : (BitVec 64)) : SailM Unit := do
  assert (flen ≥b 64) "riscv_fdext_regs.sail:250.19-250.20"
  assert ((hartSupports Ext_F) && (not (hartSupports Ext_Zfinx))) "riscv_fdext_regs.sail:251.59-251.60"
  (wF_bits i data)

def rF_or_X_H (i : fregidx) : SailM (BitVec 16) := do
  assert (flen ≥b 16) "riscv_fdext_regs.sail:261.19-261.20"
  assert (neq_bool (hartSupports Ext_F) (hartSupports Ext_Zfinx)) "riscv_fdext_regs.sail:262.55-262.56"
  bif (hartSupports Ext_F)
  then (rF_H i)
  else (pure (Sail.BitVec.extractLsb (← (rX_bits (fregidx_to_regidx i))) 15 0))

def rF_or_X_S (i : fregidx) : SailM (BitVec 32) := do
  assert (flen ≥b 32) "riscv_fdext_regs.sail:270.19-270.20"
  assert (neq_bool (hartSupports Ext_F) (hartSupports Ext_Zfinx)) "riscv_fdext_regs.sail:271.55-271.56"
  bif (hartSupports Ext_F)
  then (rF_S i)
  else (pure (Sail.BitVec.extractLsb (← (rX_bits (fregidx_to_regidx i))) 31 0))

def rF_or_X_D (i : fregidx) : SailM (BitVec 64) := do
  assert (flen ≥b 64) "riscv_fdext_regs.sail:279.19-279.20"
  assert (neq_bool (hartSupports Ext_F) (hartSupports Ext_Zfinx)) "riscv_fdext_regs.sail:280.55-280.56"
  bif (hartSupports Ext_F)
  then (rF_D i)
  else (pure (Sail.BitVec.extractLsb (← (rX_bits (fregidx_to_regidx i))) 63 0))

def wF_or_X_H (i : fregidx) (data : (BitVec 16)) : SailM Unit := do
  assert (flen ≥b 16) "riscv_fdext_regs.sail:294.19-294.20"
  assert (neq_bool (hartSupports Ext_F) (hartSupports Ext_Zfinx)) "riscv_fdext_regs.sail:295.55-295.56"
  bif (hartSupports Ext_F)
  then (wF_H i data)
  else (wX_bits (fregidx_to_regidx i) (sign_extend (m := ((2 ^i 3) *i 8)) data))

def wF_or_X_S (i : fregidx) (data : (BitVec 32)) : SailM Unit := do
  assert (flen ≥b 32) "riscv_fdext_regs.sail:303.19-303.20"
  assert (neq_bool (hartSupports Ext_F) (hartSupports Ext_Zfinx)) "riscv_fdext_regs.sail:304.55-304.56"
  bif (hartSupports Ext_F)
  then (wF_S i data)
  else (wX_bits (fregidx_to_regidx i) (sign_extend (m := ((2 ^i 3) *i 8)) data))

def wF_or_X_D (i : fregidx) (data : (BitVec 64)) : SailM Unit := do
  assert (flen ≥b 64) "riscv_fdext_regs.sail:312.20-312.21"
  assert (neq_bool (hartSupports Ext_F) (hartSupports Ext_Zfinx)) "riscv_fdext_regs.sail:313.55-313.56"
  bif (hartSupports Ext_F)
  then (wF_D i data)
  else (wX_bits (fregidx_to_regidx i) (sign_extend (m := ((2 ^i 3) *i 8)) data))

def freg_name_raw_backwards (arg_ : String) : SailM (BitVec 5) := do
  match arg_ with
  | "ft0" => (pure (0b00000 : (BitVec 5)))
  | "ft1" => (pure (0b00001 : (BitVec 5)))
  | "ft2" => (pure (0b00010 : (BitVec 5)))
  | "ft3" => (pure (0b00011 : (BitVec 5)))
  | "ft4" => (pure (0b00100 : (BitVec 5)))
  | "ft5" => (pure (0b00101 : (BitVec 5)))
  | "ft6" => (pure (0b00110 : (BitVec 5)))
  | "ft7" => (pure (0b00111 : (BitVec 5)))
  | "fs0" => (pure (0b01000 : (BitVec 5)))
  | "fs1" => (pure (0b01001 : (BitVec 5)))
  | "fa0" => (pure (0b01010 : (BitVec 5)))
  | "fa1" => (pure (0b01011 : (BitVec 5)))
  | "fa2" => (pure (0b01100 : (BitVec 5)))
  | "fa3" => (pure (0b01101 : (BitVec 5)))
  | "fa4" => (pure (0b01110 : (BitVec 5)))
  | "fa5" => (pure (0b01111 : (BitVec 5)))
  | "fa6" => (pure (0b10000 : (BitVec 5)))
  | "fa7" => (pure (0b10001 : (BitVec 5)))
  | "fs2" => (pure (0b10010 : (BitVec 5)))
  | "fs3" => (pure (0b10011 : (BitVec 5)))
  | "fs4" => (pure (0b10100 : (BitVec 5)))
  | "fs5" => (pure (0b10101 : (BitVec 5)))
  | "fs6" => (pure (0b10110 : (BitVec 5)))
  | "fs7" => (pure (0b10111 : (BitVec 5)))
  | "fs8" => (pure (0b11000 : (BitVec 5)))
  | "fs9" => (pure (0b11001 : (BitVec 5)))
  | "fs10" => (pure (0b11010 : (BitVec 5)))
  | "fs11" => (pure (0b11011 : (BitVec 5)))
  | "ft8" => (pure (0b11100 : (BitVec 5)))
  | "ft9" => (pure (0b11101 : (BitVec 5)))
  | "ft10" => (pure (0b11110 : (BitVec 5)))
  | "ft11" => (pure (0b11111 : (BitVec 5)))
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def freg_name_raw_forwards_matches (arg_ : (BitVec 5)) : Bool :=
  match_bv arg_ with
  | 00000 => true
  | 00001 => true
  | 00010 => true
  | 00011 => true
  | 00100 => true
  | 00101 => true
  | 00110 => true
  | 00111 => true
  | 01000 => true
  | 01001 => true
  | 01010 => true
  | 01011 => true
  | 01100 => true
  | 01101 => true
  | 01110 => true
  | 01111 => true
  | 10000 => true
  | 10001 => true
  | 10010 => true
  | 10011 => true
  | 10100 => true
  | 10101 => true
  | 10110 => true
  | 10111 => true
  | 11000 => true
  | 11001 => true
  | 11010 => true
  | 11011 => true
  | 11100 => true
  | 11101 => true
  | 11110 => true
  | 11111 => true
  | _ => false

def freg_name_raw_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "ft0" => true
  | "ft1" => true
  | "ft2" => true
  | "ft3" => true
  | "ft4" => true
  | "ft5" => true
  | "ft6" => true
  | "ft7" => true
  | "fs0" => true
  | "fs1" => true
  | "fa0" => true
  | "fa1" => true
  | "fa2" => true
  | "fa3" => true
  | "fa4" => true
  | "fa5" => true
  | "fa6" => true
  | "fa7" => true
  | "fs2" => true
  | "fs3" => true
  | "fs4" => true
  | "fs5" => true
  | "fs6" => true
  | "fs7" => true
  | "fs8" => true
  | "fs9" => true
  | "fs10" => true
  | "fs11" => true
  | "ft8" => true
  | "ft9" => true
  | "ft10" => true
  | "ft11" => true
  | _ => false

def freg_name_backwards (arg_ : String) : SailM fregidx := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    bif (freg_name_raw_backwards_matches mapping0_)
    then
      (do
        match (← (freg_name_raw_backwards mapping0_)) with
        | i => (pure (some (Fregidx i)))
        | _ => (pure none))
    else (pure none)) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def freg_name_forwards_matches (arg_ : fregidx) : Bool :=
  match arg_ with
  | .Fregidx i => true
  | _ => false

def freg_name_backwards_matches (arg_ : String) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    bif (freg_name_raw_backwards_matches mapping0_)
    then
      (do
        match (← (freg_name_raw_backwards mapping0_)) with
        | i => (pure (some true))
        | _ => (pure none))
    else (pure none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def freg_or_reg_name_backwards (arg_ : String) : SailM fregidx := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    bif (← (reg_name_backwards_matches mapping0_))
    then
      (do
        match (← (reg_name_backwards mapping0_)) with
        | .Regidx i =>
          (bif (hartSupports Ext_Zfinx)
          then (pure (some (Fregidx (zero_extend (m := 5) i))))
          else (pure none)))
    else (pure none)) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let mapping1_ := head_exp_
        bif (← (freg_name_backwards_matches mapping1_))
        then
          (do
            match (← (freg_name_backwards mapping1_)) with
            | f => (pure (some f))
            | _ => (pure none))
        else (pure none)) with
      | .some result => (pure result)
      | _ =>
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))

def freg_or_reg_name_forwards_matches (arg_ : fregidx) : Bool :=
  let f := arg_
  bif (hartSupports Ext_Zfinx)
  then true
  else true

def freg_or_reg_name_backwards_matches (arg_ : String) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    bif (← (reg_name_backwards_matches mapping0_))
    then
      (do
        match (← (reg_name_backwards mapping0_)) with
        | .Regidx i =>
          (bif (hartSupports Ext_Zfinx)
          then (pure (some true))
          else (pure none)))
    else (pure none)) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let mapping1_ := head_exp_
        bif (← (freg_name_backwards_matches mapping1_))
        then
          (do
            match (← (freg_name_backwards mapping1_)) with
            | f => (pure (some true))
            | _ => (pure none))
        else (pure none)) with
      | .some result => (pure result)
      | none =>
        (match head_exp_ with
        | _ => (pure false)))

def undefined_Fcsr (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_Fcsr (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_Fcsr_FFLAGS (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _update_Fcsr_FFLAGS (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _set_Fcsr_FFLAGS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Fcsr_FFLAGS r v)

def _get_Fcsr_FRM (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 7 5)

def _update_Fcsr_FRM (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 5 x)

def _set_Fcsr_FRM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Fcsr_FRM r v)

def write_fcsr (frm : (BitVec 3)) (fflags : (BitVec 5)) : SailM Unit := do
  writeReg fcsr (Sail.BitVec.updateSubrange (← readReg fcsr) 7 5 frm)
  writeReg fcsr (Sail.BitVec.updateSubrange (← readReg fcsr) 4 0 fflags)
  (dirty_fd_context_if_present ())

def accrue_fflags (flags : (BitVec 5)) : SailM Unit := do
  let f ← do (pure ((_get_Fcsr_FFLAGS (← readReg fcsr)) ||| flags))
  bif ((_get_Fcsr_FFLAGS (← readReg fcsr)) != f)
  then
    (do
      writeReg fcsr (Sail.BitVec.updateSubrange (← readReg fcsr) 4 0 f)
      (dirty_fd_context_if_present ()))
  else (pure ())

