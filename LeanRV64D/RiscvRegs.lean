import LeanRV64D.RiscvFregType

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

def rX (app_0 : regno) : SailM (BitVec (2 ^ 3 * 8)) := do
  let .Regno r := app_0
  let v ← (( do
    match r with
    | 0 => (pure zero_reg)
    | 1 => readReg x1
    | 2 => readReg x2
    | 3 => readReg x3
    | 4 => readReg x4
    | 5 => readReg x5
    | 6 => readReg x6
    | 7 => readReg x7
    | 8 => readReg x8
    | 9 => readReg x9
    | 10 => readReg x10
    | 11 => readReg x11
    | 12 => readReg x12
    | 13 => readReg x13
    | 14 => readReg x14
    | 15 => readReg x15
    | 16 => readReg x16
    | 17 => readReg x17
    | 18 => readReg x18
    | 19 => readReg x19
    | 20 => readReg x20
    | 21 => readReg x21
    | 22 => readReg x22
    | 23 => readReg x23
    | 24 => readReg x24
    | 25 => readReg x25
    | 26 => readReg x26
    | 27 => readReg x27
    | 28 => readReg x28
    | 29 => readReg x29
    | 30 => readReg x30
    | 31 => readReg x31
    | _ =>
      (do
        assert false "invalid register number"
        throw Error.Exit) ) : SailM regtype )
  (pure (regval_from_reg v))

def wX (typ_0 : regno) (in_v : (BitVec (2 ^ 3 * 8))) : SailM Unit := do
  let .Regno r : regno := typ_0
  let v := (regval_into_reg in_v)
  match r with
  | 0 => (pure ())
  | 1 => writeReg x1 v
  | 2 => writeReg x2 v
  | 3 => writeReg x3 v
  | 4 => writeReg x4 v
  | 5 => writeReg x5 v
  | 6 => writeReg x6 v
  | 7 => writeReg x7 v
  | 8 => writeReg x8 v
  | 9 => writeReg x9 v
  | 10 => writeReg x10 v
  | 11 => writeReg x11 v
  | 12 => writeReg x12 v
  | 13 => writeReg x13 v
  | 14 => writeReg x14 v
  | 15 => writeReg x15 v
  | 16 => writeReg x16 v
  | 17 => writeReg x17 v
  | 18 => writeReg x18 v
  | 19 => writeReg x19 v
  | 20 => writeReg x20 v
  | 21 => writeReg x21 v
  | 22 => writeReg x22 v
  | 23 => writeReg x23 v
  | 24 => writeReg x24 v
  | 25 => writeReg x25 v
  | 26 => writeReg x26 v
  | 27 => writeReg x27 v
  | 28 => writeReg x28 v
  | 29 => writeReg x29 v
  | 30 => writeReg x30 v
  | 31 => writeReg x31 v
  | _ => assert false "invalid register number"
  bif (r != 0)
  then (pure (xreg_write_callback (regno_to_regidx (Regno r)) in_v))
  else (pure ())

def rX_bits (i : regidx) : SailM (BitVec (2 ^ 3 * 8)) := do
  (rX (regidx_to_regno i))

def wX_bits (i : regidx) (data : (BitVec (2 ^ 3 * 8))) : SailM Unit := do
  (wX (regidx_to_regno i) data)

def reg_name_raw_backwards (arg_ : String) : SailM (BitVec 5) := do
  match arg_ with
  | "zero" => (pure (0b00000 : (BitVec 5)))
  | "ra" => (pure (0b00001 : (BitVec 5)))
  | "sp" => (pure (0b00010 : (BitVec 5)))
  | "gp" => (pure (0b00011 : (BitVec 5)))
  | "tp" => (pure (0b00100 : (BitVec 5)))
  | "t0" => (pure (0b00101 : (BitVec 5)))
  | "t1" => (pure (0b00110 : (BitVec 5)))
  | "t2" => (pure (0b00111 : (BitVec 5)))
  | "fp" => (pure (0b01000 : (BitVec 5)))
  | "s1" => (pure (0b01001 : (BitVec 5)))
  | "a0" => (pure (0b01010 : (BitVec 5)))
  | "a1" => (pure (0b01011 : (BitVec 5)))
  | "a2" => (pure (0b01100 : (BitVec 5)))
  | "a3" => (pure (0b01101 : (BitVec 5)))
  | "a4" => (pure (0b01110 : (BitVec 5)))
  | "a5" => (pure (0b01111 : (BitVec 5)))
  | "a6" => (pure (0b10000 : (BitVec 5)))
  | "a7" => (pure (0b10001 : (BitVec 5)))
  | "s2" => (pure (0b10010 : (BitVec 5)))
  | "s3" => (pure (0b10011 : (BitVec 5)))
  | "s4" => (pure (0b10100 : (BitVec 5)))
  | "s5" => (pure (0b10101 : (BitVec 5)))
  | "s6" => (pure (0b10110 : (BitVec 5)))
  | "s7" => (pure (0b10111 : (BitVec 5)))
  | "s8" => (pure (0b11000 : (BitVec 5)))
  | "s9" => (pure (0b11001 : (BitVec 5)))
  | "s10" => (pure (0b11010 : (BitVec 5)))
  | "s11" => (pure (0b11011 : (BitVec 5)))
  | "t3" => (pure (0b11100 : (BitVec 5)))
  | "t4" => (pure (0b11101 : (BitVec 5)))
  | "t5" => (pure (0b11110 : (BitVec 5)))
  | "t6" => (pure (0b11111 : (BitVec 5)))
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def reg_name_raw_forwards_matches (arg_ : (BitVec 5)) : Bool :=
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

def reg_name_raw_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "zero" => true
  | "ra" => true
  | "sp" => true
  | "gp" => true
  | "tp" => true
  | "t0" => true
  | "t1" => true
  | "t2" => true
  | "fp" => true
  | "s1" => true
  | "a0" => true
  | "a1" => true
  | "a2" => true
  | "a3" => true
  | "a4" => true
  | "a5" => true
  | "a6" => true
  | "a7" => true
  | "s2" => true
  | "s3" => true
  | "s4" => true
  | "s5" => true
  | "s6" => true
  | "s7" => true
  | "s8" => true
  | "s9" => true
  | "s10" => true
  | "s11" => true
  | "t3" => true
  | "t4" => true
  | "t5" => true
  | "t6" => true
  | _ => false

def reg_name_backwards (arg_ : String) : SailM regidx := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    bif (reg_name_raw_backwards_matches mapping0_)
    then
      (do
        match (← (reg_name_raw_backwards mapping0_)) with
        | i => (pure (some (Regidx i)))
        | _ => (pure none))
    else (pure none)) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def reg_name_forwards_matches (arg_ : regidx) : Bool :=
  match arg_ with
  | .Regidx i => true
  | _ => false

def reg_name_backwards_matches (arg_ : String) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    bif (reg_name_raw_backwards_matches mapping0_)
    then
      (do
        match (← (reg_name_raw_backwards mapping0_)) with
        | i => (pure (some true))
        | _ => (pure none))
    else (pure none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def creg_name_raw_backwards (arg_ : String) : SailM (BitVec 3) := do
  match arg_ with
  | "s0" => (pure (0b000 : (BitVec 3)))
  | "s1" => (pure (0b001 : (BitVec 3)))
  | "a0" => (pure (0b010 : (BitVec 3)))
  | "a1" => (pure (0b011 : (BitVec 3)))
  | "a2" => (pure (0b100 : (BitVec 3)))
  | "a3" => (pure (0b101 : (BitVec 3)))
  | "a4" => (pure (0b110 : (BitVec 3)))
  | "a5" => (pure (0b111 : (BitVec 3)))
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def creg_name_raw_forwards_matches (arg_ : (BitVec 3)) : Bool :=
  match_bv arg_ with
  | 000 => true
  | 001 => true
  | 010 => true
  | 011 => true
  | 100 => true
  | 101 => true
  | 110 => true
  | 111 => true
  | _ => false

def creg_name_raw_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "s0" => true
  | "s1" => true
  | "a0" => true
  | "a1" => true
  | "a2" => true
  | "a3" => true
  | "a4" => true
  | "a5" => true
  | _ => false

def creg_name_backwards (arg_ : String) : SailM cregidx := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    bif (creg_name_raw_backwards_matches mapping0_)
    then
      (do
        match (← (creg_name_raw_backwards mapping0_)) with
        | i => (pure (some (Cregidx i)))
        | _ => (pure none))
    else (pure none)) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def creg_name_forwards_matches (arg_ : cregidx) : Bool :=
  match arg_ with
  | .Cregidx i => true
  | _ => false

def creg_name_backwards_matches (arg_ : String) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    let mapping0_ := head_exp_
    bif (creg_name_raw_backwards_matches mapping0_)
    then
      (do
        match (← (creg_name_raw_backwards mapping0_)) with
        | i => (pure (some true))
        | _ => (pure none))
    else (pure none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def encdec_reg_forwards (arg_ : regidx) : (BitVec 5) :=
  match arg_ with
  | .Regidx r => r

def encdec_reg_backwards (arg_ : (BitVec 5)) : regidx :=
  match arg_ with
  | r => (Regidx r)

def encdec_reg_forwards_matches (arg_ : regidx) : Bool :=
  match arg_ with
  | .Regidx r => true
  | _ => false

def encdec_reg_backwards_matches (arg_ : (BitVec 5)) : Bool :=
  match arg_ with
  | r => true
  | _ => false

def encdec_creg_forwards (arg_ : cregidx) : (BitVec 3) :=
  match arg_ with
  | .Cregidx r => r

def encdec_creg_backwards (arg_ : (BitVec 3)) : cregidx :=
  match arg_ with
  | r => (Cregidx r)

def encdec_creg_forwards_matches (arg_ : cregidx) : Bool :=
  match arg_ with
  | .Cregidx r => true
  | _ => false

def encdec_creg_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  match arg_ with
  | r => true
  | _ => false

