import LeanRV64D.DecBits

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

def not_bit (b : (BitVec 1)) : (BitVec 1) :=
  bif (b == 1#1)
  then 0#1
  else 1#1

/-- Type quantifiers: k_p : Bool -/
def not (b : Bool) : Bool :=
  (! b)

def bit_str (b : (BitVec 1)) : SailM String := do
  match b with
  | 0#1 => (pure "0b0")
  | 1#1 => (pure "0b1")
  | _ =>
    (do
      assert false "Pattern match failure at prelude.sail:36.2-39.3"
      throw Error.Exit)

def print_step (_ : Unit) : Unit :=
  ()

def get_config_print_instr (_ : Unit) : Bool :=
  false

def get_config_print_platform (_ : Unit) : Bool :=
  false

/-- Type quantifiers: k_n : Int, m : Int, m ≥ k_n -/
def sign_extend {m : _} (v : (BitVec k_n)) : (BitVec m) :=
  (Sail.BitVec.signExtend v m)

/-- Type quantifiers: k_n : Int, m : Int, m ≥ k_n -/
def zero_extend {m : _} (v : (BitVec k_n)) : (BitVec m) :=
  (Sail.BitVec.zeroExtend v m)

/-- Type quantifiers: n : Nat, n ≥ 0 -/
def zeros {n : _} : (BitVec n) :=
  (BitVec.zero n)

/-- Type quantifiers: n : Nat, n ≥ 0 -/
def ones {n : _} : (BitVec n) :=
  (sail_ones n)

/-- Type quantifiers: m : Nat, k_n : Nat, m ≥ 0 ∧ m ≤ k_n -/
def trunc {m : _} (v : (BitVec k_n)) : (BitVec m) :=
  (Sail.BitVec.truncate v m)

/-- Type quantifiers: k_ex278680# : Bool -/
def bool_bit_forwards (arg_ : Bool) : (BitVec 1) :=
  match arg_ with
  | true => 1#1
  | false => 0#1

def bool_bit_backwards (arg_ : (BitVec 1)) : SailM Bool := do
  match arg_ with
  | 1#1 => (pure true)
  | 0#1 => (pure false)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: k_ex278681# : Bool -/
def bool_bit_forwards_matches (arg_ : Bool) : Bool :=
  match arg_ with
  | true => true
  | false => true
  | _ => false

def bool_bit_backwards_matches (arg_ : (BitVec 1)) : Bool :=
  match arg_ with
  | 1#1 => true
  | 0#1 => true
  | g__2 => false

/-- Type quantifiers: k_ex278682# : Bool -/
def bool_bits_forwards (arg_ : Bool) : (BitVec 1) :=
  match arg_ with
  | true => (0b1 : (BitVec 1))
  | false => (0b0 : (BitVec 1))

def bool_bits_backwards (arg_ : (BitVec 1)) : Bool :=
  match_bv arg_ with
  | 1 => true
  | _ => false

/-- Type quantifiers: k_ex278683# : Bool -/
def bool_bits_forwards_matches (arg_ : Bool) : Bool :=
  match arg_ with
  | true => true
  | false => true
  | _ => false

def bool_bits_backwards_matches (arg_ : (BitVec 1)) : Bool :=
  match_bv arg_ with
  | 1 => true
  | 0 => true
  | _ => false

/-- Type quantifiers: k_ex278684# : Bool -/
def bool_not_bits_forwards (arg_ : Bool) : (BitVec 1) :=
  match arg_ with
  | true => (0b0 : (BitVec 1))
  | false => (0b1 : (BitVec 1))

def bool_not_bits_backwards (arg_ : (BitVec 1)) : Bool :=
  match_bv arg_ with
  | 0 => true
  | _ => false

/-- Type quantifiers: k_ex278685# : Bool -/
def bool_not_bits_forwards_matches (arg_ : Bool) : Bool :=
  match arg_ with
  | true => true
  | false => true
  | _ => false

def bool_not_bits_backwards_matches (arg_ : (BitVec 1)) : Bool :=
  match_bv arg_ with
  | 0 => true
  | 1 => true
  | _ => false

/-- Type quantifiers: k_ex278686# : Bool -/
def bool_to_bit (x : Bool) : (BitVec 1) :=
  (bool_bit_forwards x)

def bit_to_bool (x : (BitVec 1)) : SailM Bool := do
  (bool_bit_backwards x)

/-- Type quantifiers: k_ex278688# : Bool -/
def bool_to_bits (x : Bool) : (BitVec 1) :=
  (bool_bits_forwards x)

def bits_to_bool (x : (BitVec 1)) : Bool :=
  (bool_bits_backwards x)

/-- Type quantifiers: n : Int, l : Nat, l ≥ 0 -/
def to_bits (l : Nat) (n : Int) : (BitVec l) :=
  (get_slice_int l n 0)

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def zopz0zI_s (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toInt x) <b (BitVec.toInt y))

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def zopz0zK_s (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toInt x) >b (BitVec.toInt y))

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def zopz0zIzJ_s (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toInt x) ≤b (BitVec.toInt y))

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def zopz0zKzJ_s (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toInt x) ≥b (BitVec.toInt y))

/-- Type quantifiers: k_n : Int -/
def zopz0zI_u (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toNat x) <b (BitVec.toNat y))

/-- Type quantifiers: k_n : Int -/
def zopz0zK_u (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toNat x) >b (BitVec.toNat y))

/-- Type quantifiers: k_n : Int -/
def zopz0zIzJ_u (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toNat x) ≤b (BitVec.toNat y))

/-- Type quantifiers: k_n : Int -/
def zopz0zKzJ_u (x : (BitVec k_n)) (y : (BitVec k_n)) : Bool :=
  ((BitVec.toNat x) ≥b (BitVec.toNat y))

/-- Type quantifiers: shift : Nat, k_n : Nat, k_n ≥ 1 ∧ shift ≥ 0 -/
def shift_right_arith (value : (BitVec k_n)) (shift : Nat) : (BitVec k_n) :=
  (Sail.BitVec.extractLsb (sign_extend (m := ((Sail.BitVec.length value) +i shift)) value)
    (((Sail.BitVec.length value) -i 1) +i shift) shift)

/-- Type quantifiers: k_m : Int, k_n : Nat, k_n ≥ 1 -/
def shift_bits_right_arith (value : (BitVec k_n)) (shift : (BitVec k_m)) : (BitVec k_n) :=
  (shift_right_arith value (BitVec.toNat shift))

/-- Type quantifiers: k_n : Int, k_m : Nat, k_m ≥ 0 -/
def rotate_bits_right (v : (BitVec k_n)) (n : (BitVec k_m)) : (BitVec k_n) :=
  ((shift_bits_right v n) ||| (shift_bits_left v
      ((to_bits (Sail.BitVec.length n) (Sail.BitVec.length v)) - n)))

/-- Type quantifiers: k_n : Int, k_m : Nat, k_m ≥ 0 -/
def rotate_bits_left (v : (BitVec k_n)) (n : (BitVec k_m)) : (BitVec k_n) :=
  ((shift_bits_left v n) ||| (shift_bits_right v
      ((to_bits (Sail.BitVec.length n) (Sail.BitVec.length v)) - n)))

/-- Type quantifiers: k_m : Nat, n : Nat, k_m ≥ n ∧ n ≥ 0 -/
def rotater (v : (BitVec k_m)) (n : Nat) : (BitVec k_m) :=
  ((shiftr v n) ||| (shiftl v ((Sail.BitVec.length v) -i n)))

/-- Type quantifiers: k_m : Nat, n : Nat, k_m ≥ n ∧ n ≥ 0 -/
def rotatel (v : (BitVec k_m)) (n : Nat) : (BitVec k_m) :=
  ((shiftl v n) ||| (shiftr v ((Sail.BitVec.length v) -i n)))

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def reverse_bits (xs : (BitVec k_n)) : (BitVec k_n) := Id.run do
  let ys : (BitVec k_n) := (zeros (n := (Sail.BitVec.length xs)))
  let loop_i_lower := 0
  let loop_i_upper := ((Sail.BitVec.length ys) -i 1)
  let mut loop_vars := ys
  for i in [loop_i_lower:loop_i_upper:1]i do
    let ys := loop_vars
    loop_vars := (BitVec.update ys i (BitVec.access xs (((Sail.BitVec.length ys) -i 1) -i i)))
  (pure loop_vars)

/-- Type quantifiers: n : Nat, n ∈ {1, 2, 4, 8, 16, 32, 64} -/
def log2 (n : Nat) : Int :=
  match n with
  | 1 => 0
  | 2 => 1
  | 4 => 2
  | 8 => 3
  | 16 => 4
  | 32 => 5
  | _ => 6

/-- Type quantifiers: k_n : Int -/
def hex_bits_str (x : (BitVec k_n)) : String :=
  (BitVec.toFormatted
    (zero_extend
      (m := ((3 -i (Int.emod ((Sail.BitVec.length x) +i 3) 4)) +i (Sail.BitVec.length x))) x))

