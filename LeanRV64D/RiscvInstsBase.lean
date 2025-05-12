import LeanRV64D.RiscvZvkUtils

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

def encdec_uop_forwards (arg_ : uop) : (BitVec 7) :=
  match arg_ with
  | LUI => (0b0110111 : (BitVec 7))
  | AUIPC => (0b0010111 : (BitVec 7))

def encdec_uop_backwards (arg_ : (BitVec 7)) : SailM uop := do
  match_bv arg_ with
  | 0110111 => do (pure LUI)
  | 0010111 => do (pure AUIPC)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_uop_forwards_matches (arg_ : uop) : Bool :=
  match arg_ with
  | LUI => true
  | AUIPC => true
  | _ => false

def encdec_uop_backwards_matches (arg_ : (BitVec 7)) : Bool :=
  match_bv arg_ with
  | 0110111 => true
  | 0010111 => true
  | _ => false

def utype_mnemonic_backwards (arg_ : String) : SailM uop := do
  match arg_ with
  | "lui" => (pure LUI)
  | "auipc" => (pure AUIPC)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def utype_mnemonic_forwards_matches (arg_ : uop) : Bool :=
  match arg_ with
  | LUI => true
  | AUIPC => true
  | _ => false

def utype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "lui" => true
  | "auipc" => true
  | _ => false

def encdec_bop_forwards (arg_ : bop) : (BitVec 3) :=
  match arg_ with
  | BEQ => (0b000 : (BitVec 3))
  | BNE => (0b001 : (BitVec 3))
  | BLT => (0b100 : (BitVec 3))
  | BGE => (0b101 : (BitVec 3))
  | BLTU => (0b110 : (BitVec 3))
  | BGEU => (0b111 : (BitVec 3))

def encdec_bop_backwards (arg_ : (BitVec 3)) : SailM bop := do
  match_bv arg_ with
  | 000 => do (pure BEQ)
  | 001 => do (pure BNE)
  | 100 => do (pure BLT)
  | 101 => do (pure BGE)
  | 110 => do (pure BLTU)
  | 111 => do (pure BGEU)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_bop_forwards_matches (arg_ : bop) : Bool :=
  match arg_ with
  | BEQ => true
  | BNE => true
  | BLT => true
  | BGE => true
  | BLTU => true
  | BGEU => true
  | _ => false

def encdec_bop_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  match_bv arg_ with
  | 000 => true
  | 001 => true
  | 100 => true
  | 101 => true
  | 110 => true
  | 111 => true
  | _ => false

def btype_mnemonic_backwards (arg_ : String) : SailM bop := do
  match arg_ with
  | "beq" => (pure BEQ)
  | "bne" => (pure BNE)
  | "blt" => (pure BLT)
  | "bge" => (pure BGE)
  | "bltu" => (pure BLTU)
  | "bgeu" => (pure BGEU)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def btype_mnemonic_forwards_matches (arg_ : bop) : Bool :=
  match arg_ with
  | BEQ => true
  | BNE => true
  | BLT => true
  | BGE => true
  | BLTU => true
  | BGEU => true
  | _ => false

def btype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "beq" => true
  | "bne" => true
  | "blt" => true
  | "bge" => true
  | "bltu" => true
  | "bgeu" => true
  | _ => false

def encdec_iop_forwards (arg_ : iop) : (BitVec 3) :=
  match arg_ with
  | ADDI => (0b000 : (BitVec 3))
  | SLTI => (0b010 : (BitVec 3))
  | SLTIU => (0b011 : (BitVec 3))
  | ANDI => (0b111 : (BitVec 3))
  | ORI => (0b110 : (BitVec 3))
  | XORI => (0b100 : (BitVec 3))

def encdec_iop_backwards (arg_ : (BitVec 3)) : SailM iop := do
  match_bv arg_ with
  | 000 => do (pure ADDI)
  | 010 => do (pure SLTI)
  | 011 => do (pure SLTIU)
  | 111 => do (pure ANDI)
  | 110 => do (pure ORI)
  | 100 => do (pure XORI)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_iop_forwards_matches (arg_ : iop) : Bool :=
  match arg_ with
  | ADDI => true
  | SLTI => true
  | SLTIU => true
  | ANDI => true
  | ORI => true
  | XORI => true
  | _ => false

def encdec_iop_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  match_bv arg_ with
  | 000 => true
  | 010 => true
  | 011 => true
  | 111 => true
  | 110 => true
  | 100 => true
  | _ => false

def itype_mnemonic_backwards (arg_ : String) : SailM iop := do
  match arg_ with
  | "addi" => (pure ADDI)
  | "slti" => (pure SLTI)
  | "sltiu" => (pure SLTIU)
  | "xori" => (pure XORI)
  | "ori" => (pure ORI)
  | "andi" => (pure ANDI)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def itype_mnemonic_forwards_matches (arg_ : iop) : Bool :=
  match arg_ with
  | ADDI => true
  | SLTI => true
  | SLTIU => true
  | XORI => true
  | ORI => true
  | ANDI => true
  | _ => false

def itype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "addi" => true
  | "slti" => true
  | "sltiu" => true
  | "xori" => true
  | "ori" => true
  | "andi" => true
  | _ => false

def encdec_sop_forwards (arg_ : sop) : (BitVec 3) :=
  match arg_ with
  | SLLI => (0b001 : (BitVec 3))
  | SRLI => (0b101 : (BitVec 3))
  | SRAI => (0b101 : (BitVec 3))

def encdec_sop_backwards (arg_ : (BitVec 3)) : SailM sop := do
  match_bv arg_ with
  | 001 => do (pure SLLI)
  | 101 => do (pure SRLI)
  | 101 => do (pure SRAI)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_sop_forwards_matches (arg_ : sop) : Bool :=
  match arg_ with
  | SLLI => true
  | SRLI => true
  | SRAI => true
  | _ => false

def encdec_sop_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  match_bv arg_ with
  | 001 => true
  | 101 => true
  | 101 => true
  | _ => false

def shiftiop_mnemonic_backwards (arg_ : String) : SailM sop := do
  match arg_ with
  | "slli" => (pure SLLI)
  | "srli" => (pure SRLI)
  | "srai" => (pure SRAI)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def shiftiop_mnemonic_forwards_matches (arg_ : sop) : Bool :=
  match arg_ with
  | SLLI => true
  | SRLI => true
  | SRAI => true
  | _ => false

def shiftiop_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "slli" => true
  | "srli" => true
  | "srai" => true
  | _ => false

def rtype_mnemonic_backwards (arg_ : String) : SailM rop := do
  match arg_ with
  | "add" => (pure ADD)
  | "slt" => (pure SLT)
  | "sltu" => (pure SLTU)
  | "and" => (pure AND)
  | "or" => (pure OR)
  | "xor" => (pure XOR)
  | "sll" => (pure SLL)
  | "srl" => (pure SRL)
  | "sub" => (pure SUB)
  | "sra" => (pure SRA)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def rtype_mnemonic_forwards_matches (arg_ : rop) : Bool :=
  match arg_ with
  | ADD => true
  | SLT => true
  | SLTU => true
  | AND => true
  | OR => true
  | XOR => true
  | SLL => true
  | SRL => true
  | SUB => true
  | SRA => true
  | _ => false

def rtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "add" => true
  | "slt" => true
  | "sltu" => true
  | "and" => true
  | "or" => true
  | "xor" => true
  | "sll" => true
  | "srl" => true
  | "sub" => true
  | "sra" => true
  | _ => false

/-- Type quantifiers: k_ex284886# : Bool -/
def valid_load_encdec (width : word_width) (is_unsigned : Bool) : Bool :=
  (((size_bytes_forwards width) <b xlen_bytes) || ((not is_unsigned) && (((size_bytes_forwards width) ≤b xlen_bytes) : Bool)))

/-- Type quantifiers: k_ex284922# : Bool, k_n : Nat, 0 < k_n ∧ k_n ≤ xlen -/
def extend_value (is_unsigned : Bool) (value : (BitVec k_n)) : (BitVec (2 ^ 3 * 8)) :=
  bif is_unsigned
  then (zero_extend (m := ((2 ^i 3) *i 8)) value)
  else (sign_extend (m := ((2 ^i 3) *i 8)) value)

def maybe_aq_backwards (arg_ : String) : SailM Bool := do
  match arg_ with
  | ".aq" => (pure true)
  | "" => (pure false)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: k_ex284923# : Bool -/
def maybe_aq_forwards_matches (arg_ : Bool) : Bool :=
  match arg_ with
  | true => true
  | false => true
  | _ => false

def maybe_aq_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | ".aq" => true
  | "" => true
  | _ => false

def maybe_rl_backwards (arg_ : String) : SailM Bool := do
  match arg_ with
  | ".rl" => (pure true)
  | "" => (pure false)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: k_ex284924# : Bool -/
def maybe_rl_forwards_matches (arg_ : Bool) : Bool :=
  match arg_ with
  | true => true
  | false => true
  | _ => false

def maybe_rl_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | ".rl" => true
  | "" => true
  | _ => false

def maybe_u_backwards (arg_ : String) : SailM Bool := do
  match arg_ with
  | "u" => (pure true)
  | "" => (pure false)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: k_ex284925# : Bool -/
def maybe_u_forwards_matches (arg_ : Bool) : Bool :=
  match arg_ with
  | true => true
  | false => true
  | _ => false

def maybe_u_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "u" => true
  | "" => true
  | _ => false

def rtypew_mnemonic_backwards (arg_ : String) : SailM ropw := do
  match arg_ with
  | "addw" => (pure ADDW)
  | "subw" => (pure SUBW)
  | "sllw" => (pure SLLW)
  | "srlw" => (pure SRLW)
  | "sraw" => (pure SRAW)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def rtypew_mnemonic_forwards_matches (arg_ : ropw) : Bool :=
  match arg_ with
  | ADDW => true
  | SUBW => true
  | SLLW => true
  | SRLW => true
  | SRAW => true
  | _ => false

def rtypew_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "addw" => true
  | "subw" => true
  | "sllw" => true
  | "srlw" => true
  | "sraw" => true
  | _ => false

def shiftiwop_mnemonic_backwards (arg_ : String) : SailM sopw := do
  match arg_ with
  | "slliw" => (pure SLLIW)
  | "srliw" => (pure SRLIW)
  | "sraiw" => (pure SRAIW)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def shiftiwop_mnemonic_forwards_matches (arg_ : sopw) : Bool :=
  match arg_ with
  | SLLIW => true
  | SRLIW => true
  | SRAIW => true
  | _ => false

def shiftiwop_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "slliw" => true
  | "srliw" => true
  | "sraiw" => true
  | _ => false

/-- Type quantifiers: k_ex284926# : Bool -/
def effective_fence_set (set : (BitVec 4)) (fiom : Bool) : (BitVec 4) :=
  bif fiom
  then
    ((Sail.BitVec.extractLsb set 3 2) ++ ((Sail.BitVec.extractLsb set 1 0) ||| (Sail.BitVec.extractLsb
          set 3 2)))
  else set

def bit_maybe_r_backwards (arg_ : String) : SailM (BitVec 1) := do
  match arg_ with
  | "r" => (pure (0b1 : (BitVec 1)))
  | "" => (pure (0b0 : (BitVec 1)))
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def bit_maybe_r_forwards_matches (arg_ : (BitVec 1)) : Bool :=
  match_bv arg_ with
  | 1 => true
  | 0 => true
  | _ => false

def bit_maybe_r_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "r" => true
  | "" => true
  | _ => false

def bit_maybe_w_backwards (arg_ : String) : SailM (BitVec 1) := do
  match arg_ with
  | "w" => (pure (0b1 : (BitVec 1)))
  | "" => (pure (0b0 : (BitVec 1)))
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def bit_maybe_w_forwards_matches (arg_ : (BitVec 1)) : Bool :=
  match_bv arg_ with
  | 1 => true
  | 0 => true
  | _ => false

def bit_maybe_w_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "w" => true
  | "" => true
  | _ => false

def bit_maybe_i_backwards (arg_ : String) : SailM (BitVec 1) := do
  match arg_ with
  | "i" => (pure (0b1 : (BitVec 1)))
  | "" => (pure (0b0 : (BitVec 1)))
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def bit_maybe_i_forwards_matches (arg_ : (BitVec 1)) : Bool :=
  match_bv arg_ with
  | 1 => true
  | 0 => true
  | _ => false

def bit_maybe_i_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "i" => true
  | "" => true
  | _ => false

def bit_maybe_o_backwards (arg_ : String) : SailM (BitVec 1) := do
  match arg_ with
  | "o" => (pure (0b1 : (BitVec 1)))
  | "" => (pure (0b0 : (BitVec 1)))
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def bit_maybe_o_forwards_matches (arg_ : (BitVec 1)) : Bool :=
  match_bv arg_ with
  | 1 => true
  | 0 => true
  | _ => false

def bit_maybe_o_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "o" => true
  | "" => true
  | _ => false

def fence_bits_backwards (arg_ : String) : SailM (BitVec 4) := do
  match arg_ with
  | _ => throw Error.Exit

def fence_bits_forwards_matches (arg_ : (BitVec 4)) : Bool :=
  match_bv arg_ with
  | [i:1,o:1,r:1,w:1] => true
  | _ => false

def fence_bits_backwards_matches (arg_ : String) : SailM Bool := do
  match arg_ with
  | _ => throw Error.Exit
  | _ => (pure false)

