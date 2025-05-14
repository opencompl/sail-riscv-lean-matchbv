import LeanRV64D.RiscvTypesExt

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

def xlen_max_unsigned := ((2 ^i xlen) -i 1)

def xlen_max_signed := ((2 ^i (xlen -i 1)) -i 1)

def xlen_min_signed := (0 -i (2 ^i (xlen -i 1)))

def pagesize_bits := 12

def regidx_offset (typ_0 : regidx) (o : (BitVec 5)) : regidx :=
  let .Regidx r : regidx := typ_0
  (Regidx (r + o))

def regidx_bits (app_0 : regidx) : (BitVec 5) :=
  let .Regidx b := app_0
  b

def regidx_to_regno (app_0 : regidx) : regno :=
  let .Regidx b := app_0
  (Regno (BitVec.toNat b))

def regno_to_regidx (app_0 : regno) : regidx :=
  let .Regno b := app_0
  (Regidx (to_bits 5 b))

def creg2reg_idx (app_0 : cregidx) : regidx :=
  let .Cregidx i := app_0
  (Regidx ((0b01 : (BitVec 2)) ++ i))

def zreg : regidx := (Regidx (0b00000 : (BitVec 5)))

def ra : regidx := (Regidx (0b00001 : (BitVec 5)))

def sp : regidx := (Regidx (0b00010 : (BitVec 5)))

def undefined_Architecture (_ : Unit) : SailM Architecture := do
  (internal_pick [RV32, RV64, RV128])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Architecture_of_num (arg_ : Nat) : Architecture :=
  match arg_ with
  | 0 => RV32
  | 1 => RV64
  | _ => RV128

def num_of_Architecture (arg_ : Architecture) : Int :=
  match arg_ with
  | RV32 => 0
  | RV64 => 1
  | RV128 => 2

def architecture_forwards (arg_ : Architecture) : (BitVec 2) :=
  match arg_ with
  | RV32 => (0b01 : (BitVec 2))
  | RV64 => (0b10 : (BitVec 2))
  | RV128 => (0b11 : (BitVec 2))

def architecture_backwards (arg_ : (BitVec 2)) : SailM Architecture := do
  match_bv arg_ with
  | 01 => do (pure RV32)
  | 10 => do (pure RV64)
  | 11 => do (pure RV128)
  | _ => do (internal_error "riscv_types.sail" 57 "architecture(0b00) is invalid")

def architecture_forwards_matches (arg_ : Architecture) : Bool :=
  match arg_ with
  | RV32 => true
  | RV64 => true
  | RV128 => true
  | _ => false

def architecture_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match_bv arg_ with
  | 01 => true
  | 10 => true
  | 11 => true
  | 00 => true
  | _ => false

def undefined_Privilege (_ : Unit) : SailM Privilege := do
  (internal_pick [User, Supervisor, Machine])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Privilege_of_num (arg_ : Nat) : Privilege :=
  match arg_ with
  | 0 => User
  | 1 => Supervisor
  | _ => Machine

def num_of_Privilege (arg_ : Privilege) : Int :=
  match arg_ with
  | User => 0
  | Supervisor => 1
  | Machine => 2

def privLevel_bits_forwards (arg_ : Privilege) : (BitVec 2) :=
  match arg_ with
  | User => (0b00 : (BitVec 2))
  | Supervisor => (0b01 : (BitVec 2))
  | Machine => (0b11 : (BitVec 2))

def privLevel_bits_backwards (arg_ : (BitVec 2)) : SailM Privilege := do
  match_bv arg_ with
  | 00 => do (pure User)
  | 01 => do (pure Supervisor)
  | 11 => do (pure Machine)
  | _ => do
    (internal_error "riscv_types.sail" 69
      (HAppend.hAppend "Invalid privilege level: " (BitVec.toFormatted (0b10 : (BitVec 2)))))

def privLevel_bits_forwards_matches (arg_ : Privilege) : Bool :=
  match arg_ with
  | User => true
  | Supervisor => true
  | Machine => true
  | _ => false

def privLevel_bits_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match_bv arg_ with
  | 00 => true
  | 01 => true
  | 11 => true
  | 10 => true
  | _ => false

def privLevel_to_bits (p : Privilege) : (BitVec 2) :=
  (privLevel_bits_forwards p)

def privLevel_of_bits (b : (BitVec 2)) : SailM Privilege := do
  (privLevel_bits_backwards b)

def privLevel_to_str (p : Privilege) : String :=
  match p with
  | User => "U"
  | Supervisor => "S"
  | Machine => "M"

def accessType_to_str (a : (AccessType Unit)) : String :=
  match a with
  | .Read _ => "R"
  | .Write _ => "W"
  | .ReadWrite (_, _) => "RW"
  | .InstructionFetch () => "X"

def csr_name_map_forwards (arg_ : (BitVec 12)) : SailM String := do
  match_bv arg_ with
  | 001100000001 => do (pure "misa")
  | 001100000000 => do (pure "mstatus")
  | 001100001010 => do (pure "menvcfg")
  | 001100011010 => do (pure "menvcfgh")
  | 000100001010 => do (pure "senvcfg")
  | 001100000100 => do (pure "mie")
  | 001101000100 => do (pure "mip")
  | 001100000010 => do (pure "medeleg")
  | 001100010010 => do (pure "medelegh")
  | 001100000011 => do (pure "mideleg")
  | 001101000010 => do (pure "mcause")
  | 001101000011 => do (pure "mtval")
  | 001101000000 => do (pure "mscratch")
  | 000100000110 => do (pure "scounteren")
  | 001100000110 => do (pure "mcounteren")
  | 001100100000 => do (pure "mcountinhibit")
  | 111100010001 => do (pure "mvendorid")
  | 111100010010 => do (pure "marchid")
  | 111100010011 => do (pure "mimpid")
  | 111100010100 => do (pure "mhartid")
  | 111100010101 => do (pure "mconfigptr")
  | 000100000000 => do (pure "sstatus")
  | 000101000100 => do (pure "sip")
  | 000100000100 => do (pure "sie")
  | 000101000000 => do (pure "sscratch")
  | 000101000010 => do (pure "scause")
  | 000101000011 => do (pure "stval")
  | 011110100000 => do (pure "tselect")
  | 011110100001 => do (pure "tdata1")
  | 011110100010 => do (pure "tdata2")
  | 011110100011 => do (pure "tdata3")
  | 001110100000 => do (pure "pmpcfg0")
  | 001110100001 => do (pure "pmpcfg1")
  | 001110100010 => do (pure "pmpcfg2")
  | 001110100011 => do (pure "pmpcfg3")
  | 001110100100 => do (pure "pmpcfg4")
  | 001110100101 => do (pure "pmpcfg5")
  | 001110100110 => do (pure "pmpcfg6")
  | 001110100111 => do (pure "pmpcfg7")
  | 001110101000 => do (pure "pmpcfg8")
  | 001110101001 => do (pure "pmpcfg9")
  | 001110101010 => do (pure "pmpcfg10")
  | 001110101011 => do (pure "pmpcfg11")
  | 001110101100 => do (pure "pmpcfg12")
  | 001110101101 => do (pure "pmpcfg13")
  | 001110101110 => do (pure "pmpcfg14")
  | 001110101111 => do (pure "pmpcfg15")
  | 001110110000 => do (pure "pmpaddr0")
  | 001110110001 => do (pure "pmpaddr1")
  | 001110110010 => do (pure "pmpaddr2")
  | 001110110011 => do (pure "pmpaddr3")
  | 001110110100 => do (pure "pmpaddr4")
  | 001110110101 => do (pure "pmpaddr5")
  | 001110110110 => do (pure "pmpaddr6")
  | 001110110111 => do (pure "pmpaddr7")
  | 001110111000 => do (pure "pmpaddr8")
  | 001110111001 => do (pure "pmpaddr9")
  | 001110111010 => do (pure "pmpaddr10")
  | 001110111011 => do (pure "pmpaddr11")
  | 001110111100 => do (pure "pmpaddr12")
  | 001110111101 => do (pure "pmpaddr13")
  | 001110111110 => do (pure "pmpaddr14")
  | 001110111111 => do (pure "pmpaddr15")
  | 001111000000 => do (pure "pmpaddr16")
  | 001111000001 => do (pure "pmpaddr17")
  | 001111000010 => do (pure "pmpaddr18")
  | 001111000011 => do (pure "pmpaddr19")
  | 001111000100 => do (pure "pmpaddr20")
  | 001111000101 => do (pure "pmpaddr21")
  | 001111000110 => do (pure "pmpaddr22")
  | 001111000111 => do (pure "pmpaddr23")
  | 001111001000 => do (pure "pmpaddr24")
  | 001111001001 => do (pure "pmpaddr25")
  | 001111001010 => do (pure "pmpaddr26")
  | 001111001011 => do (pure "pmpaddr27")
  | 001111001100 => do (pure "pmpaddr28")
  | 001111001101 => do (pure "pmpaddr29")
  | 001111001110 => do (pure "pmpaddr30")
  | 001111001111 => do (pure "pmpaddr31")
  | 001111010000 => do (pure "pmpaddr32")
  | 001111010001 => do (pure "pmpaddr33")
  | 001111010010 => do (pure "pmpaddr34")
  | 001111010011 => do (pure "pmpaddr35")
  | 001111010100 => do (pure "pmpaddr36")
  | 001111010101 => do (pure "pmpaddr37")
  | 001111010110 => do (pure "pmpaddr38")
  | 001111010111 => do (pure "pmpaddr39")
  | 001111011000 => do (pure "pmpaddr40")
  | 001111011001 => do (pure "pmpaddr41")
  | 001111011010 => do (pure "pmpaddr42")
  | 001111011011 => do (pure "pmpaddr43")
  | 001111011100 => do (pure "pmpaddr44")
  | 001111011101 => do (pure "pmpaddr45")
  | 001111011110 => do (pure "pmpaddr46")
  | 001111011111 => do (pure "pmpaddr47")
  | 001111100000 => do (pure "pmpaddr48")
  | 001111100001 => do (pure "pmpaddr49")
  | 001111100010 => do (pure "pmpaddr50")
  | 001111100011 => do (pure "pmpaddr51")
  | 001111100100 => do (pure "pmpaddr52")
  | 001111100101 => do (pure "pmpaddr53")
  | 001111100110 => do (pure "pmpaddr54")
  | 001111100111 => do (pure "pmpaddr55")
  | 001111101000 => do (pure "pmpaddr56")
  | 001111101001 => do (pure "pmpaddr57")
  | 001111101010 => do (pure "pmpaddr58")
  | 001111101011 => do (pure "pmpaddr59")
  | 001111101100 => do (pure "pmpaddr60")
  | 001111101101 => do (pure "pmpaddr61")
  | 001111101110 => do (pure "pmpaddr62")
  | 001111101111 => do (pure "pmpaddr63")
  | 000000001000 => do (pure "vstart")
  | 000000001001 => do (pure "vxsat")
  | 000000001010 => do (pure "vxrm")
  | 000000001111 => do (pure "vcsr")
  | 110000100000 => do (pure "vl")
  | 110000100001 => do (pure "vtype")
  | 110000100010 => do (pure "vlenb")
  | 000100000101 => do (pure "stvec")
  | 000101000001 => do (pure "sepc")
  | 001100000101 => do (pure "mtvec")
  | 001101000001 => do (pure "mepc")
  | 110000000011 => do (pure "hpmcounter3")
  | 110000000100 => do (pure "hpmcounter4")
  | 110000000101 => do (pure "hpmcounter5")
  | 110000000110 => do (pure "hpmcounter6")
  | 110000000111 => do (pure "hpmcounter7")
  | 110000001000 => do (pure "hpmcounter8")
  | 110000001001 => do (pure "hpmcounter9")
  | 110000001010 => do (pure "hpmcounter10")
  | 110000001011 => do (pure "hpmcounter11")
  | 110000001100 => do (pure "hpmcounter12")
  | 110000001101 => do (pure "hpmcounter13")
  | 110000001110 => do (pure "hpmcounter14")
  | 110000001111 => do (pure "hpmcounter15")
  | 110000010000 => do (pure "hpmcounter16")
  | 110000010001 => do (pure "hpmcounter17")
  | 110000010010 => do (pure "hpmcounter18")
  | 110000010011 => do (pure "hpmcounter19")
  | 110000010100 => do (pure "hpmcounter20")
  | 110000010101 => do (pure "hpmcounter21")
  | 110000010110 => do (pure "hpmcounter22")
  | 110000010111 => do (pure "hpmcounter23")
  | 110000011000 => do (pure "hpmcounter24")
  | 110000011001 => do (pure "hpmcounter25")
  | 110000011010 => do (pure "hpmcounter26")
  | 110000011011 => do (pure "hpmcounter27")
  | 110000011100 => do (pure "hpmcounter28")
  | 110000011101 => do (pure "hpmcounter29")
  | 110000011110 => do (pure "hpmcounter30")
  | 110000011111 => do (pure "hpmcounter31")
  | 110010000011 => do (pure "hpmcounter3h")
  | 110010000100 => do (pure "hpmcounter4h")
  | 110010000101 => do (pure "hpmcounter5h")
  | 110010000110 => do (pure "hpmcounter6h")
  | 110010000111 => do (pure "hpmcounter7h")
  | 110010001000 => do (pure "hpmcounter8h")
  | 110010001001 => do (pure "hpmcounter9h")
  | 110010001010 => do (pure "hpmcounter10h")
  | 110010001011 => do (pure "hpmcounter11h")
  | 110010001100 => do (pure "hpmcounter12h")
  | 110010001101 => do (pure "hpmcounter13h")
  | 110010001110 => do (pure "hpmcounter14h")
  | 110010001111 => do (pure "hpmcounter15h")
  | 110010010000 => do (pure "hpmcounter16h")
  | 110010010001 => do (pure "hpmcounter17h")
  | 110010010010 => do (pure "hpmcounter18h")
  | 110010010011 => do (pure "hpmcounter19h")
  | 110010010100 => do (pure "hpmcounter20h")
  | 110010010101 => do (pure "hpmcounter21h")
  | 110010010110 => do (pure "hpmcounter22h")
  | 110010010111 => do (pure "hpmcounter23h")
  | 110010011000 => do (pure "hpmcounter24h")
  | 110010011001 => do (pure "hpmcounter25h")
  | 110010011010 => do (pure "hpmcounter26h")
  | 110010011011 => do (pure "hpmcounter27h")
  | 110010011100 => do (pure "hpmcounter28h")
  | 110010011101 => do (pure "hpmcounter29h")
  | 110010011110 => do (pure "hpmcounter30h")
  | 110010011111 => do (pure "hpmcounter31h")
  | 001100100011 => do (pure "mhpmevent3")
  | 001100100100 => do (pure "mhpmevent4")
  | 001100100101 => do (pure "mhpmevent5")
  | 001100100110 => do (pure "mhpmevent6")
  | 001100100111 => do (pure "mhpmevent7")
  | 001100101000 => do (pure "mhpmevent8")
  | 001100101001 => do (pure "mhpmevent9")
  | 001100101010 => do (pure "mhpmevent10")
  | 001100101011 => do (pure "mhpmevent11")
  | 001100101100 => do (pure "mhpmevent12")
  | 001100101101 => do (pure "mhpmevent13")
  | 001100101110 => do (pure "mhpmevent14")
  | 001100101111 => do (pure "mhpmevent15")
  | 001100110000 => do (pure "mhpmevent16")
  | 001100110001 => do (pure "mhpmevent17")
  | 001100110010 => do (pure "mhpmevent18")
  | 001100110011 => do (pure "mhpmevent19")
  | 001100110100 => do (pure "mhpmevent20")
  | 001100110101 => do (pure "mhpmevent21")
  | 001100110110 => do (pure "mhpmevent22")
  | 001100110111 => do (pure "mhpmevent23")
  | 001100111000 => do (pure "mhpmevent24")
  | 001100111001 => do (pure "mhpmevent25")
  | 001100111010 => do (pure "mhpmevent26")
  | 001100111011 => do (pure "mhpmevent27")
  | 001100111100 => do (pure "mhpmevent28")
  | 001100111101 => do (pure "mhpmevent29")
  | 001100111110 => do (pure "mhpmevent30")
  | 001100111111 => do (pure "mhpmevent31")
  | 101100000011 => do (pure "mhpmcounter3")
  | 101100000100 => do (pure "mhpmcounter4")
  | 101100000101 => do (pure "mhpmcounter5")
  | 101100000110 => do (pure "mhpmcounter6")
  | 101100000111 => do (pure "mhpmcounter7")
  | 101100001000 => do (pure "mhpmcounter8")
  | 101100001001 => do (pure "mhpmcounter9")
  | 101100001010 => do (pure "mhpmcounter10")
  | 101100001011 => do (pure "mhpmcounter11")
  | 101100001100 => do (pure "mhpmcounter12")
  | 101100001101 => do (pure "mhpmcounter13")
  | 101100001110 => do (pure "mhpmcounter14")
  | 101100001111 => do (pure "mhpmcounter15")
  | 101100010000 => do (pure "mhpmcounter16")
  | 101100010001 => do (pure "mhpmcounter17")
  | 101100010010 => do (pure "mhpmcounter18")
  | 101100010011 => do (pure "mhpmcounter19")
  | 101100010100 => do (pure "mhpmcounter20")
  | 101100010101 => do (pure "mhpmcounter21")
  | 101100010110 => do (pure "mhpmcounter22")
  | 101100010111 => do (pure "mhpmcounter23")
  | 101100011000 => do (pure "mhpmcounter24")
  | 101100011001 => do (pure "mhpmcounter25")
  | 101100011010 => do (pure "mhpmcounter26")
  | 101100011011 => do (pure "mhpmcounter27")
  | 101100011100 => do (pure "mhpmcounter28")
  | 101100011101 => do (pure "mhpmcounter29")
  | 101100011110 => do (pure "mhpmcounter30")
  | 101100011111 => do (pure "mhpmcounter31")
  | 101110000011 => do (pure "mhpmcounter3h")
  | 101110000100 => do (pure "mhpmcounter4h")
  | 101110000101 => do (pure "mhpmcounter5h")
  | 101110000110 => do (pure "mhpmcounter6h")
  | 101110000111 => do (pure "mhpmcounter7h")
  | 101110001000 => do (pure "mhpmcounter8h")
  | 101110001001 => do (pure "mhpmcounter9h")
  | 101110001010 => do (pure "mhpmcounter10h")
  | 101110001011 => do (pure "mhpmcounter11h")
  | 101110001100 => do (pure "mhpmcounter12h")
  | 101110001101 => do (pure "mhpmcounter13h")
  | 101110001110 => do (pure "mhpmcounter14h")
  | 101110001111 => do (pure "mhpmcounter15h")
  | 101110010000 => do (pure "mhpmcounter16h")
  | 101110010001 => do (pure "mhpmcounter17h")
  | 101110010010 => do (pure "mhpmcounter18h")
  | 101110010011 => do (pure "mhpmcounter19h")
  | 101110010100 => do (pure "mhpmcounter20h")
  | 101110010101 => do (pure "mhpmcounter21h")
  | 101110010110 => do (pure "mhpmcounter22h")
  | 101110010111 => do (pure "mhpmcounter23h")
  | 101110011000 => do (pure "mhpmcounter24h")
  | 101110011001 => do (pure "mhpmcounter25h")
  | 101110011010 => do (pure "mhpmcounter26h")
  | 101110011011 => do (pure "mhpmcounter27h")
  | 101110011100 => do (pure "mhpmcounter28h")
  | 101110011101 => do (pure "mhpmcounter29h")
  | 101110011110 => do (pure "mhpmcounter30h")
  | 101110011111 => do (pure "mhpmcounter31h")
  | 101110000011 => do (pure "mhpmcounter3h")
  | 101110000100 => do (pure "mhpmcounter4h")
  | 101110000101 => do (pure "mhpmcounter5h")
  | 101110000110 => do (pure "mhpmcounter6h")
  | 101110000111 => do (pure "mhpmcounter7h")
  | 101110001000 => do (pure "mhpmcounter8h")
  | 101110001001 => do (pure "mhpmcounter9h")
  | 101110001010 => do (pure "mhpmcounter10h")
  | 101110001011 => do (pure "mhpmcounter11h")
  | 101110001100 => do (pure "mhpmcounter12h")
  | 101110001101 => do (pure "mhpmcounter13h")
  | 101110001110 => do (pure "mhpmcounter14h")
  | 101110001111 => do (pure "mhpmcounter15h")
  | 101110010000 => do (pure "mhpmcounter16h")
  | 101110010001 => do (pure "mhpmcounter17h")
  | 101110010010 => do (pure "mhpmcounter18h")
  | 101110010011 => do (pure "mhpmcounter19h")
  | 101110010100 => do (pure "mhpmcounter20h")
  | 101110010101 => do (pure "mhpmcounter21h")
  | 101110010110 => do (pure "mhpmcounter22h")
  | 101110010111 => do (pure "mhpmcounter23h")
  | 101110011000 => do (pure "mhpmcounter24h")
  | 101110011001 => do (pure "mhpmcounter25h")
  | 101110011010 => do (pure "mhpmcounter26h")
  | 101110011011 => do (pure "mhpmcounter27h")
  | 101110011100 => do (pure "mhpmcounter28h")
  | 101110011101 => do (pure "mhpmcounter29h")
  | 101110011110 => do (pure "mhpmcounter30h")
  | 101110011111 => do (pure "mhpmcounter31h")
  | 110110100000 => do (pure "scountovf")
  | 000000010101 => do (pure "seed")
  | 110000000000 => do (pure "cycle")
  | 110000000001 => do (pure "time")
  | 110000000010 => do (pure "instret")
  | 110010000000 => do (pure "cycleh")
  | 110010000001 => do (pure "timeh")
  | 110010000010 => do (pure "instreth")
  | 101100000000 => do (pure "mcycle")
  | 101100000010 => do (pure "minstret")
  | 101110000000 => do (pure "mcycleh")
  | 101110000010 => do (pure "minstreth")
  | 000000000001 => do (pure "fflags")
  | 000000000010 => do (pure "frm")
  | 000000000011 => do (pure "fcsr")
  | 001100100001 => do (pure "mcyclecfg")
  | 011100100001 => do (pure "mcyclecfgh")
  | 001100100010 => do (pure "minstretcfg")
  | 011100100010 => do (pure "minstretcfgh")
  | 000101001101 => do (pure "stimecmp")
  | 000101011101 => do (pure "stimecmph")
  | 000110000000 => do (pure "satp")
  | reg => do (hex_bits_12_forwards reg)

def csr_name (csr : (BitVec 12)) : SailM String := do
  (csr_name_map_forwards csr)

def exceptionType_to_str (e : ExceptionType) : String :=
  match e with
  | .E_Fetch_Addr_Align () => "misaligned-fetch"
  | .E_Fetch_Access_Fault () => "fetch-access-fault"
  | .E_Illegal_Instr () => "illegal-instruction"
  | .E_Breakpoint () => "breakpoint"
  | .E_Load_Addr_Align () => "misaligned-load"
  | .E_Load_Access_Fault () => "load-access-fault"
  | .E_SAMO_Addr_Align () => "misaligned-store/amo"
  | .E_SAMO_Access_Fault () => "store/amo-access-fault"
  | .E_U_EnvCall () => "u-call"
  | .E_S_EnvCall () => "s-call"
  | .E_Reserved_10 () => "reserved-0"
  | .E_M_EnvCall () => "m-call"
  | .E_Fetch_Page_Fault () => "fetch-page-fault"
  | .E_Load_Page_Fault () => "load-page-fault"
  | .E_Reserved_14 () => "reserved-1"
  | .E_SAMO_Page_Fault () => "store/amo-page-fault"
  | .E_Extension e => (ext_exc_type_to_str e)

def amo_mnemonic_forwards (arg_ : amoop) : String :=
  match arg_ with
  | AMOSWAP => "amoswap"
  | AMOADD => "amoadd"
  | AMOXOR => "amoxor"
  | AMOAND => "amoand"
  | AMOOR => "amoor"
  | AMOMIN => "amomin"
  | AMOMAX => "amomax"
  | AMOMINU => "amominu"
  | AMOMAXU => "amomaxu"

def btype_mnemonic_forwards (arg_ : bop) : String :=
  match arg_ with
  | BEQ => "beq"
  | BNE => "bne"
  | BLT => "blt"
  | BGE => "bge"
  | BLTU => "bltu"
  | BGEU => "bgeu"

def cbop_mnemonic_forwards (arg_ : cbop_zicbom) : String :=
  match arg_ with
  | CBO_CLEAN => "cbo.clean"
  | CBO_FLUSH => "cbo.flush"
  | CBO_INVAL => "cbo.inval"

def creg_name_raw_forwards (arg_ : (BitVec 3)) : String :=
  match_bv arg_ with
  | 000 => "s0"
  | 001 => "s1"
  | 010 => "a0"
  | 011 => "a1"
  | 100 => "a2"
  | 101 => "a3"
  | 110 => "a4"
  | _ => "a5"

def creg_name_forwards (arg_ : cregidx) : String :=
  match arg_ with
  | .Cregidx i => (creg_name_raw_forwards i)

def csr_mnemonic_forwards (arg_ : csrop) : String :=
  match arg_ with
  | CSRRW => "csrrw"
  | CSRRS => "csrrs"
  | CSRRC => "csrrc"

def f_bin_f_type_mnemonic_D_forwards (arg_ : f_bin_f_op_D) : String :=
  match arg_ with
  | FSGNJ_D => "fsgnj.d"
  | FSGNJN_D => "fsgnjn.d"
  | FSGNJX_D => "fsgnjx.d"
  | FMIN_D => "fmin.d"
  | FMAX_D => "fmax.d"

def f_bin_f_type_mnemonic_H_forwards (arg_ : f_bin_f_op_H) : String :=
  match arg_ with
  | FSGNJ_H => "fsgnj.h"
  | FSGNJN_H => "fsgnjn.h"
  | FSGNJX_H => "fsgnjx.h"
  | FMIN_H => "fmin.h"
  | FMAX_H => "fmax.h"

def f_bin_rm_type_mnemonic_D_forwards (arg_ : f_bin_rm_op_D) : String :=
  match arg_ with
  | FADD_D => "fadd.d"
  | FSUB_D => "fsub.d"
  | FMUL_D => "fmul.d"
  | FDIV_D => "fdiv.d"

def f_bin_rm_type_mnemonic_H_forwards (arg_ : f_bin_rm_op_H) : String :=
  match arg_ with
  | FADD_H => "fadd.h"
  | FSUB_H => "fsub.h"
  | FMUL_H => "fmul.h"
  | FDIV_H => "fdiv.h"

def f_bin_rm_type_mnemonic_S_forwards (arg_ : f_bin_rm_op_S) : String :=
  match arg_ with
  | FADD_S => "fadd.s"
  | FSUB_S => "fsub.s"
  | FMUL_S => "fmul.s"
  | FDIV_S => "fdiv.s"

def f_bin_type_mnemonic_f_S_forwards (arg_ : f_bin_op_f_S) : String :=
  match arg_ with
  | FSGNJ_S => "fsgnj.s"
  | FSGNJN_S => "fsgnjn.s"
  | FSGNJX_S => "fsgnjx.s"
  | FMIN_S => "fmin.s"
  | FMAX_S => "fmax.s"

def f_bin_type_mnemonic_x_S_forwards (arg_ : f_bin_op_x_S) : String :=
  match arg_ with
  | FEQ_S => "feq.s"
  | FLT_S => "flt.s"
  | FLE_S => "fle.s"

def f_bin_x_type_mnemonic_D_forwards (arg_ : f_bin_x_op_D) : String :=
  match arg_ with
  | FEQ_D => "feq.d"
  | FLT_D => "flt.d"
  | FLE_D => "fle.d"

def f_bin_x_type_mnemonic_H_forwards (arg_ : f_bin_x_op_H) : String :=
  match arg_ with
  | FEQ_H => "feq.h"
  | FLT_H => "flt.h"
  | FLE_H => "fle.h"

def f_madd_type_mnemonic_D_forwards (arg_ : f_madd_op_D) : String :=
  match arg_ with
  | FMADD_D => "fmadd.d"
  | FMSUB_D => "fmsub.d"
  | FNMSUB_D => "fnmsub.d"
  | FNMADD_D => "fnmadd.d"

def f_madd_type_mnemonic_H_forwards (arg_ : f_madd_op_H) : String :=
  match arg_ with
  | FMADD_H => "fmadd.h"
  | FMSUB_H => "fmsub.h"
  | FNMSUB_H => "fnmsub.h"
  | FNMADD_H => "fnmadd.h"

def f_madd_type_mnemonic_S_forwards (arg_ : f_madd_op_S) : String :=
  match arg_ with
  | FMADD_S => "fmadd.s"
  | FMSUB_S => "fmsub.s"
  | FNMSUB_S => "fnmsub.s"
  | FNMADD_S => "fnmadd.s"

def f_un_f_type_mnemonic_D_forwards (arg_ : f_un_f_op_D) : String :=
  match arg_ with
  | FMV_D_X => "fmv.d.x"

def f_un_f_type_mnemonic_H_forwards (arg_ : f_un_f_op_H) : String :=
  match arg_ with
  | FMV_H_X => "fmv.h.x"

def f_un_rm_ff_type_mnemonic_D_forwards (arg_ : f_un_rm_ff_op_D) : String :=
  match arg_ with
  | FSQRT_D => "fsqrt.d"
  | FCVT_S_D => "fcvt.s.d"
  | FCVT_D_S => "fcvt.d.s"

def f_un_rm_ff_type_mnemonic_H_forwards (arg_ : f_un_rm_ff_op_H) : String :=
  match arg_ with
  | FSQRT_H => "fsqrt.h"
  | FCVT_H_S => "fcvt.h.s"
  | FCVT_H_D => "fcvt.h.d"
  | FCVT_S_H => "fcvt.s.h"
  | FCVT_D_H => "fcvt.d.h"

def f_un_rm_fx_type_mnemonic_D_forwards (arg_ : f_un_rm_fx_op_D) : String :=
  match arg_ with
  | FCVT_W_D => "fcvt.w.d"
  | FCVT_WU_D => "fcvt.wu.d"
  | FCVT_L_D => "fcvt.l.d"
  | FCVT_LU_D => "fcvt.lu.d"

def f_un_rm_fx_type_mnemonic_H_forwards (arg_ : f_un_rm_fx_op_H) : String :=
  match arg_ with
  | FCVT_W_H => "fcvt.w.h"
  | FCVT_WU_H => "fcvt.wu.h"
  | FCVT_L_H => "fcvt.l.h"
  | FCVT_LU_H => "fcvt.lu.h"

def f_un_rm_fx_type_mnemonic_S_forwards (arg_ : f_un_rm_fx_op_S) : String :=
  match arg_ with
  | FCVT_W_S => "fcvt.w.s"
  | FCVT_WU_S => "fcvt.wu.s"
  | FCVT_L_S => "fcvt.l.s"
  | FCVT_LU_S => "fcvt.lu.s"

def f_un_rm_xf_type_mnemonic_D_forwards (arg_ : f_un_rm_xf_op_D) : String :=
  match arg_ with
  | FCVT_D_W => "fcvt.d.w"
  | FCVT_D_WU => "fcvt.d.wu"
  | FCVT_D_L => "fcvt.d.l"
  | FCVT_D_LU => "fcvt.d.lu"

def f_un_rm_xf_type_mnemonic_H_forwards (arg_ : f_un_rm_xf_op_H) : String :=
  match arg_ with
  | FCVT_H_W => "fcvt.h.w"
  | FCVT_H_WU => "fcvt.h.wu"
  | FCVT_H_L => "fcvt.h.l"
  | FCVT_H_LU => "fcvt.h.lu"

def f_un_rm_xf_type_mnemonic_S_forwards (arg_ : f_un_rm_xf_op_S) : String :=
  match arg_ with
  | FCVT_S_W => "fcvt.s.w"
  | FCVT_S_WU => "fcvt.s.wu"
  | FCVT_S_L => "fcvt.s.l"
  | FCVT_S_LU => "fcvt.s.lu"

def f_un_type_mnemonic_f_S_forwards (arg_ : f_un_op_f_S) : String :=
  match arg_ with
  | FMV_W_X => "fmv.w.x"

def f_un_type_mnemonic_x_S_forwards (arg_ : f_un_op_x_S) : String :=
  match arg_ with
  | FCLASS_S => "fclass.s"
  | FMV_X_W => "fmv.x.w"

def f_un_x_type_mnemonic_D_forwards (arg_ : f_un_x_op_D) : String :=
  match arg_ with
  | FMV_X_D => "fmv.x.d"
  | FCLASS_D => "fclass.d"

def f_un_x_type_mnemonic_H_forwards (arg_ : f_un_x_op_H) : String :=
  match arg_ with
  | FMV_X_H => "fmv.x.h"
  | FCLASS_H => "fclass.h"

def bit_maybe_i_forwards (arg_ : (BitVec 1)) : String :=
  match_bv arg_ with
  | 1 => "i"
  | _ => ""

def bit_maybe_o_forwards (arg_ : (BitVec 1)) : String :=
  match_bv arg_ with
  | 1 => "o"
  | _ => ""

def bit_maybe_r_forwards (arg_ : (BitVec 1)) : String :=
  match_bv arg_ with
  | 1 => "r"
  | _ => ""

def bit_maybe_w_forwards (arg_ : (BitVec 1)) : String :=
  match_bv arg_ with
  | 1 => "w"
  | _ => ""

def fence_bits_forwards (arg_ : (BitVec 4)) : String :=
  match_bv arg_ with
  | [i:1,o:1,r:1,w:1] =>
    (String.append (bit_maybe_i_forwards i)
      (String.append (bit_maybe_o_forwards o)
        (String.append (bit_maybe_r_forwards r) (String.append (bit_maybe_w_forwards w) ""))))

def freg_name_raw_forwards (arg_ : (BitVec 5)) : String :=
  match_bv arg_ with
  | 00000 => "ft0"
  | 00001 => "ft1"
  | 00010 => "ft2"
  | 00011 => "ft3"
  | 00100 => "ft4"
  | 00101 => "ft5"
  | 00110 => "ft6"
  | 00111 => "ft7"
  | 01000 => "fs0"
  | 01001 => "fs1"
  | 01010 => "fa0"
  | 01011 => "fa1"
  | 01100 => "fa2"
  | 01101 => "fa3"
  | 01110 => "fa4"
  | 01111 => "fa5"
  | 10000 => "fa6"
  | 10001 => "fa7"
  | 10010 => "fs2"
  | 10011 => "fs3"
  | 10100 => "fs4"
  | 10101 => "fs5"
  | 10110 => "fs6"
  | 10111 => "fs7"
  | 11000 => "fs8"
  | 11001 => "fs9"
  | 11010 => "fs10"
  | 11011 => "fs11"
  | 11100 => "ft8"
  | 11101 => "ft9"
  | 11110 => "ft10"
  | _ => "ft11"

def freg_name_forwards (arg_ : fregidx) : String :=
  match arg_ with
  | .Fregidx i => (freg_name_raw_forwards i)

def fregidx_to_regidx (app_0 : fregidx) : regidx :=
  let .Fregidx b := app_0
  (Regidx (trunc (m := 5) b))

def reg_name_raw_forwards (arg_ : (BitVec 5)) : String :=
  match_bv arg_ with
  | 00000 => "zero"
  | 00001 => "ra"
  | 00010 => "sp"
  | 00011 => "gp"
  | 00100 => "tp"
  | 00101 => "t0"
  | 00110 => "t1"
  | 00111 => "t2"
  | 01000 => "fp"
  | 01001 => "s1"
  | 01010 => "a0"
  | 01011 => "a1"
  | 01100 => "a2"
  | 01101 => "a3"
  | 01110 => "a4"
  | 01111 => "a5"
  | 10000 => "a6"
  | 10001 => "a7"
  | 10010 => "s2"
  | 10011 => "s3"
  | 10100 => "s4"
  | 10101 => "s5"
  | 10110 => "s6"
  | 10111 => "s7"
  | 11000 => "s8"
  | 11001 => "s9"
  | 11010 => "s10"
  | 11011 => "s11"
  | 11100 => "t3"
  | 11101 => "t4"
  | 11110 => "t5"
  | _ => "t6"

def reg_name_forwards (arg_ : regidx) : String :=
  match arg_ with
  | .Regidx i => (reg_name_raw_forwards i)

def freg_or_reg_name_forwards (arg_ : fregidx) : String :=
  let f := arg_
  bif (hartSupports Ext_Zfinx)
  then (reg_name_forwards (fregidx_to_regidx f))
  else (freg_name_forwards f)

def frm_mnemonic_forwards (arg_ : rounding_mode) : String :=
  match arg_ with
  | RM_RNE => "rne"
  | RM_RTZ => "rtz"
  | RM_RDN => "rdn"
  | RM_RUP => "rup"
  | RM_RMM => "rmm"
  | RM_DYN => "dyn"

def fvfmatype_mnemonic_forwards (arg_ : fvfmafunct6) : String :=
  match arg_ with
  | VF_VMADD => "vfmadd.vf"
  | VF_VNMADD => "vfnmadd.vf"
  | VF_VMSUB => "vfmsub.vf"
  | VF_VNMSUB => "vfnmsub.vf"
  | VF_VMACC => "vfmacc.vf"
  | VF_VNMACC => "vfnmacc.vf"
  | VF_VMSAC => "vfmsac.vf"
  | VF_VNMSAC => "vfnmsac.vf"

def fvfmtype_mnemonic_forwards (arg_ : fvfmfunct6) : String :=
  match arg_ with
  | VFM_VMFEQ => "vmfeq.vf"
  | VFM_VMFLE => "vmfle.vf"
  | VFM_VMFLT => "vmflt.vf"
  | VFM_VMFNE => "vmfne.vf"
  | VFM_VMFGT => "vmfgt.vf"
  | VFM_VMFGE => "vmfge.vf"

def fvftype_mnemonic_forwards (arg_ : fvffunct6) : String :=
  match arg_ with
  | VF_VADD => "vfadd.vf"
  | VF_VSUB => "vfsub.vf"
  | VF_VMIN => "vfmin.vf"
  | VF_VMAX => "vfmax.vf"
  | VF_VSGNJ => "vfsgnj.vf"
  | VF_VSGNJN => "vfsgnjn.vf"
  | VF_VSGNJX => "vfsgnjx.vf"
  | VF_VSLIDE1UP => "vfslide1up.vf"
  | VF_VSLIDE1DOWN => "vfslide1down.vf"
  | VF_VDIV => "vfdiv.vf"
  | VF_VRDIV => "vfrdiv.vf"
  | VF_VMUL => "vfmul.vf"
  | VF_VRSUB => "vfrsub.vf"

def fvvmatype_mnemonic_forwards (arg_ : fvvmafunct6) : String :=
  match arg_ with
  | FVV_VMADD => "vfmadd.vv"
  | FVV_VNMADD => "vfnmadd.vv"
  | FVV_VMSUB => "vfmsub.vv"
  | FVV_VNMSUB => "vfnmsub.vv"
  | FVV_VMACC => "vfmacc.vv"
  | FVV_VNMACC => "vfnmacc.vv"
  | FVV_VMSAC => "vfmsac.vv"
  | FVV_VNMSAC => "vfnmsac.vv"

def fvvmtype_mnemonic_forwards (arg_ : fvvmfunct6) : String :=
  match arg_ with
  | FVVM_VMFEQ => "vmfeq.vv"
  | FVVM_VMFLE => "vmfle.vv"
  | FVVM_VMFLT => "vmflt.vv"
  | FVVM_VMFNE => "vmfne.vv"

def fvvtype_mnemonic_forwards (arg_ : fvvfunct6) : String :=
  match arg_ with
  | FVV_VADD => "vfadd.vv"
  | FVV_VSUB => "vfsub.vv"
  | FVV_VMIN => "vfmin.vv"
  | FVV_VMAX => "vfmax.vv"
  | FVV_VSGNJ => "vfsgnj.vv"
  | FVV_VSGNJN => "vfsgnjn.vv"
  | FVV_VSGNJX => "vfsgnjx.vv"
  | FVV_VDIV => "vfdiv.vv"
  | FVV_VMUL => "vfmul.vv"

def fwftype_mnemonic_forwards (arg_ : fwffunct6) : String :=
  match arg_ with
  | FWF_VADD => "vfwadd.wf"
  | FWF_VSUB => "vfwsub.wf"

def fwvfmatype_mnemonic_forwards (arg_ : fwvfmafunct6) : String :=
  match arg_ with
  | FWVF_VMACC => "vfwmacc.vf"
  | FWVF_VNMACC => "vfwnmacc.vf"
  | FWVF_VMSAC => "vfwmsac.vf"
  | FWVF_VNMSAC => "vfwnmsac.vf"

def fwvftype_mnemonic_forwards (arg_ : fwvffunct6) : String :=
  match arg_ with
  | FWVF_VADD => "vfwadd.vf"
  | FWVF_VSUB => "vfwsub.vf"
  | FWVF_VMUL => "vfwmul.vf"

def fwvtype_mnemonic_forwards (arg_ : fwvfunct6) : String :=
  match arg_ with
  | FWV_VADD => "vfwadd.wv"
  | FWV_VSUB => "vfwsub.wv"

def fwvvmatype_mnemonic_forwards (arg_ : fwvvmafunct6) : String :=
  match arg_ with
  | FWVV_VMACC => "vfwmacc.vv"
  | FWVV_VNMACC => "vfwnmacc.vv"
  | FWVV_VMSAC => "vfwmsac.vv"
  | FWVV_VNMSAC => "vfwnmsac.vv"

def fwvvtype_mnemonic_forwards (arg_ : fwvvfunct6) : String :=
  match arg_ with
  | FWVV_VADD => "vfwadd.vv"
  | FWVV_VSUB => "vfwsub.vv"
  | FWVV_VMUL => "vfwmul.vv"

def itype_mnemonic_forwards (arg_ : iop) : String :=
  match arg_ with
  | ADDI => "addi"
  | SLTI => "slti"
  | SLTIU => "sltiu"
  | XORI => "xori"
  | ORI => "ori"
  | ANDI => "andi"

def ma_flag_backwards (arg_ : (BitVec 1)) : String :=
  match_bv arg_ with
  | 1 => (String.append (sep_forwards ()) (String.append "ma" ""))
  | _ => (String.append (sep_forwards ()) (String.append "mu" ""))

/-- Type quantifiers: k_ex279104# : Bool -/
def maybe_aq_forwards (arg_ : Bool) : String :=
  match arg_ with
  | true => ".aq"
  | false => ""

def maybe_lmul_flag_backwards (arg_ : (BitVec 3)) : SailM String := do
  match_bv arg_ with
  | 101 => do (pure (String.append (sep_forwards ()) (String.append "mf8" "")))
  | 110 => do (pure (String.append (sep_forwards ()) (String.append "mf4" "")))
  | 111 => do (pure (String.append (sep_forwards ()) (String.append "mf2" "")))
  | 000 => do (pure (String.append (sep_forwards ()) (String.append "m1" "")))
  | 001 => do (pure (String.append (sep_forwards ()) (String.append "m2" "")))
  | 010 => do (pure (String.append (sep_forwards ()) (String.append "m4" "")))
  | 011 => do (pure (String.append (sep_forwards ()) (String.append "m8" "")))
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: k_ex279105# : Bool -/
def maybe_not_u_forwards (arg_ : Bool) : String :=
  match arg_ with
  | false => "u"
  | true => ""

/-- Type quantifiers: k_ex279106# : Bool -/
def maybe_rl_forwards (arg_ : Bool) : String :=
  match arg_ with
  | true => ".rl"
  | false => ""

/-- Type quantifiers: k_ex279107# : Bool -/
def maybe_u_forwards (arg_ : Bool) : String :=
  match arg_ with
  | true => "u"
  | false => ""

def maybe_vmask_backwards (arg_ : (BitVec 1)) : String :=
  match_bv arg_ with
  | 1 => ""
  | _ => (String.append (sep_forwards ()) (String.append "v0.t" ""))

def mmtype_mnemonic_forwards (arg_ : mmfunct6) : String :=
  match arg_ with
  | MM_VMAND => "vmand.mm"
  | MM_VMNAND => "vmnand.mm"
  | MM_VMANDN => "vmandn.mm"
  | MM_VMXOR => "vmxor.mm"
  | MM_VMOR => "vmor.mm"
  | MM_VMNOR => "vmnor.mm"
  | MM_VMORN => "vmorn.mm"
  | MM_VMXNOR => "vmxnor.mm"

def mul_mnemonic_forwards (arg_ : mul_op) : SailM String := do
  match arg_ with
  | { high := false, signed_rs1 := true, signed_rs2 := true } => (pure "mul")
  | { high := true, signed_rs1 := true, signed_rs2 := true } => (pure "mulh")
  | { high := true, signed_rs1 := true, signed_rs2 := false } => (pure "mulhsu")
  | { high := true, signed_rs1 := false, signed_rs2 := false } => (pure "mulhu")
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def mvvmatype_mnemonic_forwards (arg_ : mvvmafunct6) : String :=
  match arg_ with
  | MVV_VMACC => "vmacc.vv"
  | MVV_VNMSAC => "vnmsac.vv"
  | MVV_VMADD => "vmadd.vv"
  | MVV_VNMSUB => "vnmsub.vv"

def mvvtype_mnemonic_forwards (arg_ : mvvfunct6) : String :=
  match arg_ with
  | MVV_VAADDU => "vaaddu.vv"
  | MVV_VAADD => "vaadd.vv"
  | MVV_VASUBU => "vasubu.vv"
  | MVV_VASUB => "vasub.vv"
  | MVV_VMUL => "vmul.vv"
  | MVV_VMULH => "vmulh.vv"
  | MVV_VMULHU => "vmulhu.vv"
  | MVV_VMULHSU => "vmulhsu.vv"
  | MVV_VDIVU => "vdivu.vv"
  | MVV_VDIV => "vdiv.vv"
  | MVV_VREMU => "vremu.vv"
  | MVV_VREM => "vrem.vv"

def mvxmatype_mnemonic_forwards (arg_ : mvxmafunct6) : String :=
  match arg_ with
  | MVX_VMACC => "vmacc.vx"
  | MVX_VNMSAC => "vnmsac.vx"
  | MVX_VMADD => "vmadd.vx"
  | MVX_VNMSUB => "vnmsub.vx"

def mvxtype_mnemonic_forwards (arg_ : mvxfunct6) : String :=
  match arg_ with
  | MVX_VAADDU => "vaaddu.vx"
  | MVX_VAADD => "vaadd.vx"
  | MVX_VASUBU => "vasubu.vx"
  | MVX_VASUB => "vasub.vx"
  | MVX_VSLIDE1UP => "vslide1up.vx"
  | MVX_VSLIDE1DOWN => "vslide1down.vx"
  | MVX_VMUL => "vmul.vx"
  | MVX_VMULH => "vmulh.vx"
  | MVX_VMULHU => "vmulhu.vx"
  | MVX_VMULHSU => "vmulhsu.vx"
  | MVX_VDIVU => "vdivu.vx"
  | MVX_VDIV => "vdiv.vx"
  | MVX_VREMU => "vremu.vx"
  | MVX_VREM => "vrem.vx"

def nfields_string_forwards (arg_ : (BitVec 3)) : String :=
  match_bv arg_ with
  | 000 => ""
  | 001 => "seg2"
  | 010 => "seg3"
  | 011 => "seg4"
  | 100 => "seg5"
  | 101 => "seg6"
  | 110 => "seg7"
  | _ => "seg8"

def nistype_mnemonic_forwards (arg_ : nisfunct6) : String :=
  match arg_ with
  | NIS_VNSRL => "vnsrl.wi"
  | NIS_VNSRA => "vnsra.wi"

def nitype_mnemonic_forwards (arg_ : nifunct6) : String :=
  match arg_ with
  | NI_VNCLIPU => "vnclipu.wi"
  | NI_VNCLIP => "vnclip.wi"

def nvstype_mnemonic_forwards (arg_ : nvsfunct6) : String :=
  match arg_ with
  | NVS_VNSRL => "vnsrl.wv"
  | NVS_VNSRA => "vnsra.wv"

def nvtype_mnemonic_forwards (arg_ : nvfunct6) : String :=
  match arg_ with
  | NV_VNCLIPU => "vnclipu.wv"
  | NV_VNCLIP => "vnclip.wv"

def nxstype_mnemonic_forwards (arg_ : nxsfunct6) : String :=
  match arg_ with
  | NXS_VNSRL => "vnsrl.wx"
  | NXS_VNSRA => "vnsra.wx"

def nxtype_mnemonic_forwards (arg_ : nxfunct6) : String :=
  match arg_ with
  | NX_VNCLIPU => "vnclipu.wx"
  | NX_VNCLIP => "vnclip.wx"

def rfvvtype_mnemonic_forwards (arg_ : rfvvfunct6) : String :=
  match arg_ with
  | FVV_VFREDOSUM => "vfredosum.vs"
  | FVV_VFREDUSUM => "vfredusum.vs"
  | FVV_VFREDMAX => "vfredmax.vs"
  | FVV_VFREDMIN => "vfredmin.vs"
  | FVV_VFWREDOSUM => "vfwredosum.vs"
  | FVV_VFWREDUSUM => "vfwredusum.vs"

def rivvtype_mnemonic_forwards (arg_ : rivvfunct6) : String :=
  match arg_ with
  | IVV_VWREDSUMU => "vwredsumu.vs"
  | IVV_VWREDSUM => "vwredsum.vs"

def rmvvtype_mnemonic_forwards (arg_ : rmvvfunct6) : String :=
  match arg_ with
  | MVV_VREDSUM => "vredsum.vs"
  | MVV_VREDAND => "vredand.vs"
  | MVV_VREDOR => "vredor.vs"
  | MVV_VREDXOR => "vredxor.vs"
  | MVV_VREDMINU => "vredminu.vs"
  | MVV_VREDMIN => "vredmin.vs"
  | MVV_VREDMAXU => "vredmaxu.vs"
  | MVV_VREDMAX => "vredmax.vs"

def rtype_mnemonic_forwards (arg_ : rop) : String :=
  match arg_ with
  | ADD => "add"
  | SLT => "slt"
  | SLTU => "sltu"
  | AND => "and"
  | OR => "or"
  | XOR => "xor"
  | SLL => "sll"
  | SRL => "srl"
  | SUB => "sub"
  | SRA => "sra"

def rtypew_mnemonic_forwards (arg_ : ropw) : String :=
  match arg_ with
  | ADDW => "addw"
  | SUBW => "subw"
  | SLLW => "sllw"
  | SRLW => "srlw"
  | SRAW => "sraw"

def sew_flag_backwards (arg_ : (BitVec 3)) : SailM String := do
  match_bv arg_ with
  | 000 => do (pure "e8")
  | 001 => do (pure "e16")
  | 010 => do (pure "e32")
  | 011 => do (pure "e64")
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def shiftiop_mnemonic_forwards (arg_ : sop) : String :=
  match arg_ with
  | SLLI => "slli"
  | SRLI => "srli"
  | SRAI => "srai"

def shiftiwop_mnemonic_forwards (arg_ : sopw) : String :=
  match arg_ with
  | SLLIW => "slliw"
  | SRLIW => "srliw"
  | SRAIW => "sraiw"

def simm_string_forwards (arg_ : (BitVec 5)) : SailM String := do
  match_bv arg_ with
  | 00000 => do (pure "1")
  | 00001 => do (pure "2")
  | 00011 => do (pure "4")
  | 00111 => do (pure "8")
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def size_mnemonic_forwards (arg_ : word_width) : String :=
  match arg_ with
  | BYTE => "b"
  | HALF => "h"
  | WORD => "w"
  | DOUBLE => "d"

def ta_flag_backwards (arg_ : (BitVec 1)) : String :=
  match_bv arg_ with
  | 1 => (String.append (sep_forwards ()) (String.append "ta" ""))
  | _ => (String.append (sep_forwards ()) (String.append "tu" ""))

def utype_mnemonic_forwards (arg_ : uop) : String :=
  match arg_ with
  | LUI => "lui"
  | AUIPC => "auipc"

def vext2type_mnemonic_forwards (arg_ : vext2funct6) : String :=
  match arg_ with
  | VEXT2_ZVF2 => "vzext.vf2"
  | VEXT2_SVF2 => "vsext.vf2"

def vext4type_mnemonic_forwards (arg_ : vext4funct6) : String :=
  match arg_ with
  | VEXT4_ZVF4 => "vzext.vf4"
  | VEXT4_SVF4 => "vsext.vf4"

def vext8type_mnemonic_forwards (arg_ : vext8funct6) : String :=
  match arg_ with
  | VEXT8_ZVF8 => "vzext.vf8"
  | VEXT8_SVF8 => "vsext.vf8"

def vfnunary0_mnemonic_forwards (arg_ : vfnunary0) : String :=
  match arg_ with
  | FNV_CVT_XU_F => "vfncvt.xu.f.w"
  | FNV_CVT_X_F => "vfncvt.x.f.w"
  | FNV_CVT_F_XU => "vfncvt.f.xu.w"
  | FNV_CVT_F_X => "vfncvt.f.x.w"
  | FNV_CVT_F_F => "vfncvt.f.f.w"
  | FNV_CVT_ROD_F_F => "vfncvt.rod.f.f.w"
  | FNV_CVT_RTZ_XU_F => "vfncvt.rtz.xu.f.w"
  | FNV_CVT_RTZ_X_F => "vfncvt.rtz.x.f.w"

def vfunary0_mnemonic_forwards (arg_ : vfunary0) : String :=
  match arg_ with
  | FV_CVT_XU_F => "vfcvt.xu.f.v"
  | FV_CVT_X_F => "vfcvt.x.f.v"
  | FV_CVT_F_XU => "vfcvt.f.xu.v"
  | FV_CVT_F_X => "vfcvt.f.x.v"
  | FV_CVT_RTZ_XU_F => "vfcvt.rtz.xu.f.v"
  | FV_CVT_RTZ_X_F => "vfcvt.rtz.x.f.v"

def vfunary1_mnemonic_forwards (arg_ : vfunary1) : String :=
  match arg_ with
  | FVV_VSQRT => "vfsqrt.v"
  | FVV_VRSQRT7 => "vfrsqrt7.v"
  | FVV_VREC7 => "vfrec7.v"
  | FVV_VCLASS => "vfclass.v"

def vfwunary0_mnemonic_forwards (arg_ : vfwunary0) : String :=
  match arg_ with
  | FWV_CVT_XU_F => "vfwcvt.xu.f.v"
  | FWV_CVT_X_F => "vfwcvt.x.f.v"
  | FWV_CVT_F_XU => "vfwcvt.f.xu.v"
  | FWV_CVT_F_X => "vfwcvt.f.x.v"
  | FWV_CVT_F_F => "vfwcvt.f.f.v"
  | FWV_CVT_RTZ_XU_F => "vfwcvt.rtz.xu.f.v"
  | FWV_CVT_RTZ_X_F => "vfwcvt.rtz.x.f.v"

def vicmptype_mnemonic_forwards (arg_ : vicmpfunct6) : String :=
  match arg_ with
  | VICMP_VMSEQ => "vmseq.vi"
  | VICMP_VMSNE => "vmsne.vi"
  | VICMP_VMSLEU => "vmsleu.vi"
  | VICMP_VMSLE => "vmsle.vi"
  | VICMP_VMSGTU => "vmsgtu.vi"
  | VICMP_VMSGT => "vmsgt.vi"

def vimctype_mnemonic_forwards (arg_ : vimcfunct6) : String :=
  match arg_ with
  | VIMC_VMADC => "vmadc.vi"

def vimstype_mnemonic_forwards (arg_ : vimsfunct6) : String :=
  match arg_ with
  | VIMS_VADC => "vadc.vim"

def vimtype_mnemonic_forwards (arg_ : vimfunct6) : String :=
  match arg_ with
  | VIM_VMADC => "vmadc.vim"

def visg_mnemonic_forwards (arg_ : visgfunct6) : String :=
  match arg_ with
  | VI_VSLIDEUP => "vslideup.vi"
  | VI_VSLIDEDOWN => "vslidedown.vi"
  | VI_VRGATHER => "vrgather.vi"

def vitype_mnemonic_forwards (arg_ : vifunct6) : String :=
  match arg_ with
  | VI_VADD => "vadd.vi"
  | VI_VRSUB => "vrsub.vi"
  | VI_VAND => "vand.vi"
  | VI_VOR => "vor.vi"
  | VI_VXOR => "vxor.vi"
  | VI_VSADDU => "vsaddu.vi"
  | VI_VSADD => "vsadd.vi"
  | VI_VSLL => "vsll.vi"
  | VI_VSRL => "vsrl.vi"
  | VI_VSRA => "vsra.vi"
  | VI_VSSRL => "vssrl.vi"
  | VI_VSSRA => "vssra.vi"

def vlewidth_bitsnumberstr_forwards (arg_ : vlewidth) : String :=
  match arg_ with
  | VLE8 => "8"
  | VLE16 => "16"
  | VLE32 => "32"
  | VLE64 => "64"

def vmtype_mnemonic_forwards (arg_ : vmlsop) : String :=
  match arg_ with
  | VLM => "vlm.v"
  | VSM => "vsm.v"

def vreg_name_raw_forwards (arg_ : (BitVec 5)) : String :=
  match_bv arg_ with
  | 00000 => "v0"
  | 00001 => "v1"
  | 00010 => "v2"
  | 00011 => "v3"
  | 00100 => "v4"
  | 00101 => "v5"
  | 00110 => "v6"
  | 00111 => "v7"
  | 01000 => "v8"
  | 01001 => "v9"
  | 01010 => "v10"
  | 01011 => "v11"
  | 01100 => "v12"
  | 01101 => "v13"
  | 01110 => "v14"
  | 01111 => "v15"
  | 10000 => "v16"
  | 10001 => "v17"
  | 10010 => "v18"
  | 10011 => "v19"
  | 10100 => "v20"
  | 10101 => "v21"
  | 10110 => "v22"
  | 10111 => "v23"
  | 11000 => "v24"
  | 11001 => "v25"
  | 11010 => "v26"
  | 11011 => "v27"
  | 11100 => "v28"
  | 11101 => "v29"
  | 11110 => "v30"
  | _ => "v31"

def vreg_name_forwards (arg_ : vregidx) : String :=
  match arg_ with
  | .Vregidx i => (vreg_name_raw_forwards i)

def vsha2c_mnemonic_forwards (arg_ : zvkfunct6) : String :=
  match arg_ with
  | ZVK_VSHA2CH => "vsha2ch.vv"
  | ZVK_VSHA2CL => "vsha2cl.vv"

def vvcmptype_mnemonic_forwards (arg_ : vvcmpfunct6) : String :=
  match arg_ with
  | VVCMP_VMSEQ => "vmseq.vv"
  | VVCMP_VMSNE => "vmsne.vv"
  | VVCMP_VMSLTU => "vmsltu.vv"
  | VVCMP_VMSLT => "vmslt.vv"
  | VVCMP_VMSLEU => "vmsleu.vv"
  | VVCMP_VMSLE => "vmsle.vv"

def vvmctype_mnemonic_forwards (arg_ : vvmcfunct6) : String :=
  match arg_ with
  | VVMC_VMADC => "vmadc.vv"
  | VVMC_VMSBC => "vmsbc.vv"

def vvmstype_mnemonic_forwards (arg_ : vvmsfunct6) : String :=
  match arg_ with
  | VVMS_VADC => "vadc.vvm"
  | VVMS_VSBC => "vsbc.vvm"

def vvmtype_mnemonic_forwards (arg_ : vvmfunct6) : String :=
  match arg_ with
  | VVM_VMADC => "vmadc.vvm"
  | VVM_VMSBC => "vmsbc.vvm"

def vvtype_mnemonic_forwards (arg_ : vvfunct6) : String :=
  match arg_ with
  | VV_VADD => "vadd.vv"
  | VV_VSUB => "vsub.vv"
  | VV_VAND => "vand.vv"
  | VV_VOR => "vor.vv"
  | VV_VXOR => "vxor.vv"
  | VV_VRGATHER => "vrgather.vv"
  | VV_VRGATHEREI16 => "vrgatherei16.vv"
  | VV_VSADDU => "vsaddu.vv"
  | VV_VSADD => "vsadd.vv"
  | VV_VSSUBU => "vssubu.vv"
  | VV_VSSUB => "vssub.vv"
  | VV_VSLL => "vsll.vv"
  | VV_VSMUL => "vsmul.vv"
  | VV_VSRL => "vsrl.vv"
  | VV_VSRA => "vsra.vv"
  | VV_VSSRL => "vssrl.vv"
  | VV_VSSRA => "vssra.vv"
  | VV_VMINU => "vminu.vv"
  | VV_VMIN => "vmin.vv"
  | VV_VMAXU => "vmaxu.vv"
  | VV_VMAX => "vmax.vv"

def vxcmptype_mnemonic_forwards (arg_ : vxcmpfunct6) : String :=
  match arg_ with
  | VXCMP_VMSEQ => "vmseq.vx"
  | VXCMP_VMSNE => "vmsne.vx"
  | VXCMP_VMSLTU => "vmsltu.vx"
  | VXCMP_VMSLT => "vmslt.vx"
  | VXCMP_VMSLEU => "vmsleu.vx"
  | VXCMP_VMSLE => "vmsle.vx"
  | VXCMP_VMSGTU => "vmsgtu.vx"
  | VXCMP_VMSGT => "vmsgt.vx"

def vxmctype_mnemonic_forwards (arg_ : vxmcfunct6) : String :=
  match arg_ with
  | VXMC_VMADC => "vmadc.vx"
  | VXMC_VMSBC => "vmsbc.vx"

def vxmstype_mnemonic_forwards (arg_ : vxmsfunct6) : String :=
  match arg_ with
  | VXMS_VADC => "vadc.vxm"
  | VXMS_VSBC => "vsbc.vxm"

def vxmtype_mnemonic_forwards (arg_ : vxmfunct6) : String :=
  match arg_ with
  | VXM_VMADC => "vmadc.vxm"
  | VXM_VMSBC => "vmsbc.vxm"

def vxsg_mnemonic_forwards (arg_ : vxsgfunct6) : String :=
  match arg_ with
  | VX_VSLIDEUP => "vslideup.vx"
  | VX_VSLIDEDOWN => "vslidedown.vx"
  | VX_VRGATHER => "vrgather.vx"

def vxtype_mnemonic_forwards (arg_ : vxfunct6) : String :=
  match arg_ with
  | VX_VADD => "vadd.vx"
  | VX_VSUB => "vsub.vx"
  | VX_VRSUB => "vrsub.vx"
  | VX_VAND => "vand.vx"
  | VX_VOR => "vor.vx"
  | VX_VXOR => "vxor.vx"
  | VX_VSADDU => "vsaddu.vx"
  | VX_VSADD => "vsadd.vx"
  | VX_VSSUBU => "vssubu.vx"
  | VX_VSSUB => "vssub.vx"
  | VX_VSLL => "vsll.vx"
  | VX_VSMUL => "vsmul.vx"
  | VX_VSRL => "vsrl.vx"
  | VX_VSRA => "vsra.vx"
  | VX_VSSRL => "vssrl.vx"
  | VX_VSSRA => "vssra.vx"
  | VX_VMINU => "vminu.vx"
  | VX_VMIN => "vmin.vx"
  | VX_VMAXU => "vmaxu.vx"
  | VX_VMAX => "vmax.vx"

def wmvvtype_mnemonic_forwards (arg_ : wmvvfunct6) : String :=
  match arg_ with
  | WMVV_VWMACCU => "vwmaccu.vv"
  | WMVV_VWMACC => "vwmacc.vv"
  | WMVV_VWMACCSU => "vwmaccsu.vv"

def wmvxtype_mnemonic_forwards (arg_ : wmvxfunct6) : String :=
  match arg_ with
  | WMVX_VWMACCU => "vwmaccu.vx"
  | WMVX_VWMACC => "vwmacc.vx"
  | WMVX_VWMACCUS => "vwmaccus.vx"
  | WMVX_VWMACCSU => "vwmaccsu.vx"

def wvtype_mnemonic_forwards (arg_ : wvfunct6) : String :=
  match arg_ with
  | WV_VADD => "vwadd.wv"
  | WV_VSUB => "vwsub.wv"
  | WV_VADDU => "vwaddu.wv"
  | WV_VSUBU => "vwsubu.wv"

def wvvtype_mnemonic_forwards (arg_ : wvvfunct6) : String :=
  match arg_ with
  | WVV_VADD => "vwadd.vv"
  | WVV_VSUB => "vwsub.vv"
  | WVV_VADDU => "vwaddu.vv"
  | WVV_VSUBU => "vwsubu.vv"
  | WVV_VWMUL => "vwmul.vv"
  | WVV_VWMULU => "vwmulu.vv"
  | WVV_VWMULSU => "vwmulsu.vv"

def wvxtype_mnemonic_forwards (arg_ : wvxfunct6) : String :=
  match arg_ with
  | WVX_VADD => "vwadd.vx"
  | WVX_VSUB => "vwsub.vx"
  | WVX_VADDU => "vwaddu.vx"
  | WVX_VSUBU => "vwsubu.vx"
  | WVX_VWMUL => "vwmul.vx"
  | WVX_VWMULU => "vwmulu.vx"
  | WVX_VWMULSU => "vwmulsu.vx"

def wxtype_mnemonic_forwards (arg_ : wxfunct6) : String :=
  match arg_ with
  | WX_VADD => "vwadd.wx"
  | WX_VSUB => "vwsub.wx"
  | WX_VADDU => "vwaddu.wx"
  | WX_VSUBU => "vwsubu.wx"

def zba_rtype_mnemonic_forwards (arg_ : brop_zba) : String :=
  match arg_ with
  | SH1ADD => "sh1add"
  | SH2ADD => "sh2add"
  | SH3ADD => "sh3add"

def zba_rtypeuw_mnemonic_forwards (arg_ : bropw_zba) : String :=
  match arg_ with
  | ADDUW => "add.uw"
  | SH1ADDUW => "sh1add.uw"
  | SH2ADDUW => "sh2add.uw"
  | SH3ADDUW => "sh3add.uw"

def zbb_extop_mnemonic_forwards (arg_ : extop_zbb) : String :=
  match arg_ with
  | SEXTB => "sext.b"
  | SEXTH => "sext.h"
  | ZEXTH => "zext.h"

def zbb_rtype_mnemonic_forwards (arg_ : brop_zbb) : String :=
  match arg_ with
  | ANDN => "andn"
  | ORN => "orn"
  | XNOR => "xnor"
  | MAX => "max"
  | MAXU => "maxu"
  | MIN => "min"
  | MINU => "minu"
  | ROL => "rol"
  | ROR => "ror"

def zbb_rtypew_mnemonic_forwards (arg_ : bropw_zbb) : String :=
  match arg_ with
  | ROLW => "rolw"
  | RORW => "rorw"

def zbkb_rtype_mnemonic_forwards (arg_ : brop_zbkb) : String :=
  match arg_ with
  | PACK => "pack"
  | PACKH => "packh"

def zbs_iop_mnemonic_forwards (arg_ : biop_zbs) : String :=
  match arg_ with
  | BCLRI => "bclri"
  | BEXTI => "bexti"
  | BINVI => "binvi"
  | BSETI => "bseti"

def zbs_rtype_mnemonic_forwards (arg_ : brop_zbs) : String :=
  match arg_ with
  | BCLR => "bclr"
  | BEXT => "bext"
  | BINV => "binv"
  | BSET => "bset"

def zicond_mnemonic_forwards (arg_ : zicondop) : String :=
  match arg_ with
  | CZERO_EQZ => "czero.eqz"
  | CZERO_NEZ => "czero.nez"

def assembly_forwards (arg_ : ast) : SailM String := do
  match arg_ with
  | .UTYPE (imm, rd, op) =>
    (pure (String.append (utype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_20_forwards imm)) ""))))))
  | .JAL (imm, rd) =>
    (pure (String.append "jal"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_21_forwards imm)) ""))))))
  | .JALR (imm, rs1, rd) =>
    (pure (String.append "jalr"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_12_forwards imm))
                (String.append "(" (String.append (reg_name_forwards rs1) (String.append ")" "")))))))))
  | .BTYPE (imm, rs2, rs1, op) =>
    (pure (String.append (btype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rs1)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_13_forwards imm)) ""))))))))
  | .ITYPE (imm, rs1, rd, op) =>
    (pure (String.append (itype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_12_forwards imm)) ""))))))))
  | .SHIFTIOP (shamt, rs1, rd, op) =>
    (pure (String.append (shiftiop_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_6_forwards shamt)) ""))))))))
  | .RTYPE (rs2, rs1, rd, op) =>
    (pure (String.append (rtype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .LOAD (imm, rs1, rd, is_unsigned, width, aq, rl) =>
    (pure (String.append "l"
        (String.append (size_mnemonic_forwards width)
          (String.append (maybe_u_forwards is_unsigned)
            (String.append (maybe_aq_forwards aq)
              (String.append (maybe_rl_forwards rl)
                (String.append (spc_forwards ())
                  (String.append (reg_name_forwards rd)
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_signed_12_forwards imm))
                        (String.append "("
                          (String.append (reg_name_forwards rs1) (String.append ")" "")))))))))))))
  | .STORE (imm, rs2, rs1, width, aq, rl) =>
    (pure (String.append "s"
        (String.append (size_mnemonic_forwards width)
          (String.append (maybe_aq_forwards aq)
            (String.append (maybe_rl_forwards rl)
              (String.append (spc_forwards ())
                (String.append (reg_name_forwards rs2)
                  (String.append (sep_forwards ())
                    (String.append (← (hex_bits_signed_12_forwards imm))
                      (String.append (opt_spc_forwards ())
                        (String.append "("
                          (String.append (opt_spc_forwards ())
                            (String.append (reg_name_forwards rs1)
                              (String.append (opt_spc_forwards ()) (String.append ")" "")))))))))))))))
  | .ADDIW (imm, rs1, rd) =>
    (do
      bif (xlen == 64)
      then
        (pure (String.append "addiw"
            (String.append (spc_forwards ())
              (String.append (reg_name_forwards rd)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_signed_12_forwards imm)) ""))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPEW (rs2, rs1, rd, op) =>
    (do
      bif (xlen == 64)
      then
        (pure (String.append (rtypew_mnemonic_forwards op)
            (String.append (spc_forwards ())
              (String.append (reg_name_forwards rd)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHIFTIWOP (shamt, rs1, rd, op) =>
    (do
      bif (xlen == 64)
      then
        (pure (String.append (shiftiwop_mnemonic_forwards op)
            (String.append (spc_forwards ())
              (String.append (reg_name_forwards rd)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_5_forwards shamt)) ""))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FENCE (pred, succ) =>
    (pure (String.append "fence"
        (String.append (spc_forwards ())
          (String.append (fence_bits_forwards pred)
            (String.append (sep_forwards ()) (String.append (fence_bits_forwards succ) ""))))))
  | .FENCE_TSO (pred, succ) =>
    (pure (String.append "fence.tso"
        (String.append (spc_forwards ())
          (String.append (fence_bits_forwards pred)
            (String.append (sep_forwards ()) (String.append (fence_bits_forwards succ) ""))))))
  | .ECALL () => (pure "ecall")
  | .MRET () => (pure "mret")
  | .SRET () => (pure "sret")
  | .EBREAK () => (pure "ebreak")
  | .WFI () => (pure "wfi")
  | .SFENCE_VMA (rs1, rs2) =>
    (pure (String.append "sfence.vma"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rs1)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))
  | .FENCEI () => (pure "fence.i")
  | .LOADRES (aq, rl, rs1, size, rd) =>
    (pure (String.append "lr."
        (String.append (size_mnemonic_forwards size)
          (String.append (maybe_aq_forwards aq)
            (String.append (maybe_rl_forwards rl)
              (String.append (spc_forwards ())
                (String.append (reg_name_forwards rd)
                  (String.append (sep_forwards ())
                    (String.append "("
                      (String.append (reg_name_forwards rs1) (String.append ")" "")))))))))))
  | .STORECON (aq, rl, rs2, rs1, size, rd) =>
    (pure (String.append "sc."
        (String.append (size_mnemonic_forwards size)
          (String.append (maybe_aq_forwards aq)
            (String.append (maybe_rl_forwards rl)
              (String.append (spc_forwards ())
                (String.append (reg_name_forwards rd)
                  (String.append (sep_forwards ())
                    (String.append (reg_name_forwards rs2)
                      (String.append (sep_forwards ())
                        (String.append "("
                          (String.append (reg_name_forwards rs1) (String.append ")" "")))))))))))))
  | .AMO (op, aq, rl, rs2, rs1, width, rd) =>
    (pure (String.append (amo_mnemonic_forwards op)
        (String.append "."
          (String.append (size_mnemonic_forwards width)
            (String.append (maybe_aq_forwards aq)
              (String.append (maybe_rl_forwards rl)
                (String.append (spc_forwards ())
                  (String.append (reg_name_forwards rd)
                    (String.append (sep_forwards ())
                      (String.append (reg_name_forwards rs2)
                        (String.append (sep_forwards ())
                          (String.append "("
                            (String.append (reg_name_forwards rs1) (String.append ")" ""))))))))))))))
  | .C_NOP () => (pure "c.nop")
  | .C_ADDI4SPN (rdc, nzimm) =>
    (do
      bif (nzimm != (0x00 : (BitVec 8)))
      then
        (pure (String.append "c.addi4spn"
            (String.append (spc_forwards ())
              (String.append (creg_name_forwards rdc)
                (String.append (sep_forwards ())
                  (String.append
                    (← (hex_bits_10_forwards ((nzimm : (BitVec 8)) ++ (0b00 : (BitVec 2))))) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LW (uimm, rsc, rdc) =>
    (pure (String.append "c.lw"
        (String.append (spc_forwards ())
          (String.append (creg_name_forwards rdc)
            (String.append (sep_forwards ())
              (String.append (creg_name_forwards rsc)
                (String.append (sep_forwards ())
                  (String.append
                    (← (hex_bits_7_forwards ((uimm : (BitVec 5)) ++ (0b00 : (BitVec 2))))) ""))))))))
  | .C_LD (uimm, rsc, rdc) =>
    (do
      bif (xlen == 64)
      then
        (pure (String.append "c.ld"
            (String.append (spc_forwards ())
              (String.append (creg_name_forwards rdc)
                (String.append (sep_forwards ())
                  (String.append (creg_name_forwards rsc)
                    (String.append (sep_forwards ())
                      (String.append
                        (← (hex_bits_8_forwards ((uimm : (BitVec 5)) ++ (0b000 : (BitVec 3))))) ""))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SW (uimm, rsc1, rsc2) =>
    (pure (String.append "c.sw"
        (String.append (spc_forwards ())
          (String.append (creg_name_forwards rsc1)
            (String.append (sep_forwards ())
              (String.append (creg_name_forwards rsc2)
                (String.append (sep_forwards ())
                  (String.append
                    (← (hex_bits_7_forwards ((uimm : (BitVec 5)) ++ (0b00 : (BitVec 2))))) ""))))))))
  | .C_SD (uimm, rsc1, rsc2) =>
    (do
      bif (xlen == 64)
      then
        (pure (String.append "c.sd"
            (String.append (spc_forwards ())
              (String.append (creg_name_forwards rsc1)
                (String.append (sep_forwards ())
                  (String.append (creg_name_forwards rsc2)
                    (String.append (sep_forwards ())
                      (String.append
                        (← (hex_bits_8_forwards ((uimm : (BitVec 5)) ++ (0b000 : (BitVec 3))))) ""))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDI (nzi, rsd) =>
    (do
      bif ((nzi != (0b000000 : (BitVec 6))) && (bne rsd zreg))
      then
        (pure (String.append "c.addi"
            (String.append (spc_forwards ())
              (String.append (reg_name_forwards rsd)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_6_forwards nzi)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_JAL imm =>
    (do
      bif (xlen == 32)
      then
        (pure (String.append "c.jal"
            (String.append (spc_forwards ())
              (String.append
                (← (hex_bits_signed_12_forwards ((imm : (BitVec 11)) ++ (0b0 : (BitVec 1))))) ""))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDIW (imm, rsd) =>
    (do
      bif (xlen == 64)
      then
        (pure (String.append "c.addiw"
            (String.append (spc_forwards ())
              (String.append (reg_name_forwards rsd)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_6_forwards imm)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LI (imm, rd) =>
    (do
      bif (bne rd zreg)
      then
        (pure (String.append "c.li"
            (String.append (spc_forwards ())
              (String.append (reg_name_forwards rd)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_6_forwards imm)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDI16SP imm =>
    (do
      bif (imm != (0b000000 : (BitVec 6)))
      then
        (pure (String.append "c.addi16sp"
            (String.append (spc_forwards ())
              (String.append (← (hex_bits_signed_6_forwards imm)) ""))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LUI (imm, rd) =>
    (do
      bif ((bne rd zreg) && ((bne rd sp) && (imm != (0b000000 : (BitVec 6)))))
      then
        (pure (String.append "c.lui"
            (String.append (spc_forwards ())
              (String.append (reg_name_forwards rd)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_6_forwards imm)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SRLI (shamt, rsd) =>
    (do
      bif (shamt != (0b000000 : (BitVec 6)))
      then
        (pure (String.append "c.srli"
            (String.append (spc_forwards ())
              (String.append (creg_name_forwards rsd)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_6_forwards shamt)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SRAI (shamt, rsd) =>
    (do
      bif (shamt != (0b000000 : (BitVec 6)))
      then
        (pure (String.append "c.srai"
            (String.append (spc_forwards ())
              (String.append (creg_name_forwards rsd)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_6_forwards shamt)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ANDI (imm, rsd) =>
    (pure (String.append "c.andi"
        (String.append (spc_forwards ())
          (String.append (creg_name_forwards rsd)
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_6_forwards imm)) ""))))))
  | .C_SUB (rsd, rs2) =>
    (pure (String.append "c.sub"
        (String.append (spc_forwards ())
          (String.append (creg_name_forwards rsd)
            (String.append (sep_forwards ()) (String.append (creg_name_forwards rs2) ""))))))
  | .C_XOR (rsd, rs2) =>
    (pure (String.append "c.xor"
        (String.append (spc_forwards ())
          (String.append (creg_name_forwards rsd)
            (String.append (sep_forwards ()) (String.append (creg_name_forwards rs2) ""))))))
  | .C_OR (rsd, rs2) =>
    (pure (String.append "c.or"
        (String.append (spc_forwards ())
          (String.append (creg_name_forwards rsd)
            (String.append (sep_forwards ()) (String.append (creg_name_forwards rs2) ""))))))
  | .C_AND (rsd, rs2) =>
    (pure (String.append "c.and"
        (String.append (spc_forwards ())
          (String.append (creg_name_forwards rsd)
            (String.append (sep_forwards ()) (String.append (creg_name_forwards rs2) ""))))))
  | .C_SUBW (rsd, rs2) =>
    (do
      bif (xlen == 64)
      then
        (pure (String.append "c.subw"
            (String.append (spc_forwards ())
              (String.append (creg_name_forwards rsd)
                (String.append (sep_forwards ()) (String.append (creg_name_forwards rs2) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDW (rsd, rs2) =>
    (do
      bif (xlen == 64)
      then
        (pure (String.append "c.addw"
            (String.append (spc_forwards ())
              (String.append (creg_name_forwards rsd)
                (String.append (sep_forwards ()) (String.append (creg_name_forwards rs2) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_J imm =>
    (pure (String.append "c.j"
        (String.append (spc_forwards ())
          (String.append
            (← (hex_bits_signed_12_forwards ((imm : (BitVec 11)) ++ (0b0 : (BitVec 1))))) ""))))
  | .C_BEQZ (imm, rs) =>
    (pure (String.append "c.beqz"
        (String.append (spc_forwards ())
          (String.append (creg_name_forwards rs)
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_8_forwards imm)) ""))))))
  | .C_BNEZ (imm, rs) =>
    (pure (String.append "c.bnez"
        (String.append (spc_forwards ())
          (String.append (creg_name_forwards rs)
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_8_forwards imm)) ""))))))
  | .C_SLLI (shamt, rsd) =>
    (do
      bif ((shamt != (0b000000 : (BitVec 6))) && (bne rsd zreg))
      then
        (pure (String.append "c.slli"
            (String.append (spc_forwards ())
              (String.append (reg_name_forwards rsd)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_6_forwards shamt)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LWSP (uimm, rd) =>
    (do
      bif (bne rd zreg)
      then
        (pure (String.append "c.lwsp"
            (String.append (spc_forwards ())
              (String.append (reg_name_forwards rd)
                (String.append (sep_forwards ()) (String.append (← (hex_bits_6_forwards uimm)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LDSP (uimm, rd) =>
    (do
      bif ((bne rd zreg) && (xlen == 64))
      then
        (pure (String.append "c.ldsp"
            (String.append (spc_forwards ())
              (String.append (reg_name_forwards rd)
                (String.append (sep_forwards ()) (String.append (← (hex_bits_6_forwards uimm)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SWSP (uimm, rs2) =>
    (pure (String.append "c.swsp"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rs2)
            (String.append (sep_forwards ()) (String.append (← (hex_bits_6_forwards uimm)) ""))))))
  | .C_SDSP (uimm, rs2) =>
    (do
      bif (xlen == 64)
      then
        (pure (String.append "c.sdsp"
            (String.append (spc_forwards ())
              (String.append (reg_name_forwards rs2)
                (String.append (sep_forwards ()) (String.append (← (hex_bits_6_forwards uimm)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_JR rs1 =>
    (do
      bif (bne rs1 zreg)
      then
        (pure (String.append "c.jr"
            (String.append (spc_forwards ()) (String.append (reg_name_forwards rs1) ""))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_JALR rs1 =>
    (do
      bif (bne rs1 zreg)
      then
        (pure (String.append "c.jalr"
            (String.append (spc_forwards ()) (String.append (reg_name_forwards rs1) ""))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_MV (rd, rs2) =>
    (do
      bif ((bne rd zreg) && (bne rs2 zreg))
      then
        (pure (String.append "c.mv"
            (String.append (spc_forwards ())
              (String.append (reg_name_forwards rd)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_EBREAK () => (pure "c.ebreak")
  | .C_ADD (rsd, rs2) =>
    (do
      bif ((bne rsd zreg) && (bne rs2 zreg))
      then
        (pure (String.append "c.add"
            (String.append (spc_forwards ())
              (String.append (reg_name_forwards rsd)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MUL (rs2, rs1, rd, mul_op) =>
    (pure (String.append (← (mul_mnemonic_forwards mul_op))
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .DIV (rs2, rs1, rd, s) =>
    (pure (String.append "div"
        (String.append (maybe_not_u_forwards s)
          (String.append (spc_forwards ())
            (String.append (reg_name_forwards rd)
              (String.append (sep_forwards ())
                (String.append (reg_name_forwards rs1)
                  (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) "")))))))))
  | .REM (rs2, rs1, rd, s) =>
    (pure (String.append "rem"
        (String.append (maybe_not_u_forwards s)
          (String.append (spc_forwards ())
            (String.append (reg_name_forwards rd)
              (String.append (sep_forwards ())
                (String.append (reg_name_forwards rs1)
                  (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) "")))))))))
  | .MULW (rs2, rs1, rd) =>
    (do
      bif (xlen == 64)
      then
        (pure (String.append "mulw"
            (String.append (spc_forwards ())
              (String.append (reg_name_forwards rd)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .DIVW (rs2, rs1, rd, s) =>
    (do
      bif (xlen == 64)
      then
        (pure (String.append "div"
            (String.append (maybe_not_u_forwards s)
              (String.append "w"
                (String.append (spc_forwards ())
                  (String.append (reg_name_forwards rd)
                    (String.append (sep_forwards ())
                      (String.append (reg_name_forwards rs1)
                        (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .REMW (rs2, rs1, rd, s) =>
    (do
      bif (xlen == 64)
      then
        (pure (String.append "rem"
            (String.append (maybe_not_u_forwards s)
              (String.append "w"
                (String.append (spc_forwards ())
                  (String.append (reg_name_forwards rd)
                    (String.append (sep_forwards ())
                      (String.append (reg_name_forwards rs1)
                        (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CSRImm (csr, imm, rd, op) =>
    (pure (String.append (csr_mnemonic_forwards op)
        (String.append "i"
          (String.append (spc_forwards ())
            (String.append (reg_name_forwards rd)
              (String.append (sep_forwards ())
                (String.append (← (csr_name_map_forwards csr))
                  (String.append (sep_forwards ())
                    (String.append (← (hex_bits_5_forwards imm)) "")))))))))
  | .CSRReg (csr, rs1, rd, op) =>
    (pure (String.append (csr_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (← (csr_name_map_forwards csr))
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))))
  | .C_NOP_HINT imm =>
    (pure (String.append "c.nop.hint." (String.append (← (hex_bits_6_forwards imm)) "")))
  | .C_ADDI_HINT rsd =>
    (do
      bif (bne rsd zreg)
      then (pure (String.append "c.addi.hint." (String.append (reg_name_forwards rsd) "")))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LI_HINT imm =>
    (pure (String.append "c.li.hint." (String.append (← (hex_bits_6_forwards imm)) "")))
  | .C_LUI_HINT imm =>
    (do
      bif (imm != (0b000000 : (BitVec 6)))
      then (pure (String.append "c.lui.hint." (String.append (← (hex_bits_6_forwards imm)) "")))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_MV_HINT rs2 =>
    (do
      bif (bne rs2 zreg)
      then (pure (String.append "c.mv.hint." (String.append (reg_name_forwards rs2) "")))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADD_HINT rs2 =>
    (do
      bif (bne rs2 zreg)
      then (pure (String.append "c.add.hint." (String.append (reg_name_forwards rs2) "")))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SLLI_HINT (shamt, rsd) =>
    (do
      bif ((shamt == (0b000000 : (BitVec 6))) || (rsd == zreg))
      then
        (pure (String.append "c.slli.hint."
            (String.append (reg_name_forwards rsd)
              (String.append "." (String.append (← (hex_bits_6_forwards shamt)) "")))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SRLI_HINT rsd =>
    (pure (String.append "c.srli.hint." (String.append (creg_name_forwards rsd) "")))
  | .C_SRAI_HINT rsd =>
    (pure (String.append "c.srai.hint." (String.append (creg_name_forwards rsd) "")))
  | .FENCE_RESERVED (fm, pred, succ, rs, rd) =>
    (do
      bif (((fm != (0x0 : (BitVec 4))) && (fm != (0x8 : (BitVec 4)))) || ((bne rs zreg) || (bne rd
               zreg)))
      then
        (pure (String.append "fence.reserved."
            (String.append (fence_bits_forwards pred)
              (String.append "."
                (String.append (fence_bits_forwards succ)
                  (String.append "."
                    (String.append (reg_name_forwards rs)
                      (String.append "."
                        (String.append (reg_name_forwards rd)
                          (String.append "." (String.append (← (hex_bits_4_forwards fm)) "")))))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FENCEI_RESERVED (imm, rs, rd) =>
    (do
      bif ((imm != (0x000 : (BitVec 12))) || ((bne rs zreg) || (bne rd zreg)))
      then
        (pure (String.append "fence.i.reserved."
            (String.append (reg_name_forwards rd)
              (String.append "."
                (String.append (reg_name_forwards rs)
                  (String.append "." (String.append (← (hex_bits_12_forwards imm)) "")))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .LOAD_FP (imm, rs1, rd, width) =>
    (pure (String.append "fl"
        (String.append (size_mnemonic_forwards width)
          (String.append (spc_forwards ())
            (String.append (freg_or_reg_name_forwards rd)
              (String.append (sep_forwards ())
                (String.append (← (hex_bits_signed_12_forwards imm))
                  (String.append (opt_spc_forwards ())
                    (String.append "("
                      (String.append (opt_spc_forwards ())
                        (String.append (reg_name_forwards rs1)
                          (String.append (opt_spc_forwards ()) (String.append ")" "")))))))))))))
  | .STORE_FP (imm, rs2, rs1, width) =>
    (pure (String.append "fs"
        (String.append (size_mnemonic_forwards width)
          (String.append (spc_forwards ())
            (String.append (freg_name_forwards rs2)
              (String.append (sep_forwards ())
                (String.append (← (hex_bits_signed_12_forwards imm))
                  (String.append (opt_spc_forwards ())
                    (String.append "("
                      (String.append (opt_spc_forwards ())
                        (String.append (reg_name_forwards rs1)
                          (String.append (opt_spc_forwards ()) (String.append ")" "")))))))))))))
  | .F_MADD_TYPE_S (rs3, rs2, rs1, rm, rd, op) =>
    (pure (String.append (f_madd_type_mnemonic_S_forwards op)
        (String.append (spc_forwards ())
          (String.append (freg_or_reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_or_reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (freg_or_reg_name_forwards rs2)
                    (String.append (sep_forwards ())
                      (String.append (freg_or_reg_name_forwards rs3)
                        (String.append (sep_forwards ())
                          (String.append (frm_mnemonic_forwards rm) ""))))))))))))
  | .F_BIN_RM_TYPE_S (rs2, rs1, rm, rd, op) =>
    (pure (String.append (f_bin_rm_type_mnemonic_S_forwards op)
        (String.append (spc_forwards ())
          (String.append (freg_or_reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_or_reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (freg_or_reg_name_forwards rs2)
                    (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))))
  | .F_UN_RM_FF_TYPE_S (rs1, rm, rd, FSQRT_S) =>
    (pure (String.append "fsqrt.s"
        (String.append (spc_forwards ())
          (String.append (freg_or_reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_or_reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .F_UN_RM_FX_TYPE_S (rs1, rm, rd, op) =>
    (pure (String.append (f_un_rm_fx_type_mnemonic_S_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_or_reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .F_UN_RM_XF_TYPE_S (rs1, rm, rd, op) =>
    (pure (String.append (f_un_rm_xf_type_mnemonic_S_forwards op)
        (String.append (spc_forwards ())
          (String.append (freg_or_reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .F_BIN_TYPE_F_S (rs2, rs1, rd, op) =>
    (pure (String.append (f_bin_type_mnemonic_f_S_forwards op)
        (String.append (spc_forwards ())
          (String.append (freg_or_reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_or_reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (freg_or_reg_name_forwards rs2) ""))))))))
  | .F_BIN_TYPE_X_S (rs2, rs1, rd, op) =>
    (pure (String.append (f_bin_type_mnemonic_x_S_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_or_reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (freg_or_reg_name_forwards rs2) ""))))))))
  | .F_UN_TYPE_X_S (rs1, rd, op) =>
    (pure (String.append (f_un_type_mnemonic_x_S_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (freg_name_forwards rs1) ""))))))
  | .F_UN_TYPE_F_S (rs1, rd, op) =>
    (pure (String.append (f_un_type_mnemonic_f_S_forwards op)
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .C_FLWSP (imm, rd) =>
    (do
      bif (xlen == 32)
      then
        (pure (String.append "c.flwsp"
            (String.append (spc_forwards ())
              (String.append (freg_name_forwards rd)
                (String.append (sep_forwards ()) (String.append (← (hex_bits_6_forwards imm)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_FSWSP (uimm, rs2) =>
    (do
      bif (xlen == 32)
      then
        (pure (String.append "c.fswsp"
            (String.append (spc_forwards ())
              (String.append (freg_name_forwards rs2)
                (String.append (sep_forwards ()) (String.append (← (hex_bits_6_forwards uimm)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_FLW (uimm, rsc, rdc) =>
    (do
      bif (xlen == 32)
      then
        (pure (String.append "c.flw"
            (String.append (spc_forwards ())
              (String.append (creg_name_forwards rdc)
                (String.append (sep_forwards ())
                  (String.append (creg_name_forwards rsc)
                    (String.append (sep_forwards ())
                      (String.append
                        (← (hex_bits_7_forwards ((uimm : (BitVec 5)) ++ (0b00 : (BitVec 2))))) ""))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_FSW (uimm, rsc1, rsc2) =>
    (do
      bif (xlen == 32)
      then
        (pure (String.append "c.fsw"
            (String.append (spc_forwards ())
              (String.append (creg_name_forwards rsc1)
                (String.append (sep_forwards ())
                  (String.append (creg_name_forwards rsc2)
                    (String.append (sep_forwards ())
                      (String.append
                        (← (hex_bits_7_forwards ((uimm : (BitVec 5)) ++ (0b00 : (BitVec 2))))) ""))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .F_MADD_TYPE_D (rs3, rs2, rs1, rm, rd, op) =>
    (pure (String.append (f_madd_type_mnemonic_D_forwards op)
        (String.append (spc_forwards ())
          (String.append (freg_or_reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_or_reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (freg_or_reg_name_forwards rs2)
                    (String.append (sep_forwards ())
                      (String.append (freg_or_reg_name_forwards rs3)
                        (String.append (sep_forwards ())
                          (String.append (frm_mnemonic_forwards rm) ""))))))))))))
  | .F_BIN_RM_TYPE_D (rs2, rs1, rm, rd, op) =>
    (pure (String.append (f_bin_rm_type_mnemonic_D_forwards op)
        (String.append (spc_forwards ())
          (String.append (freg_or_reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_or_reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (freg_or_reg_name_forwards rs2)
                    (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))))
  | .F_UN_RM_FF_TYPE_D (rs1, rm, rd, op) =>
    (pure (String.append (f_un_rm_ff_type_mnemonic_D_forwards op)
        (String.append (spc_forwards ())
          (String.append (freg_or_reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_or_reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .F_UN_RM_FX_TYPE_D (rs1, rm, rd, op) =>
    (pure (String.append (f_un_rm_fx_type_mnemonic_D_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_or_reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .F_UN_RM_XF_TYPE_D (rs1, rm, rd, op) =>
    (pure (String.append (f_un_rm_xf_type_mnemonic_D_forwards op)
        (String.append (spc_forwards ())
          (String.append (freg_or_reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .F_BIN_F_TYPE_D (rs2, rs1, rd, op) =>
    (pure (String.append (f_bin_f_type_mnemonic_D_forwards op)
        (String.append (spc_forwards ())
          (String.append (freg_or_reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_or_reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (freg_or_reg_name_forwards rs2) ""))))))))
  | .F_BIN_X_TYPE_D (rs2, rs1, rd, op) =>
    (pure (String.append (f_bin_x_type_mnemonic_D_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_or_reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (freg_or_reg_name_forwards rs2) ""))))))))
  | .F_UN_X_TYPE_D (rs1, rd, op) =>
    (pure (String.append (f_un_x_type_mnemonic_D_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (freg_name_forwards rs1) ""))))))
  | .F_UN_F_TYPE_D (rs1, rd, op) =>
    (pure (String.append (f_un_f_type_mnemonic_D_forwards op)
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .C_FLDSP (uimm, rd) =>
    (do
      bif ((xlen == 32) || (xlen == 64))
      then
        (pure (String.append "c.fldsp"
            (String.append (spc_forwards ())
              (String.append (freg_name_forwards rd)
                (String.append (sep_forwards ()) (String.append (← (hex_bits_6_forwards uimm)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_FSDSP (uimm, rs2) =>
    (do
      bif ((xlen == 32) || (xlen == 64))
      then
        (pure (String.append "c.fsdsp"
            (String.append (spc_forwards ())
              (String.append (freg_name_forwards rs2)
                (String.append (sep_forwards ()) (String.append (← (hex_bits_6_forwards uimm)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_FLD (uimm, rsc, rdc) =>
    (do
      bif ((xlen == 32) || (xlen == 64))
      then
        (pure (String.append "c.fld"
            (String.append (spc_forwards ())
              (String.append (creg_name_forwards rdc)
                (String.append (sep_forwards ())
                  (String.append (creg_name_forwards rsc)
                    (String.append (sep_forwards ())
                      (String.append
                        (← (hex_bits_8_forwards ((uimm : (BitVec 5)) ++ (0b000 : (BitVec 3))))) ""))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_FSD (uimm, rsc1, rsc2) =>
    (do
      bif ((xlen == 32) || (xlen == 64))
      then
        (pure (String.append "c.fsd"
            (String.append (spc_forwards ())
              (String.append (creg_name_forwards rsc1)
                (String.append (sep_forwards ())
                  (String.append (creg_name_forwards rsc2)
                    (String.append (sep_forwards ())
                      (String.append
                        (← (hex_bits_8_forwards ((uimm : (BitVec 5)) ++ (0b000 : (BitVec 3))))) ""))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SINVAL_VMA (rs1, rs2) =>
    (pure (String.append "sinval.vma"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rs1)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))
  | .SFENCE_W_INVAL () => (pure "sfence.w.inval")
  | .SFENCE_INVAL_IR () => (pure "sfence.inval.ir")
  | .SLLIUW (shamt, rs1, rd) =>
    (pure (String.append "slli.uw"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_6_forwards shamt)) ""))))))))
  | .ZBA_RTYPEUW (rs2, rs1, rd, op) =>
    (pure (String.append (zba_rtypeuw_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .ZBA_RTYPE (rs2, rs1, rd, op) =>
    (pure (String.append (zba_rtype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .RORIW (shamt, rs1, rd) =>
    (pure (String.append "roriw"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_5_forwards shamt)) ""))))))))
  | .RORI (shamt, rs1, rd) =>
    (pure (String.append "rori"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_6_forwards shamt)) ""))))))))
  | .ZBB_RTYPEW (rs2, rs1, rd, op) =>
    (pure (String.append (zbb_rtypew_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .ZBB_RTYPE (rs2, rs1, rd, op) =>
    (pure (String.append (zbb_rtype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .ZBB_EXTOP (rs1, rd, op) =>
    (pure (String.append (zbb_extop_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .REV8 (rs1, rd) =>
    (pure (String.append "rev8"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .ORCB (rs1, rd) =>
    (pure (String.append "orc.b"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .CPOP (rs1, rd) =>
    (pure (String.append "cpop"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .CPOPW (rs1, rd) =>
    (pure (String.append "cpopw"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .CLZ (rs1, rd) =>
    (pure (String.append "clz"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .CLZW (rs1, rd) =>
    (pure (String.append "clzw"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .CTZ (rs1, rd) =>
    (pure (String.append "ctz"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .CTZW (rs1, rd) =>
    (pure (String.append "ctzw"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .CLMUL (rs2, rs1, rd) =>
    (pure (String.append "clmul"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .CLMULH (rs2, rs1, rd) =>
    (pure (String.append "clmulh"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .CLMULR (rs2, rs1, rd) =>
    (pure (String.append "clmulr"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .ZBS_IOP (shamt, rs1, rd, op) =>
    (pure (String.append (zbs_iop_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_6_forwards shamt)) ""))))))))
  | .ZBS_RTYPE (rs2, rs1, rd, op) =>
    (pure (String.append (zbs_rtype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .C_LBU (uimm, rdc, rs1c) =>
    (pure (String.append "c.lbu"
        (String.append (spc_forwards ())
          (String.append (creg_name_forwards rdc)
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_2_forwards uimm))
                (String.append (opt_spc_forwards ())
                  (String.append "("
                    (String.append (opt_spc_forwards ())
                      (String.append (creg_name_forwards rs1c)
                        (String.append (opt_spc_forwards ()) (String.append ")" ""))))))))))))
  | .C_LHU (uimm, rdc, rs1c) =>
    (pure (String.append "c.lhu"
        (String.append (spc_forwards ())
          (String.append (creg_name_forwards rdc)
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_2_forwards uimm))
                (String.append (opt_spc_forwards ())
                  (String.append "("
                    (String.append (opt_spc_forwards ())
                      (String.append (creg_name_forwards rs1c)
                        (String.append (opt_spc_forwards ()) (String.append ")" ""))))))))))))
  | .C_LH (uimm, rdc, rs1c) =>
    (pure (String.append "c.lh"
        (String.append (spc_forwards ())
          (String.append (creg_name_forwards rdc)
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_2_forwards uimm))
                (String.append (opt_spc_forwards ())
                  (String.append "("
                    (String.append (opt_spc_forwards ())
                      (String.append (creg_name_forwards rs1c)
                        (String.append (opt_spc_forwards ()) (String.append ")" ""))))))))))))
  | .C_SB (uimm, rs1c, rs2c) =>
    (pure (String.append "c.sb"
        (String.append (spc_forwards ())
          (String.append (creg_name_forwards rs2c)
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_2_forwards uimm))
                (String.append (opt_spc_forwards ())
                  (String.append "("
                    (String.append (opt_spc_forwards ())
                      (String.append (creg_name_forwards rs1c)
                        (String.append (opt_spc_forwards ()) (String.append ")" ""))))))))))))
  | .C_SH (uimm, rs1c, rs2c) =>
    (pure (String.append "c.sh"
        (String.append (spc_forwards ())
          (String.append (creg_name_forwards rs1c)
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_2_forwards uimm))
                (String.append (opt_spc_forwards ())
                  (String.append "("
                    (String.append (opt_spc_forwards ())
                      (String.append (creg_name_forwards rs2c)
                        (String.append (opt_spc_forwards ()) (String.append ")" ""))))))))))))
  | .C_ZEXT_B rsdc =>
    (pure (String.append "c.zext.b"
        (String.append (spc_forwards ()) (String.append (creg_name_forwards rsdc) ""))))
  | .C_SEXT_B rsdc =>
    (pure (String.append "c.sext.b"
        (String.append (spc_forwards ()) (String.append (creg_name_forwards rsdc) ""))))
  | .C_ZEXT_H rsdc =>
    (pure (String.append "c.zext.h"
        (String.append (spc_forwards ()) (String.append (creg_name_forwards rsdc) ""))))
  | .C_SEXT_H rsdc =>
    (pure (String.append "c.sext.h"
        (String.append (spc_forwards ()) (String.append (creg_name_forwards rsdc) ""))))
  | .C_ZEXT_W rsdc =>
    (pure (String.append "c.zext.w"
        (String.append (spc_forwards ()) (String.append (creg_name_forwards rsdc) ""))))
  | .C_NOT rsdc =>
    (pure (String.append "c.not"
        (String.append (spc_forwards ()) (String.append (creg_name_forwards rsdc) ""))))
  | .C_MUL (rsdc, rs2c) =>
    (pure (String.append "c.mul"
        (String.append (spc_forwards ())
          (String.append (creg_name_forwards rsdc)
            (String.append (sep_forwards ()) (String.append (creg_name_forwards rs2c) ""))))))
  | .F_BIN_RM_TYPE_H (rs2, rs1, rm, rd, op) =>
    (pure (String.append (f_bin_rm_type_mnemonic_H_forwards op)
        (String.append (spc_forwards ())
          (String.append (freg_or_reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_or_reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (freg_or_reg_name_forwards rs2)
                    (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))))
  | .F_MADD_TYPE_H (rs3, rs2, rs1, rm, rd, op) =>
    (pure (String.append (f_madd_type_mnemonic_H_forwards op)
        (String.append (spc_forwards ())
          (String.append (freg_or_reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_or_reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (freg_or_reg_name_forwards rs2)
                    (String.append (sep_forwards ())
                      (String.append (freg_or_reg_name_forwards rs3)
                        (String.append (sep_forwards ())
                          (String.append (frm_mnemonic_forwards rm) ""))))))))))))
  | .F_BIN_F_TYPE_H (rs2, rs1, rd, op) =>
    (pure (String.append (f_bin_f_type_mnemonic_H_forwards op)
        (String.append (spc_forwards ())
          (String.append (freg_or_reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_or_reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (freg_or_reg_name_forwards rs2) ""))))))))
  | .F_BIN_X_TYPE_H (rs2, rs1, rd, op) =>
    (pure (String.append (f_bin_x_type_mnemonic_H_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_or_reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (freg_or_reg_name_forwards rs2) ""))))))))
  | .F_UN_RM_FF_TYPE_H (rs1, rm, rd, op) =>
    (pure (String.append (f_un_rm_ff_type_mnemonic_H_forwards op)
        (String.append (spc_forwards ())
          (String.append (freg_or_reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_or_reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .F_UN_RM_FX_TYPE_H (rs1, rm, rd, op) =>
    (pure (String.append (f_un_rm_fx_type_mnemonic_H_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_or_reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .F_UN_RM_XF_TYPE_H (rs1, rm, rd, op) =>
    (pure (String.append (f_un_rm_xf_type_mnemonic_H_forwards op)
        (String.append (spc_forwards ())
          (String.append (freg_or_reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .F_UN_F_TYPE_H (rs1, rd, op) =>
    (pure (String.append (f_un_f_type_mnemonic_H_forwards op)
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .F_UN_X_TYPE_H (rs1, rd, op) =>
    (pure (String.append (f_un_x_type_mnemonic_H_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (freg_name_forwards rs1) ""))))))
  | .FLI_H (constantidx, rd) =>
    (pure (String.append "fli.h"
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_5_forwards constantidx)) ""))))))
  | .FLI_S (constantidx, rd) =>
    (pure (String.append "fli.s"
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_5_forwards constantidx)) ""))))))
  | .FLI_D (constantidx, rd) =>
    (pure (String.append "fli.d"
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_5_forwards constantidx)) ""))))))
  | .FMINM_H (rs2, rs1, rd) =>
    (pure (String.append "fminm.h"
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (freg_name_forwards rs2) ""))))))))
  | .FMAXM_H (rs2, rs1, rd) =>
    (pure (String.append "fmaxm.h"
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (freg_name_forwards rs2) ""))))))))
  | .FMINM_S (rs2, rs1, rd) =>
    (pure (String.append "fminm.s"
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (freg_name_forwards rs2) ""))))))))
  | .FMAXM_S (rs2, rs1, rd) =>
    (pure (String.append "fmaxm.s"
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (freg_name_forwards rs2) ""))))))))
  | .FMINM_D (rs2, rs1, rd) =>
    (pure (String.append "fminm.d"
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (freg_name_forwards rs2) ""))))))))
  | .FMAXM_D (rs2, rs1, rd) =>
    (pure (String.append "fmaxm.d"
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (freg_name_forwards rs2) ""))))))))
  | .FROUND_H (rs1, rm, rd) =>
    (pure (String.append "fround.h"
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .FROUNDNX_H (rs1, rm, rd) =>
    (pure (String.append "froundnx.h"
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .FROUND_S (rs1, rm, rd) =>
    (pure (String.append "fround.s"
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .FROUNDNX_S (rs1, rm, rd) =>
    (pure (String.append "froundnx.s"
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .FROUND_D (rs1, rm, rd) =>
    (pure (String.append "fround.d"
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .FROUNDNX_D (rs1, rm, rd) =>
    (pure (String.append "froundnx.d"
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (frm_mnemonic_forwards rm) ""))))))))
  | .FMVH_X_D (rs1, rd) =>
    (pure (String.append "fmvh.x.d"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (freg_name_forwards rs1) ""))))))
  | .FMVP_D_X (rs2, rs1, rd) =>
    (pure (String.append "fmvp.d.x"
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .FLEQ_H (rs2, rs1, rd) =>
    (pure (String.append "fleq.h"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (freg_name_forwards rs2) ""))))))))
  | .FLTQ_H (rs2, rs1, rd) =>
    (pure (String.append "fltq.h"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (freg_name_forwards rs2) ""))))))))
  | .FLEQ_S (rs2, rs1, rd) =>
    (pure (String.append "fleq.s"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (freg_name_forwards rs2) ""))))))))
  | .FLTQ_S (rs2, rs1, rd) =>
    (pure (String.append "fltq.s"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (freg_name_forwards rs2) ""))))))))
  | .FLEQ_D (rs2, rs1, rd) =>
    (pure (String.append "fleq.d"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (freg_name_forwards rs2) ""))))))))
  | .FLTQ_D (rs2, rs1, rd) =>
    (pure (String.append "fltq.d"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (freg_name_forwards rs2) ""))))))))
  | .FCVTMOD_W_D (rs1, rd) =>
    (pure (String.append "fcvtmod.w.d"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (freg_name_forwards rs1) ""))))))
  | .SHA256SIG0 (rs1, rd) =>
    (pure (String.append "sha256sig0"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .SHA256SIG1 (rs1, rd) =>
    (pure (String.append "sha256sig1"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .SHA256SUM0 (rs1, rd) =>
    (pure (String.append "sha256sum0"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .SHA256SUM1 (rs1, rd) =>
    (pure (String.append "sha256sum1"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .AES32ESMI (bs, rs2, rs1, rd) =>
    (pure (String.append "aes32esmi"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs2)
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_2_forwards bs)) ""))))))))))
  | .AES32ESI (bs, rs2, rs1, rd) =>
    (pure (String.append "aes32esi"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs2)
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_2_forwards bs)) ""))))))))))
  | .AES32DSMI (bs, rs2, rs1, rd) =>
    (pure (String.append "aes32dsmi"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs2)
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_2_forwards bs)) ""))))))))))
  | .AES32DSI (bs, rs2, rs1, rd) =>
    (pure (String.append "aes32dsi"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs2)
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_2_forwards bs)) ""))))))))))
  | .SHA512SIG0L (rs2, rs1, rd) =>
    (pure (String.append "sha512sig0l"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .SHA512SIG0H (rs2, rs1, rd) =>
    (pure (String.append "sha512sig0h"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .SHA512SIG1L (rs2, rs1, rd) =>
    (pure (String.append "sha512sig1l"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .SHA512SIG1H (rs2, rs1, rd) =>
    (pure (String.append "sha512sig1h"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .SHA512SUM0R (rs2, rs1, rd) =>
    (pure (String.append "sha512sum0r"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .SHA512SUM1R (rs2, rs1, rd) =>
    (pure (String.append "sha512sum1r"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .AES64KS1I (rnum, rs1, rd) =>
    (pure (String.append "aes64ks1i"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (← (hex_bits_4_forwards rnum)) ""))))))))
  | .AES64KS2 (rs2, rs1, rd) =>
    (pure (String.append "aes64ks2"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .AES64IM (rs1, rd) =>
    (pure (String.append "aes64im"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .AES64ESM (rs2, rs1, rd) =>
    (pure (String.append "aes64esm"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .AES64ES (rs2, rs1, rd) =>
    (pure (String.append "aes64es"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .AES64DSM (rs2, rs1, rd) =>
    (pure (String.append "aes64dsm"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .AES64DS (rs2, rs1, rd) =>
    (pure (String.append "aes64ds"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .SHA512SIG0 (rs1, rd) =>
    (pure (String.append "sha512sig0"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .SHA512SIG1 (rs1, rd) =>
    (pure (String.append "sha512sig1"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .SHA512SUM0 (rs1, rd) =>
    (pure (String.append "sha512sum0"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .SHA512SUM1 (rs1, rd) =>
    (pure (String.append "sha512sum1"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .SM3P0 (rs1, rd) =>
    (pure (String.append "sm3p0"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .SM3P1 (rs1, rd) =>
    (pure (String.append "sm3p1"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .SM4ED (bs, rs2, rs1, rd) =>
    (pure (String.append "sm4ed"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs2)
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_2_forwards bs)) ""))))))))))
  | .SM4KS (bs, rs2, rs1, rd) =>
    (pure (String.append "sm4ks"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs2)
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_2_forwards bs)) ""))))))))))
  | .ZBKB_RTYPE (rs2, rs1, rd, op) =>
    (pure (String.append (zbkb_rtype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .ZBKB_PACKW (rs2, rs1, rd) =>
    (pure (String.append "packw"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .ZIP (rs1, rd) =>
    (pure (String.append "zip"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .UNZIP (rs1, rd) =>
    (pure (String.append "unzip"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .BREV8 (rs1, rd) =>
    (pure (String.append "brev8"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .XPERM8 (rs2, rs1, rd) =>
    (pure (String.append "xperm8"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .XPERM4 (rs2, rs1, rd) =>
    (pure (String.append "xperm4"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .ZICOND_RTYPE (rs2, rs1, rd, op) =>
    (pure (String.append (zicond_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .VSETVLI (ma, ta, sew, lmul, rs1, rd) =>
    (pure (String.append "vsetvli"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (← (sew_flag_backwards sew))
                    (String.append (← (maybe_lmul_flag_backwards lmul))
                      (String.append (ta_flag_backwards ta)
                        (String.append (ma_flag_backwards ma) "")))))))))))
  | .VSETVL (rs2, rs1, rd) =>
    (pure (String.append "vsetvl"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) ""))))))))
  | .VSETIVLI (ma, ta, sew, lmul, uimm, rd) =>
    (pure (String.append "vsetivli"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_5_forwards uimm))
                (String.append (sep_forwards ())
                  (String.append (← (sew_flag_backwards sew))
                    (String.append (← (maybe_lmul_flag_backwards lmul))
                      (String.append (ta_flag_backwards ta)
                        (String.append (ma_flag_backwards ma) "")))))))))))
  | .VVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (vvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .NVSTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (nvstype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .NVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (nvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .MASKTYPEV (vs2, vs1, vd) =>
    (pure (String.append "vmerge.vvm"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .MOVETYPEV (vs1, vd) =>
    (pure (String.append "vmv.v.v"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs1) ""))))))
  | .VXTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (vxtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .NXSTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (nxstype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .NXTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (nxtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VXSG (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (vxsg_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .MASKTYPEX (vs2, rs1, vd) =>
    (pure (String.append "vmerge.vxm"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .MOVETYPEX (rs1, vd) =>
    (pure (String.append "vmv.v.x"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .VITYPE (funct6, vm, vs2, simm, vd) =>
    (pure (String.append (vitype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_5_forwards simm))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .NISTYPE (funct6, vm, vs2, simm, vd) =>
    (pure (String.append (nistype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_5_forwards simm))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .NITYPE (funct6, vm, vs2, simm, vd) =>
    (pure (String.append (nitype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_5_forwards simm))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VISG (funct6, vm, vs2, simm, vd) =>
    (pure (String.append (visg_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_5_forwards simm))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .MASKTYPEI (vs2, simm, vd) =>
    (pure (String.append "vmerge.vim"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_5_forwards simm))
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .MOVETYPEI (vd, simm) =>
    (pure (String.append "vmv.v.i"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ()) (String.append (← (hex_bits_5_forwards simm)) ""))))))
  | .VMVRTYPE (vs2, simm, vd) =>
    (pure (String.append "vmv"
        (String.append (← (simm_string_forwards simm))
          (String.append "r.v"
            (String.append (spc_forwards ())
              (String.append (vreg_name_forwards vd)
                (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs2) ""))))))))
  | .MVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (mvvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .MVVMATYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (mvvmatype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs1)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs2)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .WVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (wvvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .WVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (wvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .WMVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (wmvvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs1)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs2)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VEXT2TYPE (funct6, vm, vs2, vd) =>
    (pure (String.append (vext2type_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VEXT4TYPE (funct6, vm, vs2, vd) =>
    (pure (String.append (vext4type_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VEXT8TYPE (funct6, vm, vs2, vd) =>
    (pure (String.append (vext8type_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VMVXS (vs2, rd) =>
    (pure (String.append "vmv.x.s"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs2) ""))))))
  | .MVVCOMPRESS (vs2, vs1, vd) =>
    (pure (String.append "vcompress.vm"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs1) ""))))))))
  | .MVXTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (mvxtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .MVXMATYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (mvxmatype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs2)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .WVXTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (wvxtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .WXTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (wxtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .WMVXTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (wmvxtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs2)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VMVSX (rs1, vd) =>
    (pure (String.append "vmv.s.x"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))
  | .FVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (fvvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FVVMATYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (fvvmatype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs1)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs2)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FWVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (fwvvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FWVVMATYPE (funct6, vm, vs1, vs2, vd) =>
    (pure (String.append (fwvvmatype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs1)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs2)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FWVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (fwvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VFUNARY0 (vm, vs2, vfunary0, vd) =>
    (pure (String.append (vfunary0_mnemonic_forwards vfunary0)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VFWUNARY0 (vm, vs2, vfwunary0, vd) =>
    (pure (String.append (vfwunary0_mnemonic_forwards vfwunary0)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VFNUNARY0 (vm, vs2, vfnunary0, vd) =>
    (pure (String.append (vfnunary0_mnemonic_forwards vfnunary0)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VFUNARY1 (vm, vs2, vfunary1, vd) =>
    (pure (String.append (vfunary1_mnemonic_forwards vfunary1)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VFMVFS (vs2, rd) =>
    (pure (String.append "vfmv.f.s"
        (String.append (spc_forwards ())
          (String.append (freg_name_forwards rd)
            (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs2) ""))))))
  | .FVFTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (fvftype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (freg_name_forwards rs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FVFMATYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (fvfmatype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs2)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FWVFTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (fwvftype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (freg_name_forwards rs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FWVFMATYPE (funct6, vm, rs1, vs2, vd) =>
    (pure (String.append (fwvfmatype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (freg_name_forwards rs1)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs2)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FWFTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (fwftype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (freg_name_forwards rs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VFMERGE (vs2, rs1, vd) =>
    (pure (String.append "vfmerge.vfm"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (freg_name_forwards rs1)
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .VFMV (rs1, vd) =>
    (pure (String.append "vfmv.v.f"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ()) (String.append (freg_name_forwards rs1) ""))))))
  | .VFMVSF (rs1, vd) =>
    (pure (String.append "vfmv.s.f"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ()) (String.append (freg_name_forwards rs1) ""))))))
  | .VLSEGTYPE (nf, vm, rs1, width, vd) =>
    (pure (String.append "vl"
        (String.append (nfields_string_forwards nf)
          (String.append "e"
            (String.append (vlewidth_bitsnumberstr_forwards width)
              (String.append ".v"
                (String.append (spc_forwards ())
                  (String.append (vreg_name_forwards vd)
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (reg_name_forwards rs1)
                          (String.append ")" (String.append (maybe_vmask_backwards vm) "")))))))))))))
  | .VLSEGFFTYPE (nf, vm, rs1, width, vd) =>
    (pure (String.append "vl"
        (String.append (nfields_string_forwards nf)
          (String.append "e"
            (String.append (vlewidth_bitsnumberstr_forwards width)
              (String.append "ff.v"
                (String.append (spc_forwards ())
                  (String.append (vreg_name_forwards vd)
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (reg_name_forwards rs1)
                          (String.append ")" (String.append (maybe_vmask_backwards vm) "")))))))))))))
  | .VSSEGTYPE (nf, vm, rs1, width, vs3) =>
    (pure (String.append "vs"
        (String.append (nfields_string_forwards nf)
          (String.append "e"
            (String.append (vlewidth_bitsnumberstr_forwards width)
              (String.append ".v"
                (String.append (spc_forwards ())
                  (String.append (vreg_name_forwards vs3)
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (reg_name_forwards rs1)
                          (String.append ")" (String.append (maybe_vmask_backwards vm) "")))))))))))))
  | .VLSSEGTYPE (nf, vm, rs2, rs1, width, vd) =>
    (pure (String.append "vls"
        (String.append (nfields_string_forwards nf)
          (String.append "e"
            (String.append (vlewidth_bitsnumberstr_forwards width)
              (String.append ".v"
                (String.append (spc_forwards ())
                  (String.append (vreg_name_forwards vd)
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (reg_name_forwards rs1)
                          (String.append ")"
                            (String.append (sep_forwards ())
                              (String.append (reg_name_forwards rs2)
                                (String.append (maybe_vmask_backwards vm) "")))))))))))))))
  | .VSSSEGTYPE (nf, vm, rs2, rs1, width, vs3) =>
    (pure (String.append "vss"
        (String.append (nfields_string_forwards nf)
          (String.append "e"
            (String.append (vlewidth_bitsnumberstr_forwards width)
              (String.append ".v"
                (String.append (spc_forwards ())
                  (String.append (vreg_name_forwards vs3)
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (reg_name_forwards rs1)
                          (String.append ")"
                            (String.append (sep_forwards ())
                              (String.append (reg_name_forwards rs2)
                                (String.append (maybe_vmask_backwards vm) "")))))))))))))))
  | .VLUXSEGTYPE (nf, vm, vs2, rs1, width, vd) =>
    (pure (String.append "vlux"
        (String.append (nfields_string_forwards nf)
          (String.append "ei"
            (String.append (vlewidth_bitsnumberstr_forwards width)
              (String.append ".v"
                (String.append (spc_forwards ())
                  (String.append (vreg_name_forwards vd)
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (reg_name_forwards rs1)
                          (String.append ")"
                            (String.append (sep_forwards ())
                              (String.append (vreg_name_forwards vs2)
                                (String.append (maybe_vmask_backwards vm) "")))))))))))))))
  | .VLOXSEGTYPE (nf, vm, vs2, rs1, width, vd) =>
    (pure (String.append "vlox"
        (String.append (nfields_string_forwards nf)
          (String.append "ei"
            (String.append (vlewidth_bitsnumberstr_forwards width)
              (String.append ".v"
                (String.append (spc_forwards ())
                  (String.append (vreg_name_forwards vd)
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (reg_name_forwards rs1)
                          (String.append ")"
                            (String.append (sep_forwards ())
                              (String.append (vreg_name_forwards vs2)
                                (String.append (maybe_vmask_backwards vm) "")))))))))))))))
  | .VSUXSEGTYPE (nf, vm, vs2, rs1, width, vs3) =>
    (pure (String.append "vsux"
        (String.append (nfields_string_forwards nf)
          (String.append "ei"
            (String.append (vlewidth_bitsnumberstr_forwards width)
              (String.append ".v"
                (String.append (spc_forwards ())
                  (String.append (vreg_name_forwards vs3)
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (reg_name_forwards rs1)
                          (String.append ")"
                            (String.append (sep_forwards ())
                              (String.append (vreg_name_forwards vs2)
                                (String.append (maybe_vmask_backwards vm) "")))))))))))))))
  | .VSOXSEGTYPE (nf, vm, vs2, rs1, width, vs3) =>
    (pure (String.append "vsox"
        (String.append (nfields_string_forwards nf)
          (String.append "ei"
            (String.append (vlewidth_bitsnumberstr_forwards width)
              (String.append ".v"
                (String.append (spc_forwards ())
                  (String.append (vreg_name_forwards vs3)
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (reg_name_forwards rs1)
                          (String.append ")"
                            (String.append (sep_forwards ())
                              (String.append (vreg_name_forwards vs2)
                                (String.append (maybe_vmask_backwards vm) "")))))))))))))))
  | .VLRETYPE (nf, rs1, width, vd) =>
    (pure (String.append "vl"
        (String.append (nfields_string_forwards nf)
          (String.append "re"
            (String.append (vlewidth_bitsnumberstr_forwards width)
              (String.append ".v"
                (String.append (spc_forwards ())
                  (String.append (vreg_name_forwards vd)
                    (String.append (sep_forwards ())
                      (String.append "("
                        (String.append (reg_name_forwards rs1) (String.append ")" ""))))))))))))
  | .VSRETYPE (nf, rs1, vs3) =>
    (pure (String.append "vs"
        (String.append (nfields_string_forwards nf)
          (String.append "r.v"
            (String.append (spc_forwards ())
              (String.append (vreg_name_forwards vs3)
                (String.append (sep_forwards ())
                  (String.append "(" (String.append (reg_name_forwards rs1) (String.append ")" ""))))))))))
  | .VMTYPE (rs1, vd_or_vs3, op) =>
    (pure (String.append (vmtype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd_or_vs3)
            (String.append (sep_forwards ())
              (String.append "(" (String.append (reg_name_forwards rs1) (String.append ")" ""))))))))
  | .MMTYPE (funct6, vs2, vs1, vd) =>
    (pure (String.append (mmtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs1) ""))))))))
  | .VCPOP_M (vm, vs2, rd) =>
    (pure (String.append "vpopc.m"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VFIRST_M (vm, vs2, rd) =>
    (pure (String.append "vfirst.m"
        (String.append (spc_forwards ())
          (String.append (reg_name_forwards rd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VMSBF_M (vm, vs2, vd) =>
    (pure (String.append "vmsbf.m"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VMSIF_M (vm, vs2, vd) =>
    (pure (String.append "vmsif.m"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VMSOF_M (vm, vs2, vd) =>
    (pure (String.append "vmsof.m"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VIOTA_M (vm, vs2, vd) =>
    (pure (String.append "viota.m"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VID_V (vm, vd) =>
    (pure (String.append "vid.v"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd) (String.append (maybe_vmask_backwards vm) "")))))
  | .VVMTYPE (funct6, vs2, vs1, vd) =>
    (pure (String.append (vvmtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .VVMCTYPE (funct6, vs2, vs1, vd) =>
    (pure (String.append (vvmctype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs1) ""))))))))
  | .VVMSTYPE (funct6, vs2, vs1, vd) =>
    (pure (String.append (vvmstype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .VVCMPTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (vvcmptype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VXMTYPE (funct6, vs2, rs1, vd) =>
    (pure (String.append (vxmtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .VXMCTYPE (funct6, vs2, rs1, vd) =>
    (pure (String.append (vxmctype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) ""))))))))
  | .VXMSTYPE (funct6, vs2, rs1, vd) =>
    (pure (String.append (vxmstype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .VXCMPTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (vxcmptype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VIMTYPE (funct6, vs2, simm, vd) =>
    (pure (String.append (vimtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_5_forwards simm))
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .VIMCTYPE (funct6, vs2, simm, vd) =>
    (pure (String.append (vimctype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (← (hex_bits_5_forwards simm)) ""))))))))
  | .VIMSTYPE (funct6, vs2, simm, vd) =>
    (pure (String.append (vimstype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_5_forwards simm))
                    (String.append (sep_forwards ()) (String.append "v0" ""))))))))))
  | .VICMPTYPE (funct6, vm, vs2, simm, vd) =>
    (pure (String.append (vicmptype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_5_forwards simm))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FVVMTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (fvvmtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .FVFMTYPE (funct6, vm, vs2, rs1, vd) =>
    (pure (String.append (fvfmtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (freg_name_forwards rs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .RIVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (rivvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .RMVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (rmvvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .RFVVTYPE (funct6, vm, vs2, vs1, vd) =>
    (pure (String.append (rfvvtype_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .ZICBOM (cbop, rs1) =>
    (pure (String.append (cbop_mnemonic_forwards cbop)
        (String.append (spc_forwards ())
          (String.append "("
            (String.append (opt_spc_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (opt_spc_forwards ()) (String.append ")" ""))))))))
  | .ZICBOZ rs1 =>
    (pure (String.append "cbo.zero"
        (String.append (spc_forwards ())
          (String.append "("
            (String.append (opt_spc_forwards ())
              (String.append (reg_name_forwards rs1)
                (String.append (opt_spc_forwards ()) (String.append ")" ""))))))))
  | .VANDN_VV (vm, vs1, vs2, vd) =>
    (pure (String.append "vandn.vv"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VANDN_VX (vm, vs2, rs1, vd) =>
    (pure (String.append "vandn.vx"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VBREV_V (vm, vs2, vd) =>
    (pure (String.append "vbrev.v"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VBREV8_V (vm, vs2, vd) =>
    (pure (String.append "vbrev8.v"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VREV8_V (vm, vs2, vd) =>
    (pure (String.append "vrev8.v"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (maybe_vmask_backwards vm) "")))))))
  | .VCLZ_V (vm, vs2, vd) =>
    (pure (String.append "vclz.v"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (maybe_vmask_backwards vm) ""))))))))
  | .VCTZ_V (vm, vs2, vd) =>
    (pure (String.append "vctz.v"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (maybe_vmask_backwards vm) ""))))))))
  | .VCPOP_V (vm, vs2, vd) =>
    (pure (String.append "vcpop.v"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (maybe_vmask_backwards vm) ""))))))))
  | .VROL_VV (vm, vs1, vs2, vd) =>
    (pure (String.append "vrol.vv"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VROL_VX (vm, vs2, rs1, vd) =>
    (pure (String.append "vrol.vx"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VROR_VV (vm, vs1, vs2, vd) =>
    (pure (String.append "vror.vv"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VROR_VX (vm, vs2, rs1, vd) =>
    (pure (String.append "vror.vx"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VROR_VI (vm, vs2, uimm, vd) =>
    (pure (String.append "vror.vi"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_5_forwards uimm))
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VWSLL_VV (vm, vs2, vs1, vd) =>
    (pure (String.append "vwsll.vv"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (sep_forwards ()) (String.append (maybe_vmask_backwards vm) ""))))))))))
  | .VWSLL_VX (vm, vs2, rs1, vd) =>
    (pure (String.append "vwsll.vx"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (sep_forwards ()) (String.append (maybe_vmask_backwards vm) ""))))))))))
  | .VWSLL_VI (vm, vs2, uimm, vd) =>
    (pure (String.append "vwsll.vi"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_5_forwards uimm))
                    (String.append (sep_forwards ()) (String.append (maybe_vmask_backwards vm) ""))))))))))
  | .VCLMUL_VV (vm, vs2, vs1, vd) =>
    (pure (String.append "vclmul.vv"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VCLMUL_VX (vm, vs2, rs1, vd) =>
    (pure (String.append "vclmul.vx"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VCLMULH_VV (vm, vs2, vs1, vd) =>
    (pure (String.append "vclmulh.vv"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (vreg_name_forwards vs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VCLMULH_VX (vm, vs2, rs1, vd) =>
    (pure (String.append "vclmulh.vx"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ())
                  (String.append (reg_name_forwards rs1)
                    (String.append (maybe_vmask_backwards vm) "")))))))))
  | .VSHA2MS_VV (vs2, vs1, vd) =>
    (pure (String.append "vsha2ms.vv"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2) (String.append (vreg_name_forwards vs1) "")))))))
  | .ZVKSHA2TYPE (funct6, vs2, vs1, vd) =>
    (pure (String.append (vsha2c_mnemonic_forwards funct6)
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (spc_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (spc_forwards ()) (String.append (vreg_name_forwards vs1) ""))))))))
  | .VSM3ME_VV (vs2, vs1, vd) =>
    (pure (String.append "vsm3me.vv"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (vreg_name_forwards vs1) ""))))))))
  | .VSM3C_VI (vs2, uimm, vd) =>
    (pure (String.append "vsm3c.vi"
        (String.append (spc_forwards ())
          (String.append (vreg_name_forwards vd)
            (String.append (sep_forwards ())
              (String.append (vreg_name_forwards vs2)
                (String.append (sep_forwards ()) (String.append (← (hex_bits_5_forwards uimm)) ""))))))))
  | .ZIMOP_MOP_R (mop, rs1, rd) =>
    (pure (String.append "mop.r."
        (String.append (← (dec_bits_5_forwards mop))
          (String.append (spc_forwards ())
            (String.append (reg_name_forwards rd)
              (String.append (sep_forwards ()) (String.append (reg_name_forwards rs1) "")))))))
  | .ZIMOP_MOP_RR (mop, rs2, rs1, rd) =>
    (pure (String.append "mop.rr."
        (String.append (← (dec_bits_3_forwards mop))
          (String.append (spc_forwards ())
            (String.append (reg_name_forwards rd)
              (String.append (sep_forwards ())
                (String.append (reg_name_forwards rs1)
                  (String.append (sep_forwards ()) (String.append (reg_name_forwards rs2) "")))))))))
  | .ZCMOP mop =>
    (pure (String.append "c.mop."
        (String.append (← (dec_bits_4_forwards ((mop : (BitVec 3)) ++ (0b1 : (BitVec 1))))) "")))
  | .ILLEGAL s =>
    (pure (String.append "illegal"
        (String.append (spc_forwards ()) (String.append (← (hex_bits_32_forwards s)) ""))))
  | .C_ILLEGAL s =>
    (pure (String.append "c.illegal"
        (String.append (spc_forwards ()) (String.append (← (hex_bits_16_forwards s)) ""))))
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def print_insn (insn : ast) : SailM String := do
  (assembly_forwards insn)

def ptw_error_to_str (e : PTW_Error) : String :=
  match e with
  | .PTW_Invalid_Addr () => "invalid-source-addr"
  | .PTW_Access () => "mem-access-error"
  | .PTW_Invalid_PTE () => "invalid-pte"
  | .PTW_No_Permission () => "no-permission"
  | .PTW_Misaligned () => "misaligned-superpage"
  | .PTW_PTE_Update () => "pte-update-needed"
  | .PTW_Ext_Error e => "extension-error"

def undefined_word_width (_ : Unit) : SailM word_width := do
  (internal_pick [BYTE, HALF, WORD, DOUBLE])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def word_width_of_num (arg_ : Nat) : word_width :=
  match arg_ with
  | 0 => BYTE
  | 1 => HALF
  | 2 => WORD
  | _ => DOUBLE

def num_of_word_width (arg_ : word_width) : Int :=
  match arg_ with
  | BYTE => 0
  | HALF => 1
  | WORD => 2
  | DOUBLE => 3

def undefined_InterruptType (_ : Unit) : SailM InterruptType := do
  (internal_pick
    [I_U_Software, I_S_Software, I_M_Software, I_U_Timer, I_S_Timer, I_M_Timer, I_U_External, I_S_External, I_M_External])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 8 -/
def InterruptType_of_num (arg_ : Nat) : InterruptType :=
  match arg_ with
  | 0 => I_U_Software
  | 1 => I_S_Software
  | 2 => I_M_Software
  | 3 => I_U_Timer
  | 4 => I_S_Timer
  | 5 => I_M_Timer
  | 6 => I_U_External
  | 7 => I_S_External
  | _ => I_M_External

def num_of_InterruptType (arg_ : InterruptType) : Int :=
  match arg_ with
  | I_U_Software => 0
  | I_S_Software => 1
  | I_M_Software => 2
  | I_U_Timer => 3
  | I_S_Timer => 4
  | I_M_Timer => 5
  | I_U_External => 6
  | I_S_External => 7
  | I_M_External => 8

def interruptType_to_bits (i : InterruptType) : (BitVec 8) :=
  match i with
  | I_U_Software => (0x00 : (BitVec 8))
  | I_S_Software => (0x01 : (BitVec 8))
  | I_M_Software => (0x03 : (BitVec 8))
  | I_U_Timer => (0x04 : (BitVec 8))
  | I_S_Timer => (0x05 : (BitVec 8))
  | I_M_Timer => (0x07 : (BitVec 8))
  | I_U_External => (0x08 : (BitVec 8))
  | I_S_External => (0x09 : (BitVec 8))
  | I_M_External => (0x0B : (BitVec 8))

def exceptionType_to_bits (e : ExceptionType) : (BitVec 8) :=
  match e with
  | .E_Fetch_Addr_Align () => (0x00 : (BitVec 8))
  | .E_Fetch_Access_Fault () => (0x01 : (BitVec 8))
  | .E_Illegal_Instr () => (0x02 : (BitVec 8))
  | .E_Breakpoint () => (0x03 : (BitVec 8))
  | .E_Load_Addr_Align () => (0x04 : (BitVec 8))
  | .E_Load_Access_Fault () => (0x05 : (BitVec 8))
  | .E_SAMO_Addr_Align () => (0x06 : (BitVec 8))
  | .E_SAMO_Access_Fault () => (0x07 : (BitVec 8))
  | .E_U_EnvCall () => (0x08 : (BitVec 8))
  | .E_S_EnvCall () => (0x09 : (BitVec 8))
  | .E_Reserved_10 () => (0x0A : (BitVec 8))
  | .E_M_EnvCall () => (0x0B : (BitVec 8))
  | .E_Fetch_Page_Fault () => (0x0C : (BitVec 8))
  | .E_Load_Page_Fault () => (0x0D : (BitVec 8))
  | .E_Reserved_14 () => (0x0E : (BitVec 8))
  | .E_SAMO_Page_Fault () => (0x0F : (BitVec 8))
  | .E_Extension e => (ext_exc_type_to_bits e)

def num_of_ExceptionType (e : ExceptionType) : Int :=
  match e with
  | .E_Fetch_Addr_Align () => 0
  | .E_Fetch_Access_Fault () => 1
  | .E_Illegal_Instr () => 2
  | .E_Breakpoint () => 3
  | .E_Load_Addr_Align () => 4
  | .E_Load_Access_Fault () => 5
  | .E_SAMO_Addr_Align () => 6
  | .E_SAMO_Access_Fault () => 7
  | .E_U_EnvCall () => 8
  | .E_S_EnvCall () => 9
  | .E_Reserved_10 () => 10
  | .E_M_EnvCall () => 11
  | .E_Fetch_Page_Fault () => 12
  | .E_Load_Page_Fault () => 13
  | .E_Reserved_14 () => 14
  | .E_SAMO_Page_Fault () => 15
  | .E_Extension e => (num_of_ext_exc_type e)

def undefined_TrapVectorMode (_ : Unit) : SailM TrapVectorMode := do
  (internal_pick [TV_Direct, TV_Vector, TV_Reserved])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def TrapVectorMode_of_num (arg_ : Nat) : TrapVectorMode :=
  match arg_ with
  | 0 => TV_Direct
  | 1 => TV_Vector
  | _ => TV_Reserved

def num_of_TrapVectorMode (arg_ : TrapVectorMode) : Int :=
  match arg_ with
  | TV_Direct => 0
  | TV_Vector => 1
  | TV_Reserved => 2

def trapVectorMode_of_bits (m : (BitVec 2)) : TrapVectorMode :=
  match_bv m with
  | 00 => TV_Direct
  | 01 => TV_Vector
  | _ => TV_Reserved

def undefined_ExtStatus (_ : Unit) : SailM ExtStatus := do
  (internal_pick [Off, Initial, Clean, Dirty])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def ExtStatus_of_num (arg_ : Nat) : ExtStatus :=
  match arg_ with
  | 0 => Off
  | 1 => Initial
  | 2 => Clean
  | _ => Dirty

def num_of_ExtStatus (arg_ : ExtStatus) : Int :=
  match arg_ with
  | Off => 0
  | Initial => 1
  | Clean => 2
  | Dirty => 3

def extStatus_bits_forwards (arg_ : ExtStatus) : (BitVec 2) :=
  match arg_ with
  | Off => (0b00 : (BitVec 2))
  | Initial => (0b01 : (BitVec 2))
  | Clean => (0b10 : (BitVec 2))
  | Dirty => (0b11 : (BitVec 2))

def extStatus_bits_backwards (arg_ : (BitVec 2)) : ExtStatus :=
  match_bv arg_ with
  | 00 => Off
  | 01 => Initial
  | 10 => Clean
  | _ => Dirty

def extStatus_bits_forwards_matches (arg_ : ExtStatus) : Bool :=
  match arg_ with
  | Off => true
  | Initial => true
  | Clean => true
  | Dirty => true
  | _ => false

def extStatus_bits_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match_bv arg_ with
  | 00 => true
  | 01 => true
  | 10 => true
  | 11 => true
  | _ => false

def extStatus_to_bits (e : ExtStatus) : (BitVec 2) :=
  (extStatus_bits_forwards e)

def extStatus_of_bits (b : (BitVec 2)) : ExtStatus :=
  (extStatus_bits_backwards b)

def undefined_SATPMode (_ : Unit) : SailM SATPMode := do
  (internal_pick [Bare, Sv32, Sv39, Sv48, Sv57])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def SATPMode_of_num (arg_ : Nat) : SATPMode :=
  match arg_ with
  | 0 => Bare
  | 1 => Sv32
  | 2 => Sv39
  | 3 => Sv48
  | _ => Sv57

def num_of_SATPMode (arg_ : SATPMode) : Int :=
  match arg_ with
  | Bare => 0
  | Sv32 => 1
  | Sv39 => 2
  | Sv48 => 3
  | Sv57 => 4

def satpMode_of_bits (a : Architecture) (m : (BitVec 4)) : (Option SATPMode) :=
  match (a, m) with
  | (_, 0b0000) => (some Bare)
  | (RV32, 0b0001) => (some Sv32)
  | (RV64, 0b1000) => (some Sv39)
  | (RV64, 0b1001) => (some Sv48)
  | (RV64, 0b1010) => (some Sv57)
  | (_, _) => none

def undefined_uop (_ : Unit) : SailM uop := do
  (internal_pick [LUI, AUIPC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def uop_of_num (arg_ : Nat) : uop :=
  match arg_ with
  | 0 => LUI
  | _ => AUIPC

def num_of_uop (arg_ : uop) : Int :=
  match arg_ with
  | LUI => 0
  | AUIPC => 1

def undefined_bop (_ : Unit) : SailM bop := do
  (internal_pick [BEQ, BNE, BLT, BGE, BLTU, BGEU])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def bop_of_num (arg_ : Nat) : bop :=
  match arg_ with
  | 0 => BEQ
  | 1 => BNE
  | 2 => BLT
  | 3 => BGE
  | 4 => BLTU
  | _ => BGEU

def num_of_bop (arg_ : bop) : Int :=
  match arg_ with
  | BEQ => 0
  | BNE => 1
  | BLT => 2
  | BGE => 3
  | BLTU => 4
  | BGEU => 5

def undefined_iop (_ : Unit) : SailM iop := do
  (internal_pick [ADDI, SLTI, SLTIU, XORI, ORI, ANDI])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def iop_of_num (arg_ : Nat) : iop :=
  match arg_ with
  | 0 => ADDI
  | 1 => SLTI
  | 2 => SLTIU
  | 3 => XORI
  | 4 => ORI
  | _ => ANDI

def num_of_iop (arg_ : iop) : Int :=
  match arg_ with
  | ADDI => 0
  | SLTI => 1
  | SLTIU => 2
  | XORI => 3
  | ORI => 4
  | ANDI => 5

def undefined_sop (_ : Unit) : SailM sop := do
  (internal_pick [SLLI, SRLI, SRAI])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def sop_of_num (arg_ : Nat) : sop :=
  match arg_ with
  | 0 => SLLI
  | 1 => SRLI
  | _ => SRAI

def num_of_sop (arg_ : sop) : Int :=
  match arg_ with
  | SLLI => 0
  | SRLI => 1
  | SRAI => 2

def undefined_rop (_ : Unit) : SailM rop := do
  (internal_pick [ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 9 -/
def rop_of_num (arg_ : Nat) : rop :=
  match arg_ with
  | 0 => ADD
  | 1 => SUB
  | 2 => SLL
  | 3 => SLT
  | 4 => SLTU
  | 5 => XOR
  | 6 => SRL
  | 7 => SRA
  | 8 => OR
  | _ => AND

def num_of_rop (arg_ : rop) : Int :=
  match arg_ with
  | ADD => 0
  | SUB => 1
  | SLL => 2
  | SLT => 3
  | SLTU => 4
  | XOR => 5
  | SRL => 6
  | SRA => 7
  | OR => 8
  | AND => 9

def undefined_ropw (_ : Unit) : SailM ropw := do
  (internal_pick [ADDW, SUBW, SLLW, SRLW, SRAW])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def ropw_of_num (arg_ : Nat) : ropw :=
  match arg_ with
  | 0 => ADDW
  | 1 => SUBW
  | 2 => SLLW
  | 3 => SRLW
  | _ => SRAW

def num_of_ropw (arg_ : ropw) : Int :=
  match arg_ with
  | ADDW => 0
  | SUBW => 1
  | SLLW => 2
  | SRLW => 3
  | SRAW => 4

def undefined_sopw (_ : Unit) : SailM sopw := do
  (internal_pick [SLLIW, SRLIW, SRAIW])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def sopw_of_num (arg_ : Nat) : sopw :=
  match arg_ with
  | 0 => SLLIW
  | 1 => SRLIW
  | _ => SRAIW

def num_of_sopw (arg_ : sopw) : Int :=
  match arg_ with
  | SLLIW => 0
  | SRLIW => 1
  | SRAIW => 2

def undefined_amoop (_ : Unit) : SailM amoop := do
  (internal_pick [AMOSWAP, AMOADD, AMOXOR, AMOAND, AMOOR, AMOMIN, AMOMAX, AMOMINU, AMOMAXU])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 8 -/
def amoop_of_num (arg_ : Nat) : amoop :=
  match arg_ with
  | 0 => AMOSWAP
  | 1 => AMOADD
  | 2 => AMOXOR
  | 3 => AMOAND
  | 4 => AMOOR
  | 5 => AMOMIN
  | 6 => AMOMAX
  | 7 => AMOMINU
  | _ => AMOMAXU

def num_of_amoop (arg_ : amoop) : Int :=
  match arg_ with
  | AMOSWAP => 0
  | AMOADD => 1
  | AMOXOR => 2
  | AMOAND => 3
  | AMOOR => 4
  | AMOMIN => 5
  | AMOMAX => 6
  | AMOMINU => 7
  | AMOMAXU => 8

def undefined_csrop (_ : Unit) : SailM csrop := do
  (internal_pick [CSRRW, CSRRS, CSRRC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def csrop_of_num (arg_ : Nat) : csrop :=
  match arg_ with
  | 0 => CSRRW
  | 1 => CSRRS
  | _ => CSRRC

def num_of_csrop (arg_ : csrop) : Int :=
  match arg_ with
  | CSRRW => 0
  | CSRRS => 1
  | CSRRC => 2

def undefined_cbop_zicbom (_ : Unit) : SailM cbop_zicbom := do
  (internal_pick [CBO_CLEAN, CBO_FLUSH, CBO_INVAL])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def cbop_zicbom_of_num (arg_ : Nat) : cbop_zicbom :=
  match arg_ with
  | 0 => CBO_CLEAN
  | 1 => CBO_FLUSH
  | _ => CBO_INVAL

def num_of_cbop_zicbom (arg_ : cbop_zicbom) : Int :=
  match arg_ with
  | CBO_CLEAN => 0
  | CBO_FLUSH => 1
  | CBO_INVAL => 2

def undefined_brop_zba (_ : Unit) : SailM brop_zba := do
  (internal_pick [SH1ADD, SH2ADD, SH3ADD])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def brop_zba_of_num (arg_ : Nat) : brop_zba :=
  match arg_ with
  | 0 => SH1ADD
  | 1 => SH2ADD
  | _ => SH3ADD

def num_of_brop_zba (arg_ : brop_zba) : Int :=
  match arg_ with
  | SH1ADD => 0
  | SH2ADD => 1
  | SH3ADD => 2

def undefined_brop_zbb (_ : Unit) : SailM brop_zbb := do
  (internal_pick [ANDN, ORN, XNOR, MAX, MAXU, MIN, MINU, ROL, ROR])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 8 -/
def brop_zbb_of_num (arg_ : Nat) : brop_zbb :=
  match arg_ with
  | 0 => ANDN
  | 1 => ORN
  | 2 => XNOR
  | 3 => MAX
  | 4 => MAXU
  | 5 => MIN
  | 6 => MINU
  | 7 => ROL
  | _ => ROR

def num_of_brop_zbb (arg_ : brop_zbb) : Int :=
  match arg_ with
  | ANDN => 0
  | ORN => 1
  | XNOR => 2
  | MAX => 3
  | MAXU => 4
  | MIN => 5
  | MINU => 6
  | ROL => 7
  | ROR => 8

def undefined_brop_zbkb (_ : Unit) : SailM brop_zbkb := do
  (internal_pick [PACK, PACKH])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def brop_zbkb_of_num (arg_ : Nat) : brop_zbkb :=
  match arg_ with
  | 0 => PACK
  | _ => PACKH

def num_of_brop_zbkb (arg_ : brop_zbkb) : Int :=
  match arg_ with
  | PACK => 0
  | PACKH => 1

def undefined_brop_zbs (_ : Unit) : SailM brop_zbs := do
  (internal_pick [BCLR, BEXT, BINV, BSET])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def brop_zbs_of_num (arg_ : Nat) : brop_zbs :=
  match arg_ with
  | 0 => BCLR
  | 1 => BEXT
  | 2 => BINV
  | _ => BSET

def num_of_brop_zbs (arg_ : brop_zbs) : Int :=
  match arg_ with
  | BCLR => 0
  | BEXT => 1
  | BINV => 2
  | BSET => 3

def undefined_bropw_zba (_ : Unit) : SailM bropw_zba := do
  (internal_pick [ADDUW, SH1ADDUW, SH2ADDUW, SH3ADDUW])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def bropw_zba_of_num (arg_ : Nat) : bropw_zba :=
  match arg_ with
  | 0 => ADDUW
  | 1 => SH1ADDUW
  | 2 => SH2ADDUW
  | _ => SH3ADDUW

def num_of_bropw_zba (arg_ : bropw_zba) : Int :=
  match arg_ with
  | ADDUW => 0
  | SH1ADDUW => 1
  | SH2ADDUW => 2
  | SH3ADDUW => 3

def undefined_bropw_zbb (_ : Unit) : SailM bropw_zbb := do
  (internal_pick [ROLW, RORW])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def bropw_zbb_of_num (arg_ : Nat) : bropw_zbb :=
  match arg_ with
  | 0 => ROLW
  | _ => RORW

def num_of_bropw_zbb (arg_ : bropw_zbb) : Int :=
  match arg_ with
  | ROLW => 0
  | RORW => 1

def undefined_biop_zbs (_ : Unit) : SailM biop_zbs := do
  (internal_pick [BCLRI, BEXTI, BINVI, BSETI])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def biop_zbs_of_num (arg_ : Nat) : biop_zbs :=
  match arg_ with
  | 0 => BCLRI
  | 1 => BEXTI
  | 2 => BINVI
  | _ => BSETI

def num_of_biop_zbs (arg_ : biop_zbs) : Int :=
  match arg_ with
  | BCLRI => 0
  | BEXTI => 1
  | BINVI => 2
  | BSETI => 3

def undefined_extop_zbb (_ : Unit) : SailM extop_zbb := do
  (internal_pick [SEXTB, SEXTH, ZEXTH])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def extop_zbb_of_num (arg_ : Nat) : extop_zbb :=
  match arg_ with
  | 0 => SEXTB
  | 1 => SEXTH
  | _ => ZEXTH

def num_of_extop_zbb (arg_ : extop_zbb) : Int :=
  match arg_ with
  | SEXTB => 0
  | SEXTH => 1
  | ZEXTH => 2

def undefined_zicondop (_ : Unit) : SailM zicondop := do
  (internal_pick [CZERO_EQZ, CZERO_NEZ])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def zicondop_of_num (arg_ : Nat) : zicondop :=
  match arg_ with
  | 0 => CZERO_EQZ
  | _ => CZERO_NEZ

def num_of_zicondop (arg_ : zicondop) : Int :=
  match arg_ with
  | CZERO_EQZ => 0
  | CZERO_NEZ => 1

def size_enc_forwards (arg_ : word_width) : (BitVec 2) :=
  match arg_ with
  | BYTE => (0b00 : (BitVec 2))
  | HALF => (0b01 : (BitVec 2))
  | WORD => (0b10 : (BitVec 2))
  | DOUBLE => (0b11 : (BitVec 2))

def size_enc_backwards (arg_ : (BitVec 2)) : word_width :=
  match_bv arg_ with
  | 00 => BYTE
  | 01 => HALF
  | 10 => WORD
  | _ => DOUBLE

def size_enc_forwards_matches (arg_ : word_width) : Bool :=
  match arg_ with
  | BYTE => true
  | HALF => true
  | WORD => true
  | DOUBLE => true
  | _ => false

def size_enc_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match_bv arg_ with
  | 00 => true
  | 01 => true
  | 10 => true
  | 11 => true
  | _ => false

def size_mnemonic_backwards (arg_ : String) : SailM word_width := do
  match arg_ with
  | "b" => (pure BYTE)
  | "h" => (pure HALF)
  | "w" => (pure WORD)
  | "d" => (pure DOUBLE)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def size_mnemonic_forwards_matches (arg_ : word_width) : Bool :=
  match arg_ with
  | BYTE => true
  | HALF => true
  | WORD => true
  | DOUBLE => true
  | _ => false

def size_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "b" => true
  | "h" => true
  | "w" => true
  | "d" => true
  | _ => false

def size_bytes_forwards (arg_ : word_width) : Int :=
  match arg_ with
  | BYTE => 1
  | HALF => 2
  | WORD => 4
  | DOUBLE => 8

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {1, 2, 4, 8} -/
def size_bytes_backwards (arg_ : Nat) : word_width :=
  match arg_ with
  | 1 => BYTE
  | 2 => HALF
  | 4 => WORD
  | _ => DOUBLE

def size_bytes_forwards_matches (arg_ : word_width) : Bool :=
  match arg_ with
  | BYTE => true
  | HALF => true
  | WORD => true
  | DOUBLE => true
  | _ => false

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {1, 2, 4, 8} -/
def size_bytes_backwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | _ => false

def undefined_mul_op (_ : Unit) : SailM mul_op := do
  (pure { high := (← (undefined_bool ()))
          signed_rs1 := (← (undefined_bool ()))
          signed_rs2 := (← (undefined_bool ())) })

