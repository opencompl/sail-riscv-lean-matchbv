import LeanRV64D.RiscvInstsVextMem

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

def encdec_mmfunct6_forwards (arg_ : mmfunct6) : (BitVec 6) :=
  match arg_ with
  | MM_VMAND => (0b011001 : (BitVec 6))
  | MM_VMNAND => (0b011101 : (BitVec 6))
  | MM_VMANDN => (0b011000 : (BitVec 6))
  | MM_VMXOR => (0b011011 : (BitVec 6))
  | MM_VMOR => (0b011010 : (BitVec 6))
  | MM_VMNOR => (0b011110 : (BitVec 6))
  | MM_VMORN => (0b011100 : (BitVec 6))
  | MM_VMXNOR => (0b011111 : (BitVec 6))

def encdec_mmfunct6_backwards (arg_ : (BitVec 6)) : SailM mmfunct6 := do
  match_bv arg_ with
  | 011001 => do (pure MM_VMAND)
  | 011101 => do (pure MM_VMNAND)
  | 011000 => do (pure MM_VMANDN)
  | 011011 => do (pure MM_VMXOR)
  | 011010 => do (pure MM_VMOR)
  | 011110 => do (pure MM_VMNOR)
  | 011100 => do (pure MM_VMORN)
  | 011111 => do (pure MM_VMXNOR)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_mmfunct6_forwards_matches (arg_ : mmfunct6) : Bool :=
  match arg_ with
  | MM_VMAND => true
  | MM_VMNAND => true
  | MM_VMANDN => true
  | MM_VMXOR => true
  | MM_VMOR => true
  | MM_VMNOR => true
  | MM_VMORN => true
  | MM_VMXNOR => true
  | _ => false

def encdec_mmfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match_bv arg_ with
  | 011001 => true
  | 011101 => true
  | 011000 => true
  | 011011 => true
  | 011010 => true
  | 011110 => true
  | 011100 => true
  | 011111 => true
  | _ => false

def mmtype_mnemonic_backwards (arg_ : String) : SailM mmfunct6 := do
  match arg_ with
  | "vmand.mm" => (pure MM_VMAND)
  | "vmnand.mm" => (pure MM_VMNAND)
  | "vmandn.mm" => (pure MM_VMANDN)
  | "vmxor.mm" => (pure MM_VMXOR)
  | "vmor.mm" => (pure MM_VMOR)
  | "vmnor.mm" => (pure MM_VMNOR)
  | "vmorn.mm" => (pure MM_VMORN)
  | "vmxnor.mm" => (pure MM_VMXNOR)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def mmtype_mnemonic_forwards_matches (arg_ : mmfunct6) : Bool :=
  match arg_ with
  | MM_VMAND => true
  | MM_VMNAND => true
  | MM_VMANDN => true
  | MM_VMXOR => true
  | MM_VMOR => true
  | MM_VMNOR => true
  | MM_VMORN => true
  | MM_VMXNOR => true
  | _ => false

def mmtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vmand.mm" => true
  | "vmnand.mm" => true
  | "vmandn.mm" => true
  | "vmxor.mm" => true
  | "vmor.mm" => true
  | "vmnor.mm" => true
  | "vmorn.mm" => true
  | "vmxnor.mm" => true
  | _ => false

