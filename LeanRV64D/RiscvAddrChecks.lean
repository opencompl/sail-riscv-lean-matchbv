import LeanRV64D.RiscvExtRegs

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

def ext_fetch_check_pc (start_pc : (BitVec (2 ^ 3 * 8))) (pc : (BitVec (2 ^ 3 * 8))) : (Ext_FetchAddr_Check Unit) :=
  (Ext_FetchAddr_OK (Virtaddr pc))

def ext_handle_fetch_check_error (err : Unit) : Unit :=
  ()

def ext_control_check_addr (pc : (BitVec (2 ^ 3 * 8))) : (Ext_ControlAddr_Check Unit) :=
  (Ext_ControlAddr_OK (Virtaddr pc))

def ext_control_check_pc (pc : (BitVec (2 ^ 3 * 8))) : (Ext_ControlAddr_Check Unit) :=
  (Ext_ControlAddr_OK (Virtaddr pc))

def ext_handle_control_check_error (err : Unit) : Unit :=
  ()

/-- Type quantifiers: width : Nat, 1 ≤ width ∧ width ≤ 4096 -/
def ext_data_get_addr (base : regidx) (offset : (BitVec (2 ^ 3 * 8))) (acc : (AccessType Unit)) (width : Nat) : SailM (Ext_DataAddr_Check Unit) := do
  let addr ← do (pure (Virtaddr ((← (rX_bits base)) + offset)))
  (pure (Ext_DataAddr_OK addr))

def ext_handle_data_check_error (err : Unit) : Unit :=
  ()

/-- Type quantifiers: k_ex281072# : Bool, k_ex281071# : Bool, k_ex281070# : Bool, k_ex281069# : Bool, size
  : Nat, 0 < size ∧ size ≤ max_mem_access -/
def ext_check_phys_mem_read (access_type : (AccessType Unit)) (paddr : physaddr) (size : Nat) (acquire : Bool) (release : Bool) (reserved : Bool) (read_meta : Bool) : Ext_PhysAddr_Check :=
  (Ext_PhysAddr_OK ())

/-- Type quantifiers: size : Nat, 0 < size ∧ size ≤ max_mem_access -/
def ext_check_phys_mem_write (write_kind : write_kind) (paddr : physaddr) (size : Nat) (data : (BitVec (8 * size))) (metadata : Unit) : Ext_PhysAddr_Check :=
  (Ext_PhysAddr_OK ())

