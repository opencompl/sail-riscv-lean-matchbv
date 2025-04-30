import LeanRV64D.Arithmetic

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
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
open Retire_Failure
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

def hartSupports_measure (ext : extension) : Int :=
  match ext with
  | Ext_C => 1
  | _ => 0

def hartSupports (merge_var : extension) : SailM Bool := do
  match merge_var with
  | Ext_M => (pure true)
  | Ext_A => (pure true)
  | Ext_F => (pure true)
  | Ext_D => (pure true)
  | Ext_B => (pure true)
  | Ext_V => (pure true)
  | Ext_S => (pure true)
  | Ext_U => (pure true)
  | Ext_Zicbom => (pure true)
  | Ext_Zicboz => (pure true)
  | Ext_Zicntr => (pure true)
  | Ext_Zicond => (pure true)
  | Ext_Zifencei => (pure true)
  | Ext_Zihpm => (pure true)
  | Ext_Zimop => (pure true)
  | Ext_Zmmul => (pure false)
  | Ext_Zaamo => (pure false)
  | Ext_Zabha => (pure true)
  | Ext_Zalrsc => (pure false)
  | Ext_Zfa => (pure true)
  | Ext_Zfh => (pure true)
  | Ext_Zfhmin => (pure false)
  | Ext_Zfinx => (pure false)
  | Ext_Zdinx => (pure false)
  | Ext_Zca => (pure true)
  | Ext_Zcb => (pure true)
  | Ext_Zcd => (pure true)
  | Ext_Zcf => (pure (Bool.and (true : Bool) (BEq.beq xlen 32)))
  | Ext_Zcmop => (pure true)
  | Ext_C => (pure (Bool.and (← (hartSupports Ext_Zca))
        (Bool.and
          (Bool.or (← (hartSupports Ext_Zcf))
            (Bool.or (not (← (hartSupports Ext_F))) (bne xlen 32)))
          (Bool.or (← (hartSupports Ext_Zcd)) (not (← (hartSupports Ext_D)))))))
  | Ext_Zba => (pure false)
  | Ext_Zbb => (pure false)
  | Ext_Zbc => (pure true)
  | Ext_Zbkb => (pure true)
  | Ext_Zbkc => (pure true)
  | Ext_Zbkx => (pure true)
  | Ext_Zbs => (pure false)
  | Ext_Zknd => (pure true)
  | Ext_Zkne => (pure true)
  | Ext_Zknh => (pure true)
  | Ext_Zkr => (pure true)
  | Ext_Zksed => (pure true)
  | Ext_Zksh => (pure true)
  | Ext_Zhinx => (pure false)
  | Ext_Zvbb => (pure true)
  | Ext_Zvkb => (pure false)
  | Ext_Zvbc => (pure true)
  | Ext_Zvknha => (pure true)
  | Ext_Zvknhb => (pure true)
  | Ext_Sscofpmf => (pure true)
  | Ext_Sstc => (pure true)
  | Ext_Svinval => (pure true)
  | Ext_Svnapot => (pure false)
  | Ext_Svpbmt => (pure false)
  | Ext_Sv32 => (pure (Bool.and (true : Bool) (BEq.beq xlen 32)))
  | Ext_Sv39 => (pure (Bool.and (true : Bool) (BEq.beq xlen 64)))
  | Ext_Sv48 => (pure (Bool.and (true : Bool) (BEq.beq xlen 64)))
  | Ext_Sv57 => (pure (Bool.and (true : Bool) (BEq.beq xlen 64)))
  | Ext_Smcntrpmf => (pure true)
  | _ => (do
      assert false "Pattern match failure at riscv_extensions.sail:217.0-217.83"
      throw Error.Exit)
termination_by let ext := merge_var; ((hartSupports_measure ext)).toNat

