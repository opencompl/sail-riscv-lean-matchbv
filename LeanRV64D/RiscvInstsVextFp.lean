import LeanRV64D.RiscvInstsVextArith

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

def encdec_fvvfunct6_forwards (arg_ : fvvfunct6) : (BitVec 6) :=
  match arg_ with
  | FVV_VADD => (0b000000 : (BitVec 6))
  | FVV_VSUB => (0b000010 : (BitVec 6))
  | FVV_VMIN => (0b000100 : (BitVec 6))
  | FVV_VMAX => (0b000110 : (BitVec 6))
  | FVV_VSGNJ => (0b001000 : (BitVec 6))
  | FVV_VSGNJN => (0b001001 : (BitVec 6))
  | FVV_VSGNJX => (0b001010 : (BitVec 6))
  | FVV_VDIV => (0b100000 : (BitVec 6))
  | FVV_VMUL => (0b100100 : (BitVec 6))

def encdec_fvvfunct6_backwards (arg_ : (BitVec 6)) : SailM fvvfunct6 := do
  match_bv arg_ with
  | 000000 => do (pure FVV_VADD)
  | 000010 => do (pure FVV_VSUB)
  | 000100 => do (pure FVV_VMIN)
  | 000110 => do (pure FVV_VMAX)
  | 001000 => do (pure FVV_VSGNJ)
  | 001001 => do (pure FVV_VSGNJN)
  | 001010 => do (pure FVV_VSGNJX)
  | 100000 => do (pure FVV_VDIV)
  | 100100 => do (pure FVV_VMUL)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_fvvfunct6_forwards_matches (arg_ : fvvfunct6) : Bool :=
  match arg_ with
  | FVV_VADD => true
  | FVV_VSUB => true
  | FVV_VMIN => true
  | FVV_VMAX => true
  | FVV_VSGNJ => true
  | FVV_VSGNJN => true
  | FVV_VSGNJX => true
  | FVV_VDIV => true
  | FVV_VMUL => true
  | _ => false

def encdec_fvvfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match_bv arg_ with
  | 000000 => true
  | 000010 => true
  | 000100 => true
  | 000110 => true
  | 001000 => true
  | 001001 => true
  | 001010 => true
  | 100000 => true
  | 100100 => true
  | _ => false

def fvvtype_mnemonic_backwards (arg_ : String) : SailM fvvfunct6 := do
  match arg_ with
  | "vfadd.vv" => (pure FVV_VADD)
  | "vfsub.vv" => (pure FVV_VSUB)
  | "vfmin.vv" => (pure FVV_VMIN)
  | "vfmax.vv" => (pure FVV_VMAX)
  | "vfsgnj.vv" => (pure FVV_VSGNJ)
  | "vfsgnjn.vv" => (pure FVV_VSGNJN)
  | "vfsgnjx.vv" => (pure FVV_VSGNJX)
  | "vfdiv.vv" => (pure FVV_VDIV)
  | "vfmul.vv" => (pure FVV_VMUL)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def fvvtype_mnemonic_forwards_matches (arg_ : fvvfunct6) : Bool :=
  match arg_ with
  | FVV_VADD => true
  | FVV_VSUB => true
  | FVV_VMIN => true
  | FVV_VMAX => true
  | FVV_VSGNJ => true
  | FVV_VSGNJN => true
  | FVV_VSGNJX => true
  | FVV_VDIV => true
  | FVV_VMUL => true
  | _ => false

def fvvtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vfadd.vv" => true
  | "vfsub.vv" => true
  | "vfmin.vv" => true
  | "vfmax.vv" => true
  | "vfsgnj.vv" => true
  | "vfsgnjn.vv" => true
  | "vfsgnjx.vv" => true
  | "vfdiv.vv" => true
  | "vfmul.vv" => true
  | _ => false

def encdec_fvvmafunct6_forwards (arg_ : fvvmafunct6) : (BitVec 6) :=
  match arg_ with
  | FVV_VMADD => (0b101000 : (BitVec 6))
  | FVV_VNMADD => (0b101001 : (BitVec 6))
  | FVV_VMSUB => (0b101010 : (BitVec 6))
  | FVV_VNMSUB => (0b101011 : (BitVec 6))
  | FVV_VMACC => (0b101100 : (BitVec 6))
  | FVV_VNMACC => (0b101101 : (BitVec 6))
  | FVV_VMSAC => (0b101110 : (BitVec 6))
  | FVV_VNMSAC => (0b101111 : (BitVec 6))

def encdec_fvvmafunct6_backwards (arg_ : (BitVec 6)) : SailM fvvmafunct6 := do
  match_bv arg_ with
  | 101000 => do (pure FVV_VMADD)
  | 101001 => do (pure FVV_VNMADD)
  | 101010 => do (pure FVV_VMSUB)
  | 101011 => do (pure FVV_VNMSUB)
  | 101100 => do (pure FVV_VMACC)
  | 101101 => do (pure FVV_VNMACC)
  | 101110 => do (pure FVV_VMSAC)
  | 101111 => do (pure FVV_VNMSAC)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_fvvmafunct6_forwards_matches (arg_ : fvvmafunct6) : Bool :=
  match arg_ with
  | FVV_VMADD => true
  | FVV_VNMADD => true
  | FVV_VMSUB => true
  | FVV_VNMSUB => true
  | FVV_VMACC => true
  | FVV_VNMACC => true
  | FVV_VMSAC => true
  | FVV_VNMSAC => true
  | _ => false

def encdec_fvvmafunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match_bv arg_ with
  | 101000 => true
  | 101001 => true
  | 101010 => true
  | 101011 => true
  | 101100 => true
  | 101101 => true
  | 101110 => true
  | 101111 => true
  | _ => false

def fvvmatype_mnemonic_backwards (arg_ : String) : SailM fvvmafunct6 := do
  match arg_ with
  | "vfmadd.vv" => (pure FVV_VMADD)
  | "vfnmadd.vv" => (pure FVV_VNMADD)
  | "vfmsub.vv" => (pure FVV_VMSUB)
  | "vfnmsub.vv" => (pure FVV_VNMSUB)
  | "vfmacc.vv" => (pure FVV_VMACC)
  | "vfnmacc.vv" => (pure FVV_VNMACC)
  | "vfmsac.vv" => (pure FVV_VMSAC)
  | "vfnmsac.vv" => (pure FVV_VNMSAC)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def fvvmatype_mnemonic_forwards_matches (arg_ : fvvmafunct6) : Bool :=
  match arg_ with
  | FVV_VMADD => true
  | FVV_VNMADD => true
  | FVV_VMSUB => true
  | FVV_VNMSUB => true
  | FVV_VMACC => true
  | FVV_VNMACC => true
  | FVV_VMSAC => true
  | FVV_VNMSAC => true
  | _ => false

def fvvmatype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vfmadd.vv" => true
  | "vfnmadd.vv" => true
  | "vfmsub.vv" => true
  | "vfnmsub.vv" => true
  | "vfmacc.vv" => true
  | "vfnmacc.vv" => true
  | "vfmsac.vv" => true
  | "vfnmsac.vv" => true
  | _ => false

def encdec_fwvvfunct6_forwards (arg_ : fwvvfunct6) : (BitVec 6) :=
  match arg_ with
  | FWVV_VADD => (0b110000 : (BitVec 6))
  | FWVV_VSUB => (0b110010 : (BitVec 6))
  | FWVV_VMUL => (0b111000 : (BitVec 6))

def encdec_fwvvfunct6_backwards (arg_ : (BitVec 6)) : SailM fwvvfunct6 := do
  match_bv arg_ with
  | 110000 => do (pure FWVV_VADD)
  | 110010 => do (pure FWVV_VSUB)
  | 111000 => do (pure FWVV_VMUL)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_fwvvfunct6_forwards_matches (arg_ : fwvvfunct6) : Bool :=
  match arg_ with
  | FWVV_VADD => true
  | FWVV_VSUB => true
  | FWVV_VMUL => true
  | _ => false

def encdec_fwvvfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match_bv arg_ with
  | 110000 => true
  | 110010 => true
  | 111000 => true
  | _ => false

def fwvvtype_mnemonic_backwards (arg_ : String) : SailM fwvvfunct6 := do
  match arg_ with
  | "vfwadd.vv" => (pure FWVV_VADD)
  | "vfwsub.vv" => (pure FWVV_VSUB)
  | "vfwmul.vv" => (pure FWVV_VMUL)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def fwvvtype_mnemonic_forwards_matches (arg_ : fwvvfunct6) : Bool :=
  match arg_ with
  | FWVV_VADD => true
  | FWVV_VSUB => true
  | FWVV_VMUL => true
  | _ => false

def fwvvtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vfwadd.vv" => true
  | "vfwsub.vv" => true
  | "vfwmul.vv" => true
  | _ => false

def encdec_fwvvmafunct6_forwards (arg_ : fwvvmafunct6) : (BitVec 6) :=
  match arg_ with
  | FWVV_VMACC => (0b111100 : (BitVec 6))
  | FWVV_VNMACC => (0b111101 : (BitVec 6))
  | FWVV_VMSAC => (0b111110 : (BitVec 6))
  | FWVV_VNMSAC => (0b111111 : (BitVec 6))

def encdec_fwvvmafunct6_backwards (arg_ : (BitVec 6)) : SailM fwvvmafunct6 := do
  match_bv arg_ with
  | 111100 => do (pure FWVV_VMACC)
  | 111101 => do (pure FWVV_VNMACC)
  | 111110 => do (pure FWVV_VMSAC)
  | 111111 => do (pure FWVV_VNMSAC)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_fwvvmafunct6_forwards_matches (arg_ : fwvvmafunct6) : Bool :=
  match arg_ with
  | FWVV_VMACC => true
  | FWVV_VNMACC => true
  | FWVV_VMSAC => true
  | FWVV_VNMSAC => true
  | _ => false

def encdec_fwvvmafunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match_bv arg_ with
  | 111100 => true
  | 111101 => true
  | 111110 => true
  | 111111 => true
  | _ => false

def fwvvmatype_mnemonic_backwards (arg_ : String) : SailM fwvvmafunct6 := do
  match arg_ with
  | "vfwmacc.vv" => (pure FWVV_VMACC)
  | "vfwnmacc.vv" => (pure FWVV_VNMACC)
  | "vfwmsac.vv" => (pure FWVV_VMSAC)
  | "vfwnmsac.vv" => (pure FWVV_VNMSAC)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def fwvvmatype_mnemonic_forwards_matches (arg_ : fwvvmafunct6) : Bool :=
  match arg_ with
  | FWVV_VMACC => true
  | FWVV_VNMACC => true
  | FWVV_VMSAC => true
  | FWVV_VNMSAC => true
  | _ => false

def fwvvmatype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vfwmacc.vv" => true
  | "vfwnmacc.vv" => true
  | "vfwmsac.vv" => true
  | "vfwnmsac.vv" => true
  | _ => false

def encdec_fwvfunct6_forwards (arg_ : fwvfunct6) : (BitVec 6) :=
  match arg_ with
  | FWV_VADD => (0b110100 : (BitVec 6))
  | FWV_VSUB => (0b110110 : (BitVec 6))

def encdec_fwvfunct6_backwards (arg_ : (BitVec 6)) : SailM fwvfunct6 := do
  match_bv arg_ with
  | 110100 => do (pure FWV_VADD)
  | 110110 => do (pure FWV_VSUB)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_fwvfunct6_forwards_matches (arg_ : fwvfunct6) : Bool :=
  match arg_ with
  | FWV_VADD => true
  | FWV_VSUB => true
  | _ => false

def encdec_fwvfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match_bv arg_ with
  | 110100 => true
  | 110110 => true
  | _ => false

def fwvtype_mnemonic_backwards (arg_ : String) : SailM fwvfunct6 := do
  match arg_ with
  | "vfwadd.wv" => (pure FWV_VADD)
  | "vfwsub.wv" => (pure FWV_VSUB)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def fwvtype_mnemonic_forwards_matches (arg_ : fwvfunct6) : Bool :=
  match arg_ with
  | FWV_VADD => true
  | FWV_VSUB => true
  | _ => false

def fwvtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vfwadd.wv" => true
  | "vfwsub.wv" => true
  | _ => false

def encdec_vfunary0_vs1_forwards (arg_ : vfunary0) : (BitVec 5) :=
  match arg_ with
  | FV_CVT_XU_F => (0b00000 : (BitVec 5))
  | FV_CVT_X_F => (0b00001 : (BitVec 5))
  | FV_CVT_F_XU => (0b00010 : (BitVec 5))
  | FV_CVT_F_X => (0b00011 : (BitVec 5))
  | FV_CVT_RTZ_XU_F => (0b00110 : (BitVec 5))
  | FV_CVT_RTZ_X_F => (0b00111 : (BitVec 5))

def encdec_vfunary0_vs1_backwards (arg_ : (BitVec 5)) : SailM vfunary0 := do
  match_bv arg_ with
  | 00000 => do (pure FV_CVT_XU_F)
  | 00001 => do (pure FV_CVT_X_F)
  | 00010 => do (pure FV_CVT_F_XU)
  | 00011 => do (pure FV_CVT_F_X)
  | 00110 => do (pure FV_CVT_RTZ_XU_F)
  | 00111 => do (pure FV_CVT_RTZ_X_F)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_vfunary0_vs1_forwards_matches (arg_ : vfunary0) : Bool :=
  match arg_ with
  | FV_CVT_XU_F => true
  | FV_CVT_X_F => true
  | FV_CVT_F_XU => true
  | FV_CVT_F_X => true
  | FV_CVT_RTZ_XU_F => true
  | FV_CVT_RTZ_X_F => true
  | _ => false

def encdec_vfunary0_vs1_backwards_matches (arg_ : (BitVec 5)) : Bool :=
  match_bv arg_ with
  | 00000 => true
  | 00001 => true
  | 00010 => true
  | 00011 => true
  | 00110 => true
  | 00111 => true
  | _ => false

def vfunary0_mnemonic_backwards (arg_ : String) : SailM vfunary0 := do
  match arg_ with
  | "vfcvt.xu.f.v" => (pure FV_CVT_XU_F)
  | "vfcvt.x.f.v" => (pure FV_CVT_X_F)
  | "vfcvt.f.xu.v" => (pure FV_CVT_F_XU)
  | "vfcvt.f.x.v" => (pure FV_CVT_F_X)
  | "vfcvt.rtz.xu.f.v" => (pure FV_CVT_RTZ_XU_F)
  | "vfcvt.rtz.x.f.v" => (pure FV_CVT_RTZ_X_F)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def vfunary0_mnemonic_forwards_matches (arg_ : vfunary0) : Bool :=
  match arg_ with
  | FV_CVT_XU_F => true
  | FV_CVT_X_F => true
  | FV_CVT_F_XU => true
  | FV_CVT_F_X => true
  | FV_CVT_RTZ_XU_F => true
  | FV_CVT_RTZ_X_F => true
  | _ => false

def vfunary0_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vfcvt.xu.f.v" => true
  | "vfcvt.x.f.v" => true
  | "vfcvt.f.xu.v" => true
  | "vfcvt.f.x.v" => true
  | "vfcvt.rtz.xu.f.v" => true
  | "vfcvt.rtz.x.f.v" => true
  | _ => false

def encdec_vfwunary0_vs1_forwards (arg_ : vfwunary0) : (BitVec 5) :=
  match arg_ with
  | FWV_CVT_XU_F => (0b01000 : (BitVec 5))
  | FWV_CVT_X_F => (0b01001 : (BitVec 5))
  | FWV_CVT_F_XU => (0b01010 : (BitVec 5))
  | FWV_CVT_F_X => (0b01011 : (BitVec 5))
  | FWV_CVT_F_F => (0b01100 : (BitVec 5))
  | FWV_CVT_RTZ_XU_F => (0b01110 : (BitVec 5))
  | FWV_CVT_RTZ_X_F => (0b01111 : (BitVec 5))

def encdec_vfwunary0_vs1_backwards (arg_ : (BitVec 5)) : SailM vfwunary0 := do
  match_bv arg_ with
  | 01000 => do (pure FWV_CVT_XU_F)
  | 01001 => do (pure FWV_CVT_X_F)
  | 01010 => do (pure FWV_CVT_F_XU)
  | 01011 => do (pure FWV_CVT_F_X)
  | 01100 => do (pure FWV_CVT_F_F)
  | 01110 => do (pure FWV_CVT_RTZ_XU_F)
  | 01111 => do (pure FWV_CVT_RTZ_X_F)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_vfwunary0_vs1_forwards_matches (arg_ : vfwunary0) : Bool :=
  match arg_ with
  | FWV_CVT_XU_F => true
  | FWV_CVT_X_F => true
  | FWV_CVT_F_XU => true
  | FWV_CVT_F_X => true
  | FWV_CVT_F_F => true
  | FWV_CVT_RTZ_XU_F => true
  | FWV_CVT_RTZ_X_F => true
  | _ => false

def encdec_vfwunary0_vs1_backwards_matches (arg_ : (BitVec 5)) : Bool :=
  match_bv arg_ with
  | 01000 => true
  | 01001 => true
  | 01010 => true
  | 01011 => true
  | 01100 => true
  | 01110 => true
  | 01111 => true
  | _ => false

def vfwunary0_mnemonic_backwards (arg_ : String) : SailM vfwunary0 := do
  match arg_ with
  | "vfwcvt.xu.f.v" => (pure FWV_CVT_XU_F)
  | "vfwcvt.x.f.v" => (pure FWV_CVT_X_F)
  | "vfwcvt.f.xu.v" => (pure FWV_CVT_F_XU)
  | "vfwcvt.f.x.v" => (pure FWV_CVT_F_X)
  | "vfwcvt.f.f.v" => (pure FWV_CVT_F_F)
  | "vfwcvt.rtz.xu.f.v" => (pure FWV_CVT_RTZ_XU_F)
  | "vfwcvt.rtz.x.f.v" => (pure FWV_CVT_RTZ_X_F)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def vfwunary0_mnemonic_forwards_matches (arg_ : vfwunary0) : Bool :=
  match arg_ with
  | FWV_CVT_XU_F => true
  | FWV_CVT_X_F => true
  | FWV_CVT_F_XU => true
  | FWV_CVT_F_X => true
  | FWV_CVT_F_F => true
  | FWV_CVT_RTZ_XU_F => true
  | FWV_CVT_RTZ_X_F => true
  | _ => false

def vfwunary0_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vfwcvt.xu.f.v" => true
  | "vfwcvt.x.f.v" => true
  | "vfwcvt.f.xu.v" => true
  | "vfwcvt.f.x.v" => true
  | "vfwcvt.f.f.v" => true
  | "vfwcvt.rtz.xu.f.v" => true
  | "vfwcvt.rtz.x.f.v" => true
  | _ => false

def encdec_vfnunary0_vs1_forwards (arg_ : vfnunary0) : (BitVec 5) :=
  match arg_ with
  | FNV_CVT_XU_F => (0b10000 : (BitVec 5))
  | FNV_CVT_X_F => (0b10001 : (BitVec 5))
  | FNV_CVT_F_XU => (0b10010 : (BitVec 5))
  | FNV_CVT_F_X => (0b10011 : (BitVec 5))
  | FNV_CVT_F_F => (0b10100 : (BitVec 5))
  | FNV_CVT_ROD_F_F => (0b10101 : (BitVec 5))
  | FNV_CVT_RTZ_XU_F => (0b10110 : (BitVec 5))
  | FNV_CVT_RTZ_X_F => (0b10111 : (BitVec 5))

def encdec_vfnunary0_vs1_backwards (arg_ : (BitVec 5)) : SailM vfnunary0 := do
  match_bv arg_ with
  | 10000 => do (pure FNV_CVT_XU_F)
  | 10001 => do (pure FNV_CVT_X_F)
  | 10010 => do (pure FNV_CVT_F_XU)
  | 10011 => do (pure FNV_CVT_F_X)
  | 10100 => do (pure FNV_CVT_F_F)
  | 10101 => do (pure FNV_CVT_ROD_F_F)
  | 10110 => do (pure FNV_CVT_RTZ_XU_F)
  | 10111 => do (pure FNV_CVT_RTZ_X_F)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_vfnunary0_vs1_forwards_matches (arg_ : vfnunary0) : Bool :=
  match arg_ with
  | FNV_CVT_XU_F => true
  | FNV_CVT_X_F => true
  | FNV_CVT_F_XU => true
  | FNV_CVT_F_X => true
  | FNV_CVT_F_F => true
  | FNV_CVT_ROD_F_F => true
  | FNV_CVT_RTZ_XU_F => true
  | FNV_CVT_RTZ_X_F => true
  | _ => false

def encdec_vfnunary0_vs1_backwards_matches (arg_ : (BitVec 5)) : Bool :=
  match_bv arg_ with
  | 10000 => true
  | 10001 => true
  | 10010 => true
  | 10011 => true
  | 10100 => true
  | 10101 => true
  | 10110 => true
  | 10111 => true
  | _ => false

def vfnunary0_mnemonic_backwards (arg_ : String) : SailM vfnunary0 := do
  match arg_ with
  | "vfncvt.xu.f.w" => (pure FNV_CVT_XU_F)
  | "vfncvt.x.f.w" => (pure FNV_CVT_X_F)
  | "vfncvt.f.xu.w" => (pure FNV_CVT_F_XU)
  | "vfncvt.f.x.w" => (pure FNV_CVT_F_X)
  | "vfncvt.f.f.w" => (pure FNV_CVT_F_F)
  | "vfncvt.rod.f.f.w" => (pure FNV_CVT_ROD_F_F)
  | "vfncvt.rtz.xu.f.w" => (pure FNV_CVT_RTZ_XU_F)
  | "vfncvt.rtz.x.f.w" => (pure FNV_CVT_RTZ_X_F)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def vfnunary0_mnemonic_forwards_matches (arg_ : vfnunary0) : Bool :=
  match arg_ with
  | FNV_CVT_XU_F => true
  | FNV_CVT_X_F => true
  | FNV_CVT_F_XU => true
  | FNV_CVT_F_X => true
  | FNV_CVT_F_F => true
  | FNV_CVT_ROD_F_F => true
  | FNV_CVT_RTZ_XU_F => true
  | FNV_CVT_RTZ_X_F => true
  | _ => false

def vfnunary0_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vfncvt.xu.f.w" => true
  | "vfncvt.x.f.w" => true
  | "vfncvt.f.xu.w" => true
  | "vfncvt.f.x.w" => true
  | "vfncvt.f.f.w" => true
  | "vfncvt.rod.f.f.w" => true
  | "vfncvt.rtz.xu.f.w" => true
  | "vfncvt.rtz.x.f.w" => true
  | _ => false

def encdec_vfunary1_vs1_forwards (arg_ : vfunary1) : (BitVec 5) :=
  match arg_ with
  | FVV_VSQRT => (0b00000 : (BitVec 5))
  | FVV_VRSQRT7 => (0b00100 : (BitVec 5))
  | FVV_VREC7 => (0b00101 : (BitVec 5))
  | FVV_VCLASS => (0b10000 : (BitVec 5))

def encdec_vfunary1_vs1_backwards (arg_ : (BitVec 5)) : SailM vfunary1 := do
  match_bv arg_ with
  | 00000 => do (pure FVV_VSQRT)
  | 00100 => do (pure FVV_VRSQRT7)
  | 00101 => do (pure FVV_VREC7)
  | 10000 => do (pure FVV_VCLASS)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_vfunary1_vs1_forwards_matches (arg_ : vfunary1) : Bool :=
  match arg_ with
  | FVV_VSQRT => true
  | FVV_VRSQRT7 => true
  | FVV_VREC7 => true
  | FVV_VCLASS => true
  | _ => false

def encdec_vfunary1_vs1_backwards_matches (arg_ : (BitVec 5)) : Bool :=
  match_bv arg_ with
  | 00000 => true
  | 00100 => true
  | 00101 => true
  | 10000 => true
  | _ => false

def vfunary1_mnemonic_backwards (arg_ : String) : SailM vfunary1 := do
  match arg_ with
  | "vfsqrt.v" => (pure FVV_VSQRT)
  | "vfrsqrt7.v" => (pure FVV_VRSQRT7)
  | "vfrec7.v" => (pure FVV_VREC7)
  | "vfclass.v" => (pure FVV_VCLASS)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def vfunary1_mnemonic_forwards_matches (arg_ : vfunary1) : Bool :=
  match arg_ with
  | FVV_VSQRT => true
  | FVV_VRSQRT7 => true
  | FVV_VREC7 => true
  | FVV_VCLASS => true
  | _ => false

def vfunary1_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vfsqrt.v" => true
  | "vfrsqrt7.v" => true
  | "vfrec7.v" => true
  | "vfclass.v" => true
  | _ => false

def encdec_fvffunct6_forwards (arg_ : fvffunct6) : (BitVec 6) :=
  match arg_ with
  | VF_VADD => (0b000000 : (BitVec 6))
  | VF_VSUB => (0b000010 : (BitVec 6))
  | VF_VMIN => (0b000100 : (BitVec 6))
  | VF_VMAX => (0b000110 : (BitVec 6))
  | VF_VSGNJ => (0b001000 : (BitVec 6))
  | VF_VSGNJN => (0b001001 : (BitVec 6))
  | VF_VSGNJX => (0b001010 : (BitVec 6))
  | VF_VSLIDE1UP => (0b001110 : (BitVec 6))
  | VF_VSLIDE1DOWN => (0b001111 : (BitVec 6))
  | VF_VDIV => (0b100000 : (BitVec 6))
  | VF_VRDIV => (0b100001 : (BitVec 6))
  | VF_VMUL => (0b100100 : (BitVec 6))
  | VF_VRSUB => (0b100111 : (BitVec 6))

def encdec_fvffunct6_backwards (arg_ : (BitVec 6)) : SailM fvffunct6 := do
  match_bv arg_ with
  | 000000 => do (pure VF_VADD)
  | 000010 => do (pure VF_VSUB)
  | 000100 => do (pure VF_VMIN)
  | 000110 => do (pure VF_VMAX)
  | 001000 => do (pure VF_VSGNJ)
  | 001001 => do (pure VF_VSGNJN)
  | 001010 => do (pure VF_VSGNJX)
  | 001110 => do (pure VF_VSLIDE1UP)
  | 001111 => do (pure VF_VSLIDE1DOWN)
  | 100000 => do (pure VF_VDIV)
  | 100001 => do (pure VF_VRDIV)
  | 100100 => do (pure VF_VMUL)
  | 100111 => do (pure VF_VRSUB)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_fvffunct6_forwards_matches (arg_ : fvffunct6) : Bool :=
  match arg_ with
  | VF_VADD => true
  | VF_VSUB => true
  | VF_VMIN => true
  | VF_VMAX => true
  | VF_VSGNJ => true
  | VF_VSGNJN => true
  | VF_VSGNJX => true
  | VF_VSLIDE1UP => true
  | VF_VSLIDE1DOWN => true
  | VF_VDIV => true
  | VF_VRDIV => true
  | VF_VMUL => true
  | VF_VRSUB => true
  | _ => false

def encdec_fvffunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match_bv arg_ with
  | 000000 => true
  | 000010 => true
  | 000100 => true
  | 000110 => true
  | 001000 => true
  | 001001 => true
  | 001010 => true
  | 001110 => true
  | 001111 => true
  | 100000 => true
  | 100001 => true
  | 100100 => true
  | 100111 => true
  | _ => false

def fvftype_mnemonic_backwards (arg_ : String) : SailM fvffunct6 := do
  match arg_ with
  | "vfadd.vf" => (pure VF_VADD)
  | "vfsub.vf" => (pure VF_VSUB)
  | "vfmin.vf" => (pure VF_VMIN)
  | "vfmax.vf" => (pure VF_VMAX)
  | "vfsgnj.vf" => (pure VF_VSGNJ)
  | "vfsgnjn.vf" => (pure VF_VSGNJN)
  | "vfsgnjx.vf" => (pure VF_VSGNJX)
  | "vfslide1up.vf" => (pure VF_VSLIDE1UP)
  | "vfslide1down.vf" => (pure VF_VSLIDE1DOWN)
  | "vfdiv.vf" => (pure VF_VDIV)
  | "vfrdiv.vf" => (pure VF_VRDIV)
  | "vfmul.vf" => (pure VF_VMUL)
  | "vfrsub.vf" => (pure VF_VRSUB)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def fvftype_mnemonic_forwards_matches (arg_ : fvffunct6) : Bool :=
  match arg_ with
  | VF_VADD => true
  | VF_VSUB => true
  | VF_VMIN => true
  | VF_VMAX => true
  | VF_VSGNJ => true
  | VF_VSGNJN => true
  | VF_VSGNJX => true
  | VF_VSLIDE1UP => true
  | VF_VSLIDE1DOWN => true
  | VF_VDIV => true
  | VF_VRDIV => true
  | VF_VMUL => true
  | VF_VRSUB => true
  | _ => false

def fvftype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vfadd.vf" => true
  | "vfsub.vf" => true
  | "vfmin.vf" => true
  | "vfmax.vf" => true
  | "vfsgnj.vf" => true
  | "vfsgnjn.vf" => true
  | "vfsgnjx.vf" => true
  | "vfslide1up.vf" => true
  | "vfslide1down.vf" => true
  | "vfdiv.vf" => true
  | "vfrdiv.vf" => true
  | "vfmul.vf" => true
  | "vfrsub.vf" => true
  | _ => false

def encdec_fvfmafunct6_forwards (arg_ : fvfmafunct6) : (BitVec 6) :=
  match arg_ with
  | VF_VMADD => (0b101000 : (BitVec 6))
  | VF_VNMADD => (0b101001 : (BitVec 6))
  | VF_VMSUB => (0b101010 : (BitVec 6))
  | VF_VNMSUB => (0b101011 : (BitVec 6))
  | VF_VMACC => (0b101100 : (BitVec 6))
  | VF_VNMACC => (0b101101 : (BitVec 6))
  | VF_VMSAC => (0b101110 : (BitVec 6))
  | VF_VNMSAC => (0b101111 : (BitVec 6))

def encdec_fvfmafunct6_backwards (arg_ : (BitVec 6)) : SailM fvfmafunct6 := do
  match_bv arg_ with
  | 101000 => do (pure VF_VMADD)
  | 101001 => do (pure VF_VNMADD)
  | 101010 => do (pure VF_VMSUB)
  | 101011 => do (pure VF_VNMSUB)
  | 101100 => do (pure VF_VMACC)
  | 101101 => do (pure VF_VNMACC)
  | 101110 => do (pure VF_VMSAC)
  | 101111 => do (pure VF_VNMSAC)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_fvfmafunct6_forwards_matches (arg_ : fvfmafunct6) : Bool :=
  match arg_ with
  | VF_VMADD => true
  | VF_VNMADD => true
  | VF_VMSUB => true
  | VF_VNMSUB => true
  | VF_VMACC => true
  | VF_VNMACC => true
  | VF_VMSAC => true
  | VF_VNMSAC => true
  | _ => false

def encdec_fvfmafunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match_bv arg_ with
  | 101000 => true
  | 101001 => true
  | 101010 => true
  | 101011 => true
  | 101100 => true
  | 101101 => true
  | 101110 => true
  | 101111 => true
  | _ => false

def fvfmatype_mnemonic_backwards (arg_ : String) : SailM fvfmafunct6 := do
  match arg_ with
  | "vfmadd.vf" => (pure VF_VMADD)
  | "vfnmadd.vf" => (pure VF_VNMADD)
  | "vfmsub.vf" => (pure VF_VMSUB)
  | "vfnmsub.vf" => (pure VF_VNMSUB)
  | "vfmacc.vf" => (pure VF_VMACC)
  | "vfnmacc.vf" => (pure VF_VNMACC)
  | "vfmsac.vf" => (pure VF_VMSAC)
  | "vfnmsac.vf" => (pure VF_VNMSAC)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def fvfmatype_mnemonic_forwards_matches (arg_ : fvfmafunct6) : Bool :=
  match arg_ with
  | VF_VMADD => true
  | VF_VNMADD => true
  | VF_VMSUB => true
  | VF_VNMSUB => true
  | VF_VMACC => true
  | VF_VNMACC => true
  | VF_VMSAC => true
  | VF_VNMSAC => true
  | _ => false

def fvfmatype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vfmadd.vf" => true
  | "vfnmadd.vf" => true
  | "vfmsub.vf" => true
  | "vfnmsub.vf" => true
  | "vfmacc.vf" => true
  | "vfnmacc.vf" => true
  | "vfmsac.vf" => true
  | "vfnmsac.vf" => true
  | _ => false

def encdec_fwvffunct6_forwards (arg_ : fwvffunct6) : (BitVec 6) :=
  match arg_ with
  | FWVF_VADD => (0b110000 : (BitVec 6))
  | FWVF_VSUB => (0b110010 : (BitVec 6))
  | FWVF_VMUL => (0b111000 : (BitVec 6))

def encdec_fwvffunct6_backwards (arg_ : (BitVec 6)) : SailM fwvffunct6 := do
  match_bv arg_ with
  | 110000 => do (pure FWVF_VADD)
  | 110010 => do (pure FWVF_VSUB)
  | 111000 => do (pure FWVF_VMUL)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_fwvffunct6_forwards_matches (arg_ : fwvffunct6) : Bool :=
  match arg_ with
  | FWVF_VADD => true
  | FWVF_VSUB => true
  | FWVF_VMUL => true
  | _ => false

def encdec_fwvffunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match_bv arg_ with
  | 110000 => true
  | 110010 => true
  | 111000 => true
  | _ => false

def fwvftype_mnemonic_backwards (arg_ : String) : SailM fwvffunct6 := do
  match arg_ with
  | "vfwadd.vf" => (pure FWVF_VADD)
  | "vfwsub.vf" => (pure FWVF_VSUB)
  | "vfwmul.vf" => (pure FWVF_VMUL)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def fwvftype_mnemonic_forwards_matches (arg_ : fwvffunct6) : Bool :=
  match arg_ with
  | FWVF_VADD => true
  | FWVF_VSUB => true
  | FWVF_VMUL => true
  | _ => false

def fwvftype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vfwadd.vf" => true
  | "vfwsub.vf" => true
  | "vfwmul.vf" => true
  | _ => false

def encdec_fwvfmafunct6_forwards (arg_ : fwvfmafunct6) : (BitVec 6) :=
  match arg_ with
  | FWVF_VMACC => (0b111100 : (BitVec 6))
  | FWVF_VNMACC => (0b111101 : (BitVec 6))
  | FWVF_VMSAC => (0b111110 : (BitVec 6))
  | FWVF_VNMSAC => (0b111111 : (BitVec 6))

def encdec_fwvfmafunct6_backwards (arg_ : (BitVec 6)) : SailM fwvfmafunct6 := do
  match_bv arg_ with
  | 111100 => do (pure FWVF_VMACC)
  | 111101 => do (pure FWVF_VNMACC)
  | 111110 => do (pure FWVF_VMSAC)
  | 111111 => do (pure FWVF_VNMSAC)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_fwvfmafunct6_forwards_matches (arg_ : fwvfmafunct6) : Bool :=
  match arg_ with
  | FWVF_VMACC => true
  | FWVF_VNMACC => true
  | FWVF_VMSAC => true
  | FWVF_VNMSAC => true
  | _ => false

def encdec_fwvfmafunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match_bv arg_ with
  | 111100 => true
  | 111101 => true
  | 111110 => true
  | 111111 => true
  | _ => false

def fwvfmatype_mnemonic_backwards (arg_ : String) : SailM fwvfmafunct6 := do
  match arg_ with
  | "vfwmacc.vf" => (pure FWVF_VMACC)
  | "vfwnmacc.vf" => (pure FWVF_VNMACC)
  | "vfwmsac.vf" => (pure FWVF_VMSAC)
  | "vfwnmsac.vf" => (pure FWVF_VNMSAC)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def fwvfmatype_mnemonic_forwards_matches (arg_ : fwvfmafunct6) : Bool :=
  match arg_ with
  | FWVF_VMACC => true
  | FWVF_VNMACC => true
  | FWVF_VMSAC => true
  | FWVF_VNMSAC => true
  | _ => false

def fwvfmatype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vfwmacc.vf" => true
  | "vfwnmacc.vf" => true
  | "vfwmsac.vf" => true
  | "vfwnmsac.vf" => true
  | _ => false

def encdec_fwffunct6_forwards (arg_ : fwffunct6) : (BitVec 6) :=
  match arg_ with
  | FWF_VADD => (0b110100 : (BitVec 6))
  | FWF_VSUB => (0b110110 : (BitVec 6))

def encdec_fwffunct6_backwards (arg_ : (BitVec 6)) : SailM fwffunct6 := do
  match_bv arg_ with
  | 110100 => do (pure FWF_VADD)
  | 110110 => do (pure FWF_VSUB)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_fwffunct6_forwards_matches (arg_ : fwffunct6) : Bool :=
  match arg_ with
  | FWF_VADD => true
  | FWF_VSUB => true
  | _ => false

def encdec_fwffunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match_bv arg_ with
  | 110100 => true
  | 110110 => true
  | _ => false

def fwftype_mnemonic_backwards (arg_ : String) : SailM fwffunct6 := do
  match arg_ with
  | "vfwadd.wf" => (pure FWF_VADD)
  | "vfwsub.wf" => (pure FWF_VSUB)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def fwftype_mnemonic_forwards_matches (arg_ : fwffunct6) : Bool :=
  match arg_ with
  | FWF_VADD => true
  | FWF_VSUB => true
  | _ => false

def fwftype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vfwadd.wf" => true
  | "vfwsub.wf" => true
  | _ => false

