import LeanRV64D.RiscvInstsEnd

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

def csr_name_map_forwards_matches (arg_ : (BitVec 12)) : Bool :=
  match_bv arg_ with
  | 001100000001 => true
  | 001100000000 => true
  | 001100001010 => true
  | 001100011010 => true
  | 000100001010 => true
  | 001100000100 => true
  | 001101000100 => true
  | 001100000010 => true
  | 001100010010 => true
  | 001100000011 => true
  | 001101000010 => true
  | 001101000011 => true
  | 001101000000 => true
  | 000100000110 => true
  | 001100000110 => true
  | 001100100000 => true
  | 111100010001 => true
  | 111100010010 => true
  | 111100010011 => true
  | 111100010100 => true
  | 111100010101 => true
  | 000100000000 => true
  | 000101000100 => true
  | 000100000100 => true
  | 000101000000 => true
  | 000101000010 => true
  | 000101000011 => true
  | 011110100000 => true
  | 011110100001 => true
  | 011110100010 => true
  | 011110100011 => true
  | 001110100000 => true
  | 001110100001 => true
  | 001110100010 => true
  | 001110100011 => true
  | 001110100100 => true
  | 001110100101 => true
  | 001110100110 => true
  | 001110100111 => true
  | 001110101000 => true
  | 001110101001 => true
  | 001110101010 => true
  | 001110101011 => true
  | 001110101100 => true
  | 001110101101 => true
  | 001110101110 => true
  | 001110101111 => true
  | 001110110000 => true
  | 001110110001 => true
  | 001110110010 => true
  | 001110110011 => true
  | 001110110100 => true
  | 001110110101 => true
  | 001110110110 => true
  | 001110110111 => true
  | 001110111000 => true
  | 001110111001 => true
  | 001110111010 => true
  | 001110111011 => true
  | 001110111100 => true
  | 001110111101 => true
  | 001110111110 => true
  | 001110111111 => true
  | 001111000000 => true
  | 001111000001 => true
  | 001111000010 => true
  | 001111000011 => true
  | 001111000100 => true
  | 001111000101 => true
  | 001111000110 => true
  | 001111000111 => true
  | 001111001000 => true
  | 001111001001 => true
  | 001111001010 => true
  | 001111001011 => true
  | 001111001100 => true
  | 001111001101 => true
  | 001111001110 => true
  | 001111001111 => true
  | 001111010000 => true
  | 001111010001 => true
  | 001111010010 => true
  | 001111010011 => true
  | 001111010100 => true
  | 001111010101 => true
  | 001111010110 => true
  | 001111010111 => true
  | 001111011000 => true
  | 001111011001 => true
  | 001111011010 => true
  | 001111011011 => true
  | 001111011100 => true
  | 001111011101 => true
  | 001111011110 => true
  | 001111011111 => true
  | 001111100000 => true
  | 001111100001 => true
  | 001111100010 => true
  | 001111100011 => true
  | 001111100100 => true
  | 001111100101 => true
  | 001111100110 => true
  | 001111100111 => true
  | 001111101000 => true
  | 001111101001 => true
  | 001111101010 => true
  | 001111101011 => true
  | 001111101100 => true
  | 001111101101 => true
  | 001111101110 => true
  | 001111101111 => true
  | 000000001000 => true
  | 000000001001 => true
  | 000000001010 => true
  | 000000001111 => true
  | 110000100000 => true
  | 110000100001 => true
  | 110000100010 => true
  | 000100000101 => true
  | 000101000001 => true
  | 001100000101 => true
  | 001101000001 => true
  | 110000000011 => true
  | 110000000100 => true
  | 110000000101 => true
  | 110000000110 => true
  | 110000000111 => true
  | 110000001000 => true
  | 110000001001 => true
  | 110000001010 => true
  | 110000001011 => true
  | 110000001100 => true
  | 110000001101 => true
  | 110000001110 => true
  | 110000001111 => true
  | 110000010000 => true
  | 110000010001 => true
  | 110000010010 => true
  | 110000010011 => true
  | 110000010100 => true
  | 110000010101 => true
  | 110000010110 => true
  | 110000010111 => true
  | 110000011000 => true
  | 110000011001 => true
  | 110000011010 => true
  | 110000011011 => true
  | 110000011100 => true
  | 110000011101 => true
  | 110000011110 => true
  | 110000011111 => true
  | 110010000011 => true
  | 110010000100 => true
  | 110010000101 => true
  | 110010000110 => true
  | 110010000111 => true
  | 110010001000 => true
  | 110010001001 => true
  | 110010001010 => true
  | 110010001011 => true
  | 110010001100 => true
  | 110010001101 => true
  | 110010001110 => true
  | 110010001111 => true
  | 110010010000 => true
  | 110010010001 => true
  | 110010010010 => true
  | 110010010011 => true
  | 110010010100 => true
  | 110010010101 => true
  | 110010010110 => true
  | 110010010111 => true
  | 110010011000 => true
  | 110010011001 => true
  | 110010011010 => true
  | 110010011011 => true
  | 110010011100 => true
  | 110010011101 => true
  | 110010011110 => true
  | 110010011111 => true
  | 001100100011 => true
  | 001100100100 => true
  | 001100100101 => true
  | 001100100110 => true
  | 001100100111 => true
  | 001100101000 => true
  | 001100101001 => true
  | 001100101010 => true
  | 001100101011 => true
  | 001100101100 => true
  | 001100101101 => true
  | 001100101110 => true
  | 001100101111 => true
  | 001100110000 => true
  | 001100110001 => true
  | 001100110010 => true
  | 001100110011 => true
  | 001100110100 => true
  | 001100110101 => true
  | 001100110110 => true
  | 001100110111 => true
  | 001100111000 => true
  | 001100111001 => true
  | 001100111010 => true
  | 001100111011 => true
  | 001100111100 => true
  | 001100111101 => true
  | 001100111110 => true
  | 001100111111 => true
  | 101100000011 => true
  | 101100000100 => true
  | 101100000101 => true
  | 101100000110 => true
  | 101100000111 => true
  | 101100001000 => true
  | 101100001001 => true
  | 101100001010 => true
  | 101100001011 => true
  | 101100001100 => true
  | 101100001101 => true
  | 101100001110 => true
  | 101100001111 => true
  | 101100010000 => true
  | 101100010001 => true
  | 101100010010 => true
  | 101100010011 => true
  | 101100010100 => true
  | 101100010101 => true
  | 101100010110 => true
  | 101100010111 => true
  | 101100011000 => true
  | 101100011001 => true
  | 101100011010 => true
  | 101100011011 => true
  | 101100011100 => true
  | 101100011101 => true
  | 101100011110 => true
  | 101100011111 => true
  | 101110000011 => true
  | 101110000100 => true
  | 101110000101 => true
  | 101110000110 => true
  | 101110000111 => true
  | 101110001000 => true
  | 101110001001 => true
  | 101110001010 => true
  | 101110001011 => true
  | 101110001100 => true
  | 101110001101 => true
  | 101110001110 => true
  | 101110001111 => true
  | 101110010000 => true
  | 101110010001 => true
  | 101110010010 => true
  | 101110010011 => true
  | 101110010100 => true
  | 101110010101 => true
  | 101110010110 => true
  | 101110010111 => true
  | 101110011000 => true
  | 101110011001 => true
  | 101110011010 => true
  | 101110011011 => true
  | 101110011100 => true
  | 101110011101 => true
  | 101110011110 => true
  | 101110011111 => true
  | 101110000011 => true
  | 101110000100 => true
  | 101110000101 => true
  | 101110000110 => true
  | 101110000111 => true
  | 101110001000 => true
  | 101110001001 => true
  | 101110001010 => true
  | 101110001011 => true
  | 101110001100 => true
  | 101110001101 => true
  | 101110001110 => true
  | 101110001111 => true
  | 101110010000 => true
  | 101110010001 => true
  | 101110010010 => true
  | 101110010011 => true
  | 101110010100 => true
  | 101110010101 => true
  | 101110010110 => true
  | 101110010111 => true
  | 101110011000 => true
  | 101110011001 => true
  | 101110011010 => true
  | 101110011011 => true
  | 101110011100 => true
  | 101110011101 => true
  | 101110011110 => true
  | 101110011111 => true
  | 110110100000 => true
  | 000000010101 => true
  | 110000000000 => true
  | 110000000001 => true
  | 110000000010 => true
  | 110010000000 => true
  | 110010000001 => true
  | 110010000010 => true
  | 101100000000 => true
  | 101100000010 => true
  | 101110000000 => true
  | 101110000010 => true
  | 000000000001 => true
  | 000000000010 => true
  | 000000000011 => true
  | 001100100001 => true
  | 011100100001 => true
  | 001100100010 => true
  | 011100100010 => true
  | 000101001101 => true
  | 000101011101 => true
  | 000110000000 => true
  | reg => true
  | _ => false

def csr_name_map_backwards_matches (arg_ : String) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | "misa" => (some true)
  | "mstatus" => (some true)
  | "menvcfg" => (some true)
  | "menvcfgh" => (some true)
  | "senvcfg" => (some true)
  | "mie" => (some true)
  | "mip" => (some true)
  | "medeleg" => (some true)
  | "medelegh" => (some true)
  | "mideleg" => (some true)
  | "mcause" => (some true)
  | "mtval" => (some true)
  | "mscratch" => (some true)
  | "scounteren" => (some true)
  | "mcounteren" => (some true)
  | "mcountinhibit" => (some true)
  | "mvendorid" => (some true)
  | "marchid" => (some true)
  | "mimpid" => (some true)
  | "mhartid" => (some true)
  | "mconfigptr" => (some true)
  | "sstatus" => (some true)
  | "sip" => (some true)
  | "sie" => (some true)
  | "sscratch" => (some true)
  | "scause" => (some true)
  | "stval" => (some true)
  | "tselect" => (some true)
  | "tdata1" => (some true)
  | "tdata2" => (some true)
  | "tdata3" => (some true)
  | "pmpcfg0" => (some true)
  | "pmpcfg1" => (some true)
  | "pmpcfg2" => (some true)
  | "pmpcfg3" => (some true)
  | "pmpcfg4" => (some true)
  | "pmpcfg5" => (some true)
  | "pmpcfg6" => (some true)
  | "pmpcfg7" => (some true)
  | "pmpcfg8" => (some true)
  | "pmpcfg9" => (some true)
  | "pmpcfg10" => (some true)
  | "pmpcfg11" => (some true)
  | "pmpcfg12" => (some true)
  | "pmpcfg13" => (some true)
  | "pmpcfg14" => (some true)
  | "pmpcfg15" => (some true)
  | "pmpaddr0" => (some true)
  | "pmpaddr1" => (some true)
  | "pmpaddr2" => (some true)
  | "pmpaddr3" => (some true)
  | "pmpaddr4" => (some true)
  | "pmpaddr5" => (some true)
  | "pmpaddr6" => (some true)
  | "pmpaddr7" => (some true)
  | "pmpaddr8" => (some true)
  | "pmpaddr9" => (some true)
  | "pmpaddr10" => (some true)
  | "pmpaddr11" => (some true)
  | "pmpaddr12" => (some true)
  | "pmpaddr13" => (some true)
  | "pmpaddr14" => (some true)
  | "pmpaddr15" => (some true)
  | "pmpaddr16" => (some true)
  | "pmpaddr17" => (some true)
  | "pmpaddr18" => (some true)
  | "pmpaddr19" => (some true)
  | "pmpaddr20" => (some true)
  | "pmpaddr21" => (some true)
  | "pmpaddr22" => (some true)
  | "pmpaddr23" => (some true)
  | "pmpaddr24" => (some true)
  | "pmpaddr25" => (some true)
  | "pmpaddr26" => (some true)
  | "pmpaddr27" => (some true)
  | "pmpaddr28" => (some true)
  | "pmpaddr29" => (some true)
  | "pmpaddr30" => (some true)
  | "pmpaddr31" => (some true)
  | "pmpaddr32" => (some true)
  | "pmpaddr33" => (some true)
  | "pmpaddr34" => (some true)
  | "pmpaddr35" => (some true)
  | "pmpaddr36" => (some true)
  | "pmpaddr37" => (some true)
  | "pmpaddr38" => (some true)
  | "pmpaddr39" => (some true)
  | "pmpaddr40" => (some true)
  | "pmpaddr41" => (some true)
  | "pmpaddr42" => (some true)
  | "pmpaddr43" => (some true)
  | "pmpaddr44" => (some true)
  | "pmpaddr45" => (some true)
  | "pmpaddr46" => (some true)
  | "pmpaddr47" => (some true)
  | "pmpaddr48" => (some true)
  | "pmpaddr49" => (some true)
  | "pmpaddr50" => (some true)
  | "pmpaddr51" => (some true)
  | "pmpaddr52" => (some true)
  | "pmpaddr53" => (some true)
  | "pmpaddr54" => (some true)
  | "pmpaddr55" => (some true)
  | "pmpaddr56" => (some true)
  | "pmpaddr57" => (some true)
  | "pmpaddr58" => (some true)
  | "pmpaddr59" => (some true)
  | "pmpaddr60" => (some true)
  | "pmpaddr61" => (some true)
  | "pmpaddr62" => (some true)
  | "pmpaddr63" => (some true)
  | "vstart" => (some true)
  | "vxsat" => (some true)
  | "vxrm" => (some true)
  | "vcsr" => (some true)
  | "vl" => (some true)
  | "vtype" => (some true)
  | "vlenb" => (some true)
  | "stvec" => (some true)
  | "sepc" => (some true)
  | "mtvec" => (some true)
  | "mepc" => (some true)
  | "hpmcounter3" => (some true)
  | "hpmcounter4" => (some true)
  | "hpmcounter5" => (some true)
  | "hpmcounter6" => (some true)
  | "hpmcounter7" => (some true)
  | "hpmcounter8" => (some true)
  | "hpmcounter9" => (some true)
  | "hpmcounter10" => (some true)
  | "hpmcounter11" => (some true)
  | "hpmcounter12" => (some true)
  | "hpmcounter13" => (some true)
  | "hpmcounter14" => (some true)
  | "hpmcounter15" => (some true)
  | "hpmcounter16" => (some true)
  | "hpmcounter17" => (some true)
  | "hpmcounter18" => (some true)
  | "hpmcounter19" => (some true)
  | "hpmcounter20" => (some true)
  | "hpmcounter21" => (some true)
  | "hpmcounter22" => (some true)
  | "hpmcounter23" => (some true)
  | "hpmcounter24" => (some true)
  | "hpmcounter25" => (some true)
  | "hpmcounter26" => (some true)
  | "hpmcounter27" => (some true)
  | "hpmcounter28" => (some true)
  | "hpmcounter29" => (some true)
  | "hpmcounter30" => (some true)
  | "hpmcounter31" => (some true)
  | "hpmcounter3h" => (some true)
  | "hpmcounter4h" => (some true)
  | "hpmcounter5h" => (some true)
  | "hpmcounter6h" => (some true)
  | "hpmcounter7h" => (some true)
  | "hpmcounter8h" => (some true)
  | "hpmcounter9h" => (some true)
  | "hpmcounter10h" => (some true)
  | "hpmcounter11h" => (some true)
  | "hpmcounter12h" => (some true)
  | "hpmcounter13h" => (some true)
  | "hpmcounter14h" => (some true)
  | "hpmcounter15h" => (some true)
  | "hpmcounter16h" => (some true)
  | "hpmcounter17h" => (some true)
  | "hpmcounter18h" => (some true)
  | "hpmcounter19h" => (some true)
  | "hpmcounter20h" => (some true)
  | "hpmcounter21h" => (some true)
  | "hpmcounter22h" => (some true)
  | "hpmcounter23h" => (some true)
  | "hpmcounter24h" => (some true)
  | "hpmcounter25h" => (some true)
  | "hpmcounter26h" => (some true)
  | "hpmcounter27h" => (some true)
  | "hpmcounter28h" => (some true)
  | "hpmcounter29h" => (some true)
  | "hpmcounter30h" => (some true)
  | "hpmcounter31h" => (some true)
  | "mhpmevent3" => (some true)
  | "mhpmevent4" => (some true)
  | "mhpmevent5" => (some true)
  | "mhpmevent6" => (some true)
  | "mhpmevent7" => (some true)
  | "mhpmevent8" => (some true)
  | "mhpmevent9" => (some true)
  | "mhpmevent10" => (some true)
  | "mhpmevent11" => (some true)
  | "mhpmevent12" => (some true)
  | "mhpmevent13" => (some true)
  | "mhpmevent14" => (some true)
  | "mhpmevent15" => (some true)
  | "mhpmevent16" => (some true)
  | "mhpmevent17" => (some true)
  | "mhpmevent18" => (some true)
  | "mhpmevent19" => (some true)
  | "mhpmevent20" => (some true)
  | "mhpmevent21" => (some true)
  | "mhpmevent22" => (some true)
  | "mhpmevent23" => (some true)
  | "mhpmevent24" => (some true)
  | "mhpmevent25" => (some true)
  | "mhpmevent26" => (some true)
  | "mhpmevent27" => (some true)
  | "mhpmevent28" => (some true)
  | "mhpmevent29" => (some true)
  | "mhpmevent30" => (some true)
  | "mhpmevent31" => (some true)
  | "mhpmcounter3" => (some true)
  | "mhpmcounter4" => (some true)
  | "mhpmcounter5" => (some true)
  | "mhpmcounter6" => (some true)
  | "mhpmcounter7" => (some true)
  | "mhpmcounter8" => (some true)
  | "mhpmcounter9" => (some true)
  | "mhpmcounter10" => (some true)
  | "mhpmcounter11" => (some true)
  | "mhpmcounter12" => (some true)
  | "mhpmcounter13" => (some true)
  | "mhpmcounter14" => (some true)
  | "mhpmcounter15" => (some true)
  | "mhpmcounter16" => (some true)
  | "mhpmcounter17" => (some true)
  | "mhpmcounter18" => (some true)
  | "mhpmcounter19" => (some true)
  | "mhpmcounter20" => (some true)
  | "mhpmcounter21" => (some true)
  | "mhpmcounter22" => (some true)
  | "mhpmcounter23" => (some true)
  | "mhpmcounter24" => (some true)
  | "mhpmcounter25" => (some true)
  | "mhpmcounter26" => (some true)
  | "mhpmcounter27" => (some true)
  | "mhpmcounter28" => (some true)
  | "mhpmcounter29" => (some true)
  | "mhpmcounter30" => (some true)
  | "mhpmcounter31" => (some true)
  | "mhpmcounter3h" => (some true)
  | "mhpmcounter4h" => (some true)
  | "mhpmcounter5h" => (some true)
  | "mhpmcounter6h" => (some true)
  | "mhpmcounter7h" => (some true)
  | "mhpmcounter8h" => (some true)
  | "mhpmcounter9h" => (some true)
  | "mhpmcounter10h" => (some true)
  | "mhpmcounter11h" => (some true)
  | "mhpmcounter12h" => (some true)
  | "mhpmcounter13h" => (some true)
  | "mhpmcounter14h" => (some true)
  | "mhpmcounter15h" => (some true)
  | "mhpmcounter16h" => (some true)
  | "mhpmcounter17h" => (some true)
  | "mhpmcounter18h" => (some true)
  | "mhpmcounter19h" => (some true)
  | "mhpmcounter20h" => (some true)
  | "mhpmcounter21h" => (some true)
  | "mhpmcounter22h" => (some true)
  | "mhpmcounter23h" => (some true)
  | "mhpmcounter24h" => (some true)
  | "mhpmcounter25h" => (some true)
  | "mhpmcounter26h" => (some true)
  | "mhpmcounter27h" => (some true)
  | "mhpmcounter28h" => (some true)
  | "mhpmcounter29h" => (some true)
  | "mhpmcounter30h" => (some true)
  | "mhpmcounter31h" => (some true)
  | "mhpmcounter3h" => (some true)
  | "mhpmcounter4h" => (some true)
  | "mhpmcounter5h" => (some true)
  | "mhpmcounter6h" => (some true)
  | "mhpmcounter7h" => (some true)
  | "mhpmcounter8h" => (some true)
  | "mhpmcounter9h" => (some true)
  | "mhpmcounter10h" => (some true)
  | "mhpmcounter11h" => (some true)
  | "mhpmcounter12h" => (some true)
  | "mhpmcounter13h" => (some true)
  | "mhpmcounter14h" => (some true)
  | "mhpmcounter15h" => (some true)
  | "mhpmcounter16h" => (some true)
  | "mhpmcounter17h" => (some true)
  | "mhpmcounter18h" => (some true)
  | "mhpmcounter19h" => (some true)
  | "mhpmcounter20h" => (some true)
  | "mhpmcounter21h" => (some true)
  | "mhpmcounter22h" => (some true)
  | "mhpmcounter23h" => (some true)
  | "mhpmcounter24h" => (some true)
  | "mhpmcounter25h" => (some true)
  | "mhpmcounter26h" => (some true)
  | "mhpmcounter27h" => (some true)
  | "mhpmcounter28h" => (some true)
  | "mhpmcounter29h" => (some true)
  | "mhpmcounter30h" => (some true)
  | "mhpmcounter31h" => (some true)
  | "scountovf" => (some true)
  | "seed" => (some true)
  | "cycle" => (some true)
  | "time" => (some true)
  | "instret" => (some true)
  | "cycleh" => (some true)
  | "timeh" => (some true)
  | "instreth" => (some true)
  | "mcycle" => (some true)
  | "minstret" => (some true)
  | "mcycleh" => (some true)
  | "minstreth" => (some true)
  | "fflags" => (some true)
  | "frm" => (some true)
  | "fcsr" => (some true)
  | "mcyclecfg" => (some true)
  | "mcyclecfgh" => (some true)
  | "minstretcfg" => (some true)
  | "minstretcfgh" => (some true)
  | "stimecmp" => (some true)
  | "stimecmph" => (some true)
  | "satp" => (some true)
  | mapping0_ =>
    (bif (hex_bits_12_backwards_matches mapping0_)
    then
      (match (hex_bits_12_backwards mapping0_) with
      | reg => (some true)
      | _ => none)
    else none)) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

