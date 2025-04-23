import LeanRV64D.PreludeMem

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

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def carryless_mul (a : (BitVec k_n)) (b : (BitVec k_n)) : (BitVec (2 * k_n)) := Id.run do
  let result : (BitVec (2 * k_n)) := (zeros (n := (2 *i (Sail.BitVec.length b))))
  let loop_i_lower := 0
  let loop_i_upper := ((Sail.BitVec.length b) -i 1)
  let mut loop_vars := result
  for i in [loop_i_lower:loop_i_upper:1]i do
    let result := loop_vars
    loop_vars :=
      bif (BEq.beq (BitVec.access a i) 1#1)
      then (result ^^^ (shiftl (zero_extend (m := (2 *i (Sail.BitVec.length b))) b) i))
      else result
  (pure loop_vars)

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def carryless_mulr (a : (BitVec k_n)) (b : (BitVec k_n)) : (BitVec k_n) := Id.run do
  let result : (BitVec k_n) := (zeros (n := (Sail.BitVec.length b)))
  let loop_i_lower := 0
  let loop_i_upper := ((Sail.BitVec.length result) -i 1)
  let mut loop_vars := result
  for i in [loop_i_lower:loop_i_upper:1]i do
    let result := loop_vars
    loop_vars :=
      bif (BEq.beq (BitVec.access a i) 1#1)
      then (result ^^^ (shiftr b (((Sail.BitVec.length result) -i i) -i 1)))
      else result
  (pure loop_vars)

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def carryless_mul_reversed (a : (BitVec k_n)) (b : (BitVec k_n)) : (BitVec k_n) :=
  let prod := (carryless_mul (reverse_bits a) (reverse_bits b))
  (reverse_bits (Sail.BitVec.extractLsb prod ((Sail.BitVec.length b) -i 1) 0))

def cmulr_equivalence (a : (BitVec 16)) (b : (BitVec 16)) : Bool :=
  (BEq.beq (carryless_mul_reversed a b) (carryless_mulr a b))

