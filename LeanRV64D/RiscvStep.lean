import LeanRV64D.RiscvFetch

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

noncomputable section

namespace LeanRV64D.Functions

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
open SATPMode
open Retired
open Register
open Privilege
open PmpAddrMatchType
open PTW_Result
open PTW_Error
open PTE_Check
open InterruptType
open FetchResult
open Ext_PhysAddr_Check
open Ext_FetchAddr_Check
open Ext_DataAddr_Check
open Ext_ControlAddr_Check
open ExtStatus
open ExceptionType
open Architecture
open AccessType

/-- Type quantifiers: step_no : Int -/
def step (step_no : Int) : SailM Bool := do
  let _ : Unit := (ext_pre_step_hook ())
  writeReg minstret_increment (← (should_inc_minstret (← readReg cur_privilege)))
  writeReg minstret_write none
  writeReg minstreth_write none
  let (retired, stepped) ← (( do
    match (← (dispatchInterrupt (← readReg cur_privilege))) with
    | .some (intr, priv) => (do
        let _ : Unit :=
          bif (get_config_print_instr ())
          then (print_bits "Handling interrupt: " (interruptType_to_bits intr))
          else ()
        (handle_interrupt intr priv)
        (pure (RETIRE_FAIL, false)))
    | none => (do
        match (ext_fetch_hook (← (fetch ()))) with
        | .F_Ext_Error e => (let _ : Unit := (ext_handle_fetch_check_error e)
          (pure (RETIRE_FAIL, false)))
        | .F_Error (e, addr) => (do
            (handle_mem_exception (Virtaddr addr) e)
            (pure (RETIRE_FAIL, false)))
        | .F_RVC h => (do
            let _ : Unit := (sail_instr_announce h)
            writeReg instbits (zero_extend (m := ((2 ^i 3) *i 8)) h)
            let ast ← do (ext_decode_compressed h)
            bif (get_config_print_instr ())
            then
              (pure (print_endline
                  (HAppend.hAppend "["
                    (HAppend.hAppend (Int.repr step_no)
                      (HAppend.hAppend "] ["
                        (HAppend.hAppend (privLevel_to_str (← readReg cur_privilege))
                          (HAppend.hAppend "]: "
                            (HAppend.hAppend (BitVec.toFormatted (← readReg PC))
                              (HAppend.hAppend " ("
                                (HAppend.hAppend (BitVec.toFormatted h)
                                  (HAppend.hAppend ") " (← (print_insn ast)))))))))))))
            else (pure ())
            bif (← (currentlyEnabled Ext_Zca))
            then
              (do
                writeReg nextPC (BitVec.addInt (← readReg PC) 2)
                let t__4 ← do (execute ast)
                (pure (t__4, true)))
            else
              (do
                (handle_illegal ())
                (pure (RETIRE_FAIL, true))))
        | .F_Base w => (do
            let _ : Unit := (sail_instr_announce w)
            writeReg instbits (zero_extend (m := ((2 ^i 3) *i 8)) w)
            let ast ← do (ext_decode w)
            bif (get_config_print_instr ())
            then
              (pure (print_endline
                  (HAppend.hAppend "["
                    (HAppend.hAppend (Int.repr step_no)
                      (HAppend.hAppend "] ["
                        (HAppend.hAppend (privLevel_to_str (← readReg cur_privilege))
                          (HAppend.hAppend "]: "
                            (HAppend.hAppend (BitVec.toFormatted (← readReg PC))
                              (HAppend.hAppend " ("
                                (HAppend.hAppend (BitVec.toFormatted w)
                                  (HAppend.hAppend ") " (← (print_insn ast)))))))))))))
            else (pure ())
            writeReg nextPC (BitVec.addInt (← readReg PC) 4)
            let t__6 ← do (execute ast)
            (pure (t__6, true)))) ) : SailM (Retired × Bool) )
  (tick_pc ())
  bif (bne retired RETIRE_SUCCESS)
  then writeReg minstret_increment false
  else (pure ())
  (update_minstret ())
  let _ : Unit := (ext_post_step_hook ())
  (pure stepped)

def loop (_ : Unit) : SailM Unit := do
  let insns_per_tick := (plat_insns_per_tick ())
  let i : Int := 0
  let step_no : Int := 0
  let (i, step_no) ← (( do
    let mut loop_vars := (i, step_no)
    while (← (λ (i, step_no) => do (pure (not (← readReg htif_done)))) loop_vars) do
      let (i, step_no) := loop_vars
      loop_vars ← do
        let stepped ← do (step step_no)
        let step_no ← (( do
          bif stepped
          then
            (do
              let step_no : Int := (step_no +i 1)
              let _ : Unit :=
                bif (get_config_print_instr ())
                then (print_step ())
                else ()
              (cycle_count ())
              (pure step_no))
          else (pure step_no) ) : SailM Int )
        let i ← (( do
          bif (← readReg htif_done)
          then
            (do
              let exit_val ← do (pure (BitVec.toNat (← readReg htif_exit_code)))
              let _ : Unit :=
                bif (BEq.beq exit_val 0)
                then (print "SUCCESS")
                else (print_int "FAILURE: " exit_val)
              (pure i))
          else
            (do
              let i : Int := (i +i 1)
              bif (BEq.beq i insns_per_tick)
              then
                (do
                  (tick_clock ())
                  (tick_platform ())
                  (pure 0))
              else (pure i)) ) : SailM Int )
        (pure (i, step_no))
    (pure loop_vars) ) : SailM (Int × Int) )
  (pure ())

def reset (_ : Unit) : SailM Unit := do
  (reset_sys ())
  (reset_vmem ())
  (pure (ext_reset ()))

def init_model (_ : Unit) : SailM Unit := do
  (init_platform ())
  (reset ())

