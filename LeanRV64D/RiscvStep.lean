import LeanRV64D.RiscvFetch

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
open PTW_Result
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

def retires_or_traps (r : (ExecutionResult Retire_Failure)) : Bool :=
  match r with
  | .RETIRE_OK () => true
  | .RETIRE_FAIL (.Illegal_Instruction ()) => true
  | .RETIRE_FAIL (.Memory_Exception _) => true
  | .RETIRE_FAIL (.Trap _) => true
  | .RETIRE_FAIL (.Wait_For_Interrupt ()) => false
  | .RETIRE_FAIL (.Ext_ControlAddr_Check_Failure _) => true
  | .RETIRE_FAIL (.Ext_DataAddr_Check_Failure _) => true
  | .RETIRE_FAIL (.Ext_CSR_Check_Failure ()) => true
  | .RETIRE_FAIL (.Ext_XRET_Priv_Failure _) => true

/-- Type quantifiers: k_ex399856# : Bool, step_no : Int -/
def run_hart_waiting (step_no : Int) (exit_wait : Bool) (instbits : (BitVec (2 ^ 3 * 8))) : SailM (Step × Bool) := do
  bif (← (shouldWakeForInterrupt ()))
  then
    (do
      bif (get_config_print_instr ())
      then
        (pure (print_endline
            (HAppend.hAppend "interrupt exit from WAIT state at PC "
              (BitVec.toFormatted (← readReg PC)))))
      else (pure ())
      writeReg hart_state (HART_ACTIVE ())
      (pure ((Step_Execute ((RETIRE_OK ()), instbits)), true)))
  else
    (do
      bif exit_wait
      then
        (do
          bif (get_config_print_instr ())
          then
            (pure (print_endline
                (HAppend.hAppend "forced exit from WAIT state at PC "
                  (BitVec.toFormatted (← readReg PC)))))
          else (pure ())
          writeReg hart_state (HART_ACTIVE ())
          bif (Bool.or (BEq.beq (← readReg cur_privilege) Machine)
               (BEq.beq (_get_Mstatus_TW (← readReg mstatus)) (0b0 : (BitVec 1))))
          then (pure ((Step_Execute ((RETIRE_OK ()), instbits)), true))
          else (pure ((Step_Execute ((RETIRE_FAIL (Illegal_Instruction ())), instbits)), true)))
      else
        (do
          bif (get_config_print_instr ())
          then
            (pure (print_endline
                (HAppend.hAppend "remaining in WAIT state at PC "
                  (BitVec.toFormatted (← readReg PC)))))
          else (pure ())
          (pure ((Step_Waiting ()), false))))

/-- Type quantifiers: k_ex399871# : Bool, step_no : Int -/
def run_hart_active (step_no : Int) (exit_wait : Bool) : SailM (Step × Bool) := do
  match (← (dispatchInterrupt (← readReg cur_privilege))) with
  | .some (intr, priv) => (pure ((Step_Pending_Interrupt (intr, priv)), false))
  | none => (do
      match (ext_fetch_hook (← (fetch ()))) with
      | .F_Ext_Error e => (pure ((Step_Ext_Fetch_Failure e), false))
      | .F_Error (e, addr) => (pure ((Step_Fetch_Failure ((Virtaddr addr), e)), false))
      | .F_RVC h => (do
          let _ : Unit := (sail_instr_announce h)
          let instbits : xlenbits := (zero_extend (m := ((2 ^i 3) *i 8)) h)
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
              let r ← do (execute ast)
              (pure ((Step_Execute (r, instbits)), (retires_or_traps r))))
          else (pure ((Step_Execute ((RETIRE_FAIL (Illegal_Instruction ())), instbits)), true)))
      | .F_Base w => (do
          let _ : Unit := (sail_instr_announce w)
          let instbits : instbits := (zero_extend (m := ((2 ^i 3) *i 8)) w)
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
          let r ← do (execute ast)
          (pure ((Step_Execute (r, instbits)), (retires_or_traps r)))))

def wfi_is_nop (_ : Unit) : Bool :=
  true

/-- Type quantifiers: k_ex399878# : Bool, step_no : Int -/
def try_step (step_no : Int) (exit_wait : Bool) : SailM Bool := do
  let _ : Unit := (ext_pre_step_hook ())
  writeReg minstret_increment (← (should_inc_minstret (← readReg cur_privilege)))
  let (step_val, did_step) ← (( do
    match (← readReg hart_state) with
    | .HART_WAITING instbits => (run_hart_waiting step_no exit_wait instbits)
    | .HART_ACTIVE () => (run_hart_active step_no exit_wait) ) : SailM (Step × Bool) )
  let stepped : Bool := did_step
  let stepped ← (( do
    match step_val with
    | .Step_Pending_Interrupt (intr, priv) => (do
        let _ : Unit :=
          bif (get_config_print_instr ())
          then (print_bits "Handling interrupt: " (interruptType_to_bits intr))
          else ()
        writeReg minstret_increment false
        (handle_interrupt intr priv)
        (pure stepped))
    | .Step_Ext_Fetch_Failure e => (do
        writeReg minstret_increment false
        let _ : Unit := (ext_handle_fetch_check_error e)
        (pure stepped))
    | .Step_Fetch_Failure (vaddr, e) => (do
        writeReg minstret_increment false
        (handle_mem_exception vaddr e)
        (pure stepped))
    | .Step_Waiting () => (do
        assert (hart_is_waiting (← readReg hart_state)) "cannot be Waiting in a non-Wait state"
        (pure stepped))
    | .Step_Execute (.RETIRE_OK (), _) => (do
        assert (hart_is_active (← readReg hart_state)) "riscv_step.sail:165.39-165.40"
        (pure stepped))
    | .Step_Execute (.RETIRE_FAIL (.Trap (priv, ctl, pc)), _) => (do
        writeReg minstret_increment false
        (set_next_pc (← (exception_handler priv ctl pc)))
        (pure stepped))
    | .Step_Execute (.RETIRE_FAIL (.Memory_Exception (vaddr, e)), _) => (do
        writeReg minstret_increment false
        (handle_mem_exception vaddr e)
        (pure stepped))
    | .Step_Execute (.RETIRE_FAIL (.Illegal_Instruction ()), instbits) => (do
        writeReg minstret_increment false
        (handle_illegal instbits)
        (pure stepped))
    | .Step_Execute (.RETIRE_FAIL (.Wait_For_Interrupt ()), instbits) => (do
        bif (wfi_is_nop ())
        then
          (do
            assert (hart_is_active (← readReg hart_state)) "riscv_step.sail:183.41-183.42"
            (pure true))
        else
          (do
            bif (get_config_print_instr ())
            then
              (pure (print_endline
                  (HAppend.hAppend "entering WAIT state at PC "
                    (BitVec.toFormatted (← readReg PC)))))
            else (pure ())
            writeReg hart_state (HART_WAITING instbits)
            (pure stepped)))
    | .Step_Execute (.RETIRE_FAIL (.Ext_CSR_Check_Failure ()), _) => (do
        writeReg minstret_increment false
        let _ : Unit := (ext_check_CSR_fail ())
        (pure stepped))
    | .Step_Execute (.RETIRE_FAIL (.Ext_ControlAddr_Check_Failure e), _) => (do
        writeReg minstret_increment false
        let _ : Unit := (ext_handle_control_check_error e)
        (pure stepped))
    | .Step_Execute (.RETIRE_FAIL (.Ext_DataAddr_Check_Failure e), _) => (do
        writeReg minstret_increment false
        let _ : Unit := (ext_handle_data_check_error e)
        (pure stepped))
    | .Step_Execute (.RETIRE_FAIL (.Ext_XRET_Priv_Failure ()), _) => (do
        writeReg minstret_increment false
        let _ : Unit := (ext_fail_xret_priv ())
        (pure stepped)) ) : SailM Bool )
  match (← readReg hart_state) with
  | .HART_WAITING _ => (pure ())
  | .HART_ACTIVE () => (do
      (tick_pc ())
      (update_minstret ())
      (pure (ext_post_step_hook ())))
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
        let stepped ← do (try_step step_no true)
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
  writeReg hart_state (HART_ACTIVE ())
  (init_platform ())
  (reset ())

