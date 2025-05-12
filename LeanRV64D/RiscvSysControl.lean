import LeanRV64D.RiscvSmcntrpmf

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

def csrAccess (csr : (BitVec 12)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb csr 11 10)

def csrPriv (csr : (BitVec 12)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb csr 9 8)

def check_CSR_priv (csr : (BitVec 12)) (p : Privilege) : Bool :=
  (zopz0zKzJ_u (privLevel_to_bits p) (csrPriv csr))

/-- Type quantifiers: k_ex281915# : Bool -/
def check_CSR_access (csr : (BitVec 12)) (isWrite : Bool) : Bool :=
  (not (isWrite && ((csrAccess csr) == (0b11 : (BitVec 2)))))

def check_TVM_SATP (csr : (BitVec 12)) (p : Privilege) : SailM Bool := do
  (pure (not
      ((csr == (0x180 : (BitVec 12))) && ((p == Supervisor) && ((_get_Mstatus_TVM
              (← readReg mstatus)) == (0b1 : (BitVec 1)))))))

def feature_enabled_for_priv (p : Privilege) (machine_enable_bit : (BitVec 1)) (supervisor_enable_bit : (BitVec 1)) : SailM Bool := do
  match p with
  | Machine => (pure true)
  | Supervisor => (pure (machine_enable_bit == 1#1))
  | User =>
    (pure ((machine_enable_bit == 1#1) && ((not (← (currentlyEnabled Ext_S))) || (supervisor_enable_bit == 1#1))))

def check_Counteren (csr : (BitVec 12)) (p : Privilege) : SailM Bool := do
  bif ((zopz0zI_u csr (0xC00 : (BitVec 12))) || (zopz0zI_u (0xC1F : (BitVec 12)) csr))
  then (pure true)
  else
    (do
      let index := (BitVec.toNat (Sail.BitVec.extractLsb csr 4 0))
      (feature_enabled_for_priv p (BitVec.access (← readReg mcounteren) index)
        (BitVec.access (← readReg scounteren) index)))

def check_Stimecmp (csr : (BitVec 12)) (p : Privilege) : SailM Bool := do
  bif ((csr != (0x14D : (BitVec 12))) && (csr != (0x15D : (BitVec 12))))
  then (pure true)
  else
    (pure ((p == Machine) || ((p == Supervisor) && (((_get_Counteren_TM (← readReg mcounteren)) == (0b1 : (BitVec 1))) && ((_get_MEnvcfg_STCE
                (← readReg menvcfg)) == (0b1 : (BitVec 1)))))))

/-- Type quantifiers: k_ex282002# : Bool -/
def check_seed_CSR (csr : (BitVec 12)) (p : Privilege) (isWrite : Bool) : Bool :=
  bif (not (csr == (0x015 : (BitVec 12))))
  then true
  else
    (bif (not isWrite)
    then false
    else
      (match p with
      | Machine => true
      | Supervisor => false
      | User => false))

def is_CSR_defined (merge_var : (BitVec 12)) : SailM Bool := do
  match_bv merge_var with
  | 001100000001 => do (pure true)
  | 001100000000 => do (pure true)
  | 001100010000 => do (pure (xlen == 32))
  | 001100001010 => do (currentlyEnabled Ext_U)
  | 001100011010 => do (pure ((← (currentlyEnabled Ext_U)) && (xlen == 32)))
  | 000100001010 => do (currentlyEnabled Ext_S)
  | 001100000100 => do (pure true)
  | 001101000100 => do (pure true)
  | 001100000010 => do (currentlyEnabled Ext_S)
  | 001100010010 => do (pure ((← (currentlyEnabled Ext_S)) && (xlen == 32)))
  | 001100000011 => do (currentlyEnabled Ext_S)
  | 001101000010 => do (pure true)
  | 001101000011 => do (pure true)
  | 001101000000 => do (pure true)
  | 000100000110 => do (currentlyEnabled Ext_S)
  | 001100000110 => do (currentlyEnabled Ext_U)
  | 001100100000 => do (pure true)
  | 111100010001 => do (pure true)
  | 111100010010 => do (pure true)
  | 111100010011 => do (pure true)
  | 111100010100 => do (pure true)
  | 111100010101 => do (pure true)
  | 000100000000 => do (currentlyEnabled Ext_S)
  | 000101000100 => do (currentlyEnabled Ext_S)
  | 000100000100 => do (currentlyEnabled Ext_S)
  | 000101000000 => do (currentlyEnabled Ext_S)
  | 000101000010 => do (currentlyEnabled Ext_S)
  | 000101000011 => do (currentlyEnabled Ext_S)
  | 011110100000 => do (pure true)
  | [00111010,idx:4] => do
    (pure (((sys_pmp_count ()) >b (BitVec.toNat idx)) && (((BitVec.access idx 0) == 0#1) || (xlen == 32))))
  | [00111011,idx:4] => do
    (pure ((sys_pmp_count ()) >b (BitVec.toNat ((0b00 : (BitVec 2)) ++ idx))))
  | [00111100,idx:4] => do
    (pure ((sys_pmp_count ()) >b (BitVec.toNat ((0b01 : (BitVec 2)) ++ idx))))
  | [00111101,idx:4] => do
    (pure ((sys_pmp_count ()) >b (BitVec.toNat ((0b10 : (BitVec 2)) ++ idx))))
  | [00111110,idx:4] => do
    (pure ((sys_pmp_count ()) >b (BitVec.toNat ((0b11 : (BitVec 2)) ++ idx))))
  | 000000001000 => do (currentlyEnabled Ext_V)
  | 000000001001 => do (currentlyEnabled Ext_V)
  | 000000001010 => do (currentlyEnabled Ext_V)
  | 000000001111 => do (currentlyEnabled Ext_V)
  | 110000100000 => do (currentlyEnabled Ext_V)
  | 110000100001 => do (currentlyEnabled Ext_V)
  | 110000100010 => do (currentlyEnabled Ext_V)
  | 000100000101 => do (currentlyEnabled Ext_S)
  | 000101000001 => do (currentlyEnabled Ext_S)
  | 001100000101 => do (pure true)
  | 001101000001 => do (pure true)
  | [0011001,index:5] if ((BitVec.toNat index) ≥b 3) => do (currentlyEnabled Ext_Zihpm)
  | [1011000,index:5] if ((BitVec.toNat index) ≥b 3) => do (currentlyEnabled Ext_Zihpm)
  | [1011100,index:5] if ((BitVec.toNat index) ≥b 3) => do
    (pure ((← (currentlyEnabled Ext_Zihpm)) && (xlen == 32)))
  | [1100000,index:5] if ((BitVec.toNat index) ≥b 3) => do
    (pure ((← (currentlyEnabled Ext_Zihpm)) && (← (currentlyEnabled Ext_U))))
  | [1100100,index:5] if ((BitVec.toNat index) ≥b 3) => do
    (pure ((← (currentlyEnabled Ext_Zihpm)) && ((← (currentlyEnabled Ext_U)) && (xlen == 32))))
  | [0111001,index:5] if ((BitVec.toNat index) ≥b 3) => do
    (pure ((← (currentlyEnabled Ext_Sscofpmf)) && (xlen == 32)))
  | 110110100000 => do
    (pure ((← (currentlyEnabled Ext_Sscofpmf)) && (← (currentlyEnabled Ext_S))))
  | 000000010101 => do (currentlyEnabled Ext_Zkr)
  | 110000000000 => do (currentlyEnabled Ext_Zicntr)
  | 110000000001 => do (currentlyEnabled Ext_Zicntr)
  | 110000000010 => do (currentlyEnabled Ext_Zicntr)
  | 110010000000 => do (pure ((← (currentlyEnabled Ext_Zicntr)) && (xlen == 32)))
  | 110010000001 => do (pure ((← (currentlyEnabled Ext_Zicntr)) && (xlen == 32)))
  | 110010000010 => do (pure ((← (currentlyEnabled Ext_Zicntr)) && (xlen == 32)))
  | 101100000000 => do (currentlyEnabled Ext_Zicntr)
  | 101100000010 => do (currentlyEnabled Ext_Zicntr)
  | 101110000000 => do (pure ((← (currentlyEnabled Ext_Zicntr)) && (xlen == 32)))
  | 101110000010 => do (pure ((← (currentlyEnabled Ext_Zicntr)) && (xlen == 32)))
  | 000000000001 => do (pure ((← (currentlyEnabled Ext_F)) || (← (currentlyEnabled Ext_Zfinx))))
  | 000000000010 => do (pure ((← (currentlyEnabled Ext_F)) || (← (currentlyEnabled Ext_Zfinx))))
  | 000000000011 => do (pure ((← (currentlyEnabled Ext_F)) || (← (currentlyEnabled Ext_Zfinx))))
  | 001100100001 => do (currentlyEnabled Ext_Smcntrpmf)
  | 011100100001 => do (pure ((← (currentlyEnabled Ext_Smcntrpmf)) && (xlen == 32)))
  | 001100100010 => do (currentlyEnabled Ext_Smcntrpmf)
  | 011100100010 => do (pure ((← (currentlyEnabled Ext_Smcntrpmf)) && (xlen == 32)))
  | 000101001101 => do (pure ((← (currentlyEnabled Ext_S)) && (← (currentlyEnabled Ext_Sstc))))
  | 000101011101 => do
    (pure ((← (currentlyEnabled Ext_S)) && ((← (currentlyEnabled Ext_Sstc)) && (xlen == 32))))
  | 000110000000 => do (currentlyEnabled Ext_S)
  | _ => do (pure false)

/-- Type quantifiers: k_ex282238# : Bool -/
def check_CSR (csr : (BitVec 12)) (p : Privilege) (isWrite : Bool) : SailM Bool := do
  (pure ((← (is_CSR_defined csr)) && ((check_CSR_priv csr p) && ((check_CSR_access csr isWrite) && ((← (check_TVM_SATP
                csr p)) && ((← (check_Counteren csr p)) && ((← (check_Stimecmp csr p)) && (check_seed_CSR
                  csr p isWrite))))))))

def exception_delegatee (e : ExceptionType) (p : Privilege) : SailM Privilege := do
  let idx := (num_of_ExceptionType e)
  let super ← do (bit_to_bool (BitVec.access (← readReg medeleg) idx))
  let deleg ← do
    bif ((← (currentlyEnabled Ext_S)) && super)
    then (pure Supervisor)
    else (pure Machine)
  bif (zopz0zI_u (privLevel_to_bits deleg) (privLevel_to_bits p))
  then (pure p)
  else (pure deleg)

def findPendingInterrupt (ip : (BitVec (2 ^ 3 * 8))) : (Option InterruptType) :=
  let ip := (Mk_Minterrupts ip)
  bif ((_get_Minterrupts_MEI ip) == (0b1 : (BitVec 1)))
  then (some I_M_External)
  else
    (bif ((_get_Minterrupts_MSI ip) == (0b1 : (BitVec 1)))
    then (some I_M_Software)
    else
      (bif ((_get_Minterrupts_MTI ip) == (0b1 : (BitVec 1)))
      then (some I_M_Timer)
      else
        (bif ((_get_Minterrupts_SEI ip) == (0b1 : (BitVec 1)))
        then (some I_S_External)
        else
          (bif ((_get_Minterrupts_SSI ip) == (0b1 : (BitVec 1)))
          then (some I_S_Software)
          else
            (bif ((_get_Minterrupts_STI ip) == (0b1 : (BitVec 1)))
            then (some I_S_Timer)
            else none)))))

def getPendingSet (priv : Privilege) : SailM (Option ((BitVec (2 ^ 3 * 8)) × Privilege)) := do
  assert ((← (currentlyEnabled Ext_S)) || ((← readReg mideleg) == (zeros (n := ((2 ^i 3) *i 8))))) "riscv_sys_control.sail:137.58-137.59"
  let pending_m ← do
    (pure ((← readReg mip) &&& ((← readReg mie) &&& (Complement.complement (← readReg mideleg)))))
  let pending_s ← do (pure ((← readReg mip) &&& ((← readReg mie) &&& (← readReg mideleg))))
  let mIE ← do
    (pure (((priv == Machine) && ((_get_Mstatus_MIE (← readReg mstatus)) == (0b1 : (BitVec 1)))) || ((priv == Supervisor) || (priv == User))))
  let sIE ← do
    (pure (((priv == Supervisor) && ((_get_Mstatus_SIE (← readReg mstatus)) == (0b1 : (BitVec 1)))) || (priv == User)))
  bif (mIE && (pending_m != (zeros (n := ((2 ^i 3) *i 8)))))
  then (pure (some (pending_m, Machine)))
  else
    (bif (sIE && (pending_s != (zeros (n := ((2 ^i 3) *i 8)))))
    then (pure (some (pending_s, Supervisor)))
    else (pure none))

def shouldWakeForInterrupt (_ : Unit) : SailM Bool := do
  (pure (((← readReg mip) &&& (← readReg mie)) != (zeros (n := ((2 ^i 3) *i 8)))))

def dispatchInterrupt (priv : Privilege) : SailM (Option (InterruptType × Privilege)) := do
  match (← (getPendingSet priv)) with
  | none => (pure none)
  | .some (ip, p) =>
    (match (findPendingInterrupt ip) with
    | none => (pure none)
    | .some i => (pure (some (i, p))))

def tval (excinfo : (Option (BitVec (2 ^ 3 * 8)))) : (BitVec (2 ^ 3 * 8)) :=
  match excinfo with
  | .some e => e
  | none => (zeros (n := ((2 ^i 3) *i 8)))

def track_trap (p : Privilege) : SailM Unit := do
  (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
  match p with
  | Machine =>
    (do
      (csr_name_write_callback "mcause" (← readReg mcause))
      (csr_name_write_callback "mtval" (← readReg mtval))
      (csr_name_write_callback "mepc" (← readReg mepc)))
  | Supervisor =>
    (do
      (csr_name_write_callback "scause" (← readReg scause))
      (csr_name_write_callback "stval" (← readReg stval))
      (csr_name_write_callback "sepc" (← readReg sepc)))
  | User => (internal_error "riscv_sys_control.sail" 217 "Invalid privilege level")

/-- Type quantifiers: k_ex282484# : Bool -/
def trap_handler (del_priv : Privilege) (intr : Bool) (c : (BitVec 8)) (pc : (BitVec (2 ^ 3 * 8))) (info : (Option (BitVec (2 ^ 3 * 8)))) (ext : (Option Unit)) : SailM (BitVec (2 ^ 3 * 8)) := do
  let _ : Unit := (trap_callback ())
  let _ : Unit :=
    bif (get_config_print_platform ())
    then
      (print_endline
        (HAppend.hAppend "handling "
          (HAppend.hAppend
            (bif intr
            then "int#"
            else "exc#")
            (HAppend.hAppend (BitVec.toFormatted c)
              (HAppend.hAppend " at priv "
                (HAppend.hAppend (privLevel_to_str del_priv)
                  (HAppend.hAppend " with tval " (BitVec.toFormatted (tval info)))))))))
    else ()
  match del_priv with
  | Machine =>
    (do
      writeReg mcause (Sail.BitVec.updateSubrange (← readReg mcause) (((2 ^i 3) *i 8) -i 1)
        (((2 ^i 3) *i 8) -i 1) (bool_to_bits intr))
      writeReg mcause (Sail.BitVec.updateSubrange (← readReg mcause) (((2 ^i 3) *i 8) -i 2) 0
        (zero_extend (m := 63) c))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 7 7
        (_get_Mstatus_MIE (← readReg mstatus)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3 (0b0 : (BitVec 1)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 12 11
        (privLevel_to_bits (← readReg cur_privilege)))
      writeReg mtval (tval info)
      writeReg mepc pc
      writeReg cur_privilege del_priv
      let _ : Unit := (handle_trap_extension del_priv pc ext)
      (track_trap del_priv)
      (prepare_trap_vector del_priv (← readReg mcause)))
  | Supervisor =>
    (do
      assert (← (currentlyEnabled Ext_S)) "no supervisor mode present for delegation"
      writeReg scause (Sail.BitVec.updateSubrange (← readReg scause) (((2 ^i 3) *i 8) -i 1)
        (((2 ^i 3) *i 8) -i 1) (bool_to_bits intr))
      writeReg scause (Sail.BitVec.updateSubrange (← readReg scause) (((2 ^i 3) *i 8) -i 2) 0
        (zero_extend (m := 63) c))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 5 5
        (_get_Mstatus_SIE (← readReg mstatus)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 1 1 (0b0 : (BitVec 1)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 8 8
        (← do
          match (← readReg cur_privilege) with
          | User => (pure (0b0 : (BitVec 1)))
          | Supervisor => (pure (0b1 : (BitVec 1)))
          | Machine =>
            (internal_error "riscv_sys_control.sail" 260 "invalid privilege for s-mode trap")))
      writeReg stval (tval info)
      writeReg sepc pc
      writeReg cur_privilege del_priv
      let _ : Unit := (handle_trap_extension del_priv pc ext)
      (track_trap del_priv)
      (prepare_trap_vector del_priv (← readReg scause)))
  | User => (internal_error "riscv_sys_control.sail" 273 "Invalid privilege level")

def exception_handler (cur_priv : Privilege) (ctl : ctl_result) (pc : (BitVec (2 ^ 3 * 8))) : SailM (BitVec (2 ^ 3 * 8)) := do
  match (cur_priv, ctl) with
  | (_, .CTL_TRAP e) =>
    (do
      let del_priv ← do (exception_delegatee e.trap cur_priv)
      let _ : Unit :=
        bif (get_config_print_platform ())
        then
          (print_endline
            (HAppend.hAppend "trapping from "
              (HAppend.hAppend (privLevel_to_str cur_priv)
                (HAppend.hAppend " to "
                  (HAppend.hAppend (privLevel_to_str del_priv)
                    (HAppend.hAppend " to handle " (exceptionType_to_str e.trap)))))))
        else ()
      (trap_handler del_priv false (exceptionType_to_bits e.trap) pc e.excinfo e.ext))
  | (_, .CTL_MRET ()) =>
    (do
      let prev_priv ← do readReg cur_privilege
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3
        (_get_Mstatus_MPIE (← readReg mstatus)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 7 7 (0b1 : (BitVec 1)))
      writeReg cur_privilege (← (privLevel_of_bits (_get_Mstatus_MPP (← readReg mstatus))))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 12 11
        (privLevel_to_bits
          (← do
            bif (← (currentlyEnabled Ext_U))
            then (pure User)
            else (pure Machine))))
      bif (bne (← readReg cur_privilege) Machine)
      then
        writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 (0b0 : (BitVec 1)))
      else (pure ())
      (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
      bif (get_config_print_platform ())
      then
        (pure (print_endline
            (HAppend.hAppend "ret-ing from "
              (HAppend.hAppend (privLevel_to_str prev_priv)
                (HAppend.hAppend " to " (privLevel_to_str (← readReg cur_privilege)))))))
      else (pure ())
      (prepare_xret_target Machine))
  | (_, .CTL_SRET ()) =>
    (do
      let prev_priv ← do readReg cur_privilege
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 1 1
        (_get_Mstatus_SPIE (← readReg mstatus)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 5 5 (0b1 : (BitVec 1)))
      writeReg cur_privilege (← do
        bif ((_get_Mstatus_SPP (← readReg mstatus)) == (0b1 : (BitVec 1)))
        then (pure Supervisor)
        else (pure User))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 8 8 (0b0 : (BitVec 1)))
      bif (bne (← readReg cur_privilege) Machine)
      then
        writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 (0b0 : (BitVec 1)))
      else (pure ())
      (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
      bif (get_config_print_platform ())
      then
        (pure (print_endline
            (HAppend.hAppend "ret-ing from "
              (HAppend.hAppend (privLevel_to_str prev_priv)
                (HAppend.hAppend " to " (privLevel_to_str (← readReg cur_privilege)))))))
      else (pure ())
      (prepare_xret_target Supervisor))

def handle_mem_exception (typ_0 : virtaddr) (e : ExceptionType) : SailM Unit := do
  let .Virtaddr addr : virtaddr := typ_0
  let t : sync_exception :=
    { trap := e
      excinfo := (some addr)
      ext := none }
  (set_next_pc (← (exception_handler (← readReg cur_privilege) (CTL_TRAP t) (← readReg PC))))

def handle_exception (e : ExceptionType) : SailM Unit := do
  let t : sync_exception :=
    { trap := e
      excinfo := none
      ext := none }
  (set_next_pc (← (exception_handler (← readReg cur_privilege) (CTL_TRAP t) (← readReg PC))))

def handle_interrupt (i : InterruptType) (del_priv : Privilege) : SailM Unit := do
  (set_next_pc
    (← (trap_handler del_priv true (interruptType_to_bits i) (← readReg PC) none none)))

def reset_misa (_ : Unit) : SailM Unit := do
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 0 0
    (bool_to_bits (hartSupports Ext_A)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 2 2
    (bool_to_bits (hartSupports Ext_C)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 1 1
    (bool_to_bits (hartSupports Ext_B)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 8 8 (0b1 : (BitVec 1)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 12 12
    (bool_to_bits (hartSupports Ext_M)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 20 20
    (bool_to_bits (hartSupports Ext_U)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 18 18
    (bool_to_bits (hartSupports Ext_S)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 21 21
    (bool_to_bits (hartSupports Ext_V)))
  bif ((hartSupports Ext_F) && (hartSupports Ext_Zfinx))
  then (internal_error "riscv_sys_control.sail" 352 "F and Zfinx cannot both be enabled!")
  else (pure ())
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 5 5
    (bool_to_bits (hartSupports Ext_F)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 3 3
    (bool_to_bits (hartSupports Ext_D)))
  (csr_name_write_callback "misa" (← readReg misa))

def reset_sys (_ : Unit) : SailM Unit := do
  writeReg cur_privilege Machine
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3 (0b0 : (BitVec 1)))
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 (0b0 : (BitVec 1)))
  (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
  (reset_misa ())
  (cancel_reservation ())
  writeReg mcause (zeros (n := ((2 ^i 3) *i 8)))
  (csr_name_write_callback "mcause" (← readReg mcause))
  (reset_pmp ())
  writeReg vstart (zeros (n := 16))
  writeReg vl (zeros (n := ((2 ^i 3) *i 8)))
  writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 2 1 (0b00 : (BitVec 2)))
  writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 0 0 (0b0 : (BitVec 1)))
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) (((2 ^i 3) *i 8) -i 1)
    (((2 ^i 3) *i 8) -i 1) (0b1 : (BitVec 1)))
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) (((2 ^i 3) *i 8) -i 2) 8
    (zeros (n := 55)))
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 7 7 (0b0 : (BitVec 1)))
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 6 6 (0b0 : (BitVec 1)))
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 5 3 (0b000 : (BitVec 3)))
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 2 0 (0b000 : (BitVec 3)))

/-- Type quantifiers: k_t : Type -/
def MemoryOpResult_add_meta (r : (Result k_t ExceptionType)) (m : Unit) : (Result (k_t × Unit) ExceptionType) :=
  match r with
  | .Ok v => (Ok (v, m))
  | .Err e => (Err e)

/-- Type quantifiers: k_t : Type -/
def MemoryOpResult_drop_meta (r : (Result (k_t × Unit) ExceptionType)) : (Result k_t ExceptionType) :=
  match r with
  | .Ok (v, m) => (Ok v)
  | .Err e => (Err e)

