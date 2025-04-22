import LeanRV64D.RiscvPlatform

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

/-- Type quantifiers: width : Int -/
def is_aligned_addr (typ_0 : physaddr) (width : Int) : Bool :=
  let .Physaddr addr : physaddr := typ_0
  (BEq.beq (Int.emod (BitVec.toNat addr) width) 0)

/-- Type quantifiers: k_ex344883# : Bool, k_ex344882# : Bool, k_ex344881# : Bool -/
def read_kind_of_flags (aq : Bool) (rl : Bool) (res : Bool) : (Option read_kind) :=
  match (aq, rl, res) with
  | (false, false, false) => (some Read_plain)
  | (true, false, false) => (some Read_RISCV_acquire)
  | (true, true, false) => (some Read_RISCV_strong_acquire)
  | (false, false, true) => (some Read_RISCV_reserved)
  | (true, false, true) => (some Read_RISCV_reserved_acquire)
  | (true, true, true) => (some Read_RISCV_reserved_strong_acquire)
  | (false, true, false) => none
  | (false, true, true) => none

/-- Type quantifiers: k_ex344889# : Bool, k_ex344888# : Bool, k_ex344887# : Bool -/
def write_kind_of_flags (aq : Bool) (rl : Bool) (con : Bool) : SailM write_kind := do
  match (aq, rl, con) with
  | (false, false, false) => (pure Write_plain)
  | (false, true, false) => (pure Write_RISCV_release)
  | (false, false, true) => (pure Write_RISCV_conditional)
  | (false, true, true) => (pure Write_RISCV_conditional_release)
  | (true, true, false) => (pure Write_RISCV_strong_release)
  | (true, true, true) => (pure Write_RISCV_conditional_strong_release)
  | (true, false, false) => sailThrow ((Error_not_implemented "store.aq"))
  | (true, false, true) => sailThrow ((Error_not_implemented "sc.aq"))

/-- Type quantifiers: k_ex344896# : Bool, k_ex344895# : Bool, k_ex344894# : Bool, k_ex344893# : Bool, width
  : Nat, 0 < width ∧ width ≤ max_mem_access -/
def phys_mem_read (t : (AccessType Unit)) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) (meta : Bool) : SailM (Result ((BitVec (8 * width)) × Unit) ExceptionType) := do
  let result ← do
    match (read_kind_of_flags aq rl res) with
    | .some rk => (pure (some (← (read_ram rk paddr width meta))))
    | none => (pure none)
  match (t, result) with
  | (.InstructionFetch (), none) => (pure (Err (E_Fetch_Access_Fault ())))
  | (.Read Data, none) => (pure (Err (E_Load_Access_Fault ())))
  | (_, none) => (pure (Err (E_SAMO_Access_Fault ())))
  | (_, .some (v, m)) => (let _ : Unit :=
      bif (get_config_print_mem ())
      then
        (print_endline
          (HAppend.hAppend "mem["
            (HAppend.hAppend (accessType_to_str t)
              (HAppend.hAppend ","
                (HAppend.hAppend (BitVec.toFormatted (bits_of_physaddr paddr))
                  (HAppend.hAppend "] -> " (BitVec.toFormatted v)))))))
      else ()
    (pure (Ok (v, m))))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def phys_access_check (t : (AccessType Unit)) (p : Privilege) (paddr : physaddr) (width : Nat) : SailM (Option ExceptionType) := do
  bif (BEq.beq (sys_pmp_count ()) 0)
  then (pure none)
  else (pmpCheck paddr width t p)

/-- Type quantifiers: k_ex344920# : Bool, k_ex344919# : Bool, k_ex344918# : Bool, k_ex344917# : Bool, width
  : Nat, 0 < width ∧ width ≤ max_mem_access -/
def checked_mem_read (t : (AccessType Unit)) (priv : Privilege) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) (meta : Bool) : SailM (Result ((BitVec (8 * width)) × Unit) ExceptionType) := do
  match (← (phys_access_check t priv paddr width)) with
  | .some e => (pure (Err e))
  | none => (do
      bif (within_mmio_readable paddr width)
      then (pure (MemoryOpResult_add_meta (← (mmio_read t paddr width)) default_meta))
      else
        (do
          bif (within_phys_mem paddr width)
          then
            (do
              match (ext_check_phys_mem_read t paddr width aq rl res meta) with
              | .Ext_PhysAddr_OK () => (phys_mem_read t paddr width aq rl res meta)
              | .Ext_PhysAddr_Error e => (pure (Err e)))
          else
            (match t with
            | .InstructionFetch () => (pure (Err (E_Fetch_Access_Fault ())))
            | .Read Data => (pure (Err (E_Load_Access_Fault ())))
            | _ => (pure (Err (E_SAMO_Access_Fault ()))))))

/-- Type quantifiers: width : Nat, width > 0 -/
def rvfi_read (app_0 : physaddr) (width : Nat) (result : (Result ((BitVec (8 * width)) × Unit) ExceptionType)) : Unit :=
  let .Physaddr addr := app_0
  ()

/-- Type quantifiers: k_ex344930# : Bool, k_ex344929# : Bool, k_ex344928# : Bool, k_ex344927# : Bool, width
  : Nat, 0 < width ∧ width ≤ max_mem_access -/
def mem_read_priv_meta (typ : (AccessType Unit)) (priv : Privilege) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) (meta : Bool) : SailM (Result ((BitVec (8 * width)) × Unit) ExceptionType) := do
  let result ← (( do
    bif (Bool.and (Bool.or aq res) (not (is_aligned_addr paddr width)))
    then (pure (Err (E_Load_Addr_Align ())))
    else
      (do
        match (aq, rl, res) with
        | (false, true, false) => sailThrow ((Error_not_implemented "load.rl"))
        | (false, true, true) => sailThrow ((Error_not_implemented "lr.rl"))
        | (_, _, _) => (checked_mem_read typ priv paddr width aq rl res meta)) ) : SailM
    (MemoryOpResult ((BitVec (8 * width)) × mem_meta)) )
  let _ : Unit := (rvfi_read paddr width result)
  (pure result)

/-- Type quantifiers: k_ex344984# : Bool, k_ex344983# : Bool, k_ex344982# : Bool, k_ex344981# : Bool, width
  : Nat, 0 < width ∧ width ≤ max_mem_access -/
def mem_read_meta (typ : (AccessType Unit)) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) (meta : Bool) : SailM (Result ((BitVec (8 * width)) × Unit) ExceptionType) := do
  (mem_read_priv_meta typ
    (← (effectivePrivilege typ (← readReg mstatus) (← readReg cur_privilege))) paddr width aq
    rl res meta)

/-- Type quantifiers: k_ex344987# : Bool, k_ex344986# : Bool, k_ex344985# : Bool, width : Nat, 0 <
  width ∧ width ≤ max_mem_access -/
def mem_read_priv (typ : (AccessType Unit)) (priv : Privilege) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExceptionType) := do
  (pure (MemoryOpResult_drop_meta (← (mem_read_priv_meta typ priv paddr width aq rl res false))))

/-- Type quantifiers: k_ex344990# : Bool, k_ex344989# : Bool, k_ex344988# : Bool, width : Nat, 0 <
  width ∧ width ≤ max_mem_access -/
def mem_read (typ : (AccessType Unit)) (paddr : physaddr) (width : Nat) (aq : Bool) (rel : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExceptionType) := do
  (mem_read_priv typ
    (← (effectivePrivilege typ (← readReg mstatus) (← readReg cur_privilege))) paddr width aq
    rel res)

/-- Type quantifiers: k_ex344993# : Bool, k_ex344992# : Bool, k_ex344991# : Bool, width : Nat, 0 <
  width ∧ width ≤ max_mem_access -/
def mem_write_ea (addr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Unit ExceptionType) := do
  bif (Bool.and (Bool.or rl con) (not (is_aligned_addr addr width)))
  then (pure (Err (E_SAMO_Addr_Align ())))
  else (pure (Ok (write_ram_ea (← (write_kind_of_flags aq rl con)) addr width)))

/-- Type quantifiers: width : Nat, width > 0 -/
def rvfi_write (app_0 : physaddr) (width : Nat) (value : (BitVec (8 * width))) (meta : Unit) (result : (Result Bool ExceptionType)) : Unit :=
  let .Physaddr addr := app_0
  ()

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def phys_mem_write (wk : write_kind) (paddr : physaddr) (width : Nat) (data : (BitVec (8 * width))) (meta : Unit) : SailM (Result Bool ExceptionType) := do
  let result ← do (write_ram wk paddr width data meta)
  let _ : Unit :=
    bif (get_config_print_mem ())
    then
      (print_endline
        (HAppend.hAppend "mem["
          (HAppend.hAppend (BitVec.toFormatted (bits_of_physaddr paddr))
            (HAppend.hAppend "] <- " (BitVec.toFormatted data)))))
    else ()
  (pure (Ok result))

/-- Type quantifiers: k_ex345011# : Bool, k_ex345010# : Bool, k_ex345009# : Bool, width : Nat, 0 <
  width ∧ width ≤ max_mem_access -/
def checked_mem_write (paddr : physaddr) (width : Nat) (data : (BitVec (8 * width))) (typ : (AccessType Unit)) (priv : Privilege) (meta : Unit) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  match (← (phys_access_check typ priv paddr width)) with
  | .some e => (pure (Err e))
  | none => (do
      bif (within_mmio_writable paddr width)
      then (mmio_write paddr width data)
      else
        (do
          bif (within_phys_mem paddr width)
          then
            (do
              let wk ← do (write_kind_of_flags aq rl con)
              match (ext_check_phys_mem_write wk paddr width data meta) with
              | .Ext_PhysAddr_OK () => (phys_mem_write wk paddr width data meta)
              | .Ext_PhysAddr_Error e => (pure (Err e)))
          else (pure (Err (E_SAMO_Access_Fault ())))))

/-- Type quantifiers: k_ex345025# : Bool, k_ex345024# : Bool, k_ex345023# : Bool, width : Nat, 0 <
  width ∧ width ≤ max_mem_access -/
def mem_write_value_priv_meta (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (typ : (AccessType Unit)) (priv : Privilege) (meta : Unit) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  bif (Bool.and (Bool.or rl con) (not (is_aligned_addr paddr width)))
  then (pure (Err (E_SAMO_Addr_Align ())))
  else
    (do
      let result ← do (checked_mem_write paddr width value typ priv meta aq rl con)
      let _ : Unit := (rvfi_write paddr width value meta result)
      (pure result))

/-- Type quantifiers: k_ex345036# : Bool, k_ex345035# : Bool, k_ex345034# : Bool, width : Nat, 0 <
  width ∧ width ≤ max_mem_access -/
def mem_write_value_priv (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (priv : Privilege) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  (mem_write_value_priv_meta paddr width value (Write default_write_acc) priv default_meta aq rl con)

/-- Type quantifiers: k_ex345039# : Bool, k_ex345038# : Bool, k_ex345037# : Bool, width : Nat, 0 <
  width ∧ width ≤ max_mem_access -/
def mem_write_value_meta (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (ext_acc : Unit) (meta : Unit) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  let typ := (Write ext_acc)
  let ep ← do (effectivePrivilege typ (← readReg mstatus) (← readReg cur_privilege))
  (mem_write_value_priv_meta paddr width value typ ep meta aq rl con)

/-- Type quantifiers: k_ex345042# : Bool, k_ex345041# : Bool, k_ex345040# : Bool, width : Nat, 0 <
  width ∧ width ≤ max_mem_access -/
def mem_write_value (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  (mem_write_value_meta paddr width value default_write_acc default_meta aq rl con)

