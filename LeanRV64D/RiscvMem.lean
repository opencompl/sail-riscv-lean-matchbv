import LeanRV64D.RiscvPlatform

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

/-- Type quantifiers: width : Int -/
def is_aligned_paddr (typ_0 : physaddr) (width : Int) : Bool :=
  let .Physaddr addr : physaddr := typ_0
  ((Int.emod (BitVec.toNat addr) width) == 0)

/-- Type quantifiers: width : Int -/
def is_aligned_vaddr (typ_0 : virtaddr) (width : Int) : Bool :=
  let .Virtaddr addr : virtaddr := typ_0
  ((Int.emod (BitVec.toNat addr) width) == 0)

def is_aligned_bits (vaddr : (BitVec (2 ^ 3 * 8))) (width : word_width) : Bool :=
  match width with
  | BYTE => true
  | HALF => ((Sail.BitVec.extractLsb vaddr 0 0) == (zeros (n := ((0 -i 0) +i 1))))
  | WORD => ((Sail.BitVec.extractLsb vaddr 1 0) == (zeros (n := ((1 -i 0) +i 1))))
  | DOUBLE => ((Sail.BitVec.extractLsb vaddr 2 0) == (zeros (n := ((2 -i 0) +i 1))))

/-- Type quantifiers: k_ex282984# : Bool, k_ex282983# : Bool, k_ex282982# : Bool -/
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

/-- Type quantifiers: k_ex282990# : Bool, k_ex282989# : Bool, k_ex282988# : Bool -/
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

/-- Type quantifiers: k_ex282997# : Bool, k_ex282996# : Bool, k_ex282995# : Bool, k_ex282994# : Bool, width
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
  | (_, .some (v, m)) => (pure (Ok (v, m)))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def phys_access_check (t : (AccessType Unit)) (p : Privilege) (paddr : physaddr) (width : Nat) : SailM (Option ExceptionType) := do
  bif ((sys_pmp_count ()) == 0)
  then (pure none)
  else (pmpCheck paddr width t p)

/-- Type quantifiers: k_ex283020# : Bool, k_ex283019# : Bool, k_ex283018# : Bool, k_ex283017# : Bool, width
  : Nat, 0 < width ∧ width ≤ max_mem_access -/
def checked_mem_read (t : (AccessType Unit)) (priv : Privilege) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) (meta : Bool) : SailM (Result ((BitVec (8 * width)) × Unit) ExceptionType) := do
  match (← (phys_access_check t priv paddr width)) with
  | .some e => (pure (Err e))
  | none =>
    (do
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

/-- Type quantifiers: k_ex283030# : Bool, k_ex283029# : Bool, k_ex283028# : Bool, k_ex283027# : Bool, width
  : Nat, 0 < width ∧ width ≤ max_mem_access -/
def mem_read_priv_meta (typ : (AccessType Unit)) (priv : Privilege) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) (meta : Bool) : SailM (Result ((BitVec (8 * width)) × Unit) ExceptionType) := do
  let result ← (( do
    bif ((aq || res) && (not (is_aligned_paddr paddr width)))
    then (pure (Err (E_Load_Addr_Align ())))
    else
      (do
        match (aq, rl, res) with
        | (false, true, false) => sailThrow ((Error_not_implemented "load.rl"))
        | (false, true, true) => sailThrow ((Error_not_implemented "lr.rl"))
        | (_, _, _) => (checked_mem_read typ priv paddr width aq rl res meta)) ) : SailM
    (MemoryOpResult ((BitVec (8 * width)) × mem_meta)) )
  let _ : Unit :=
    match result with
    | .Ok (value, _) =>
      (mem_read_callback (accessType_to_str typ) (bits_of_physaddr paddr) width value)
    | .Err e => (mem_exception_callback (bits_of_physaddr paddr) (num_of_ExceptionType e))
  (pure result)

/-- Type quantifiers: k_ex283085# : Bool, k_ex283084# : Bool, k_ex283083# : Bool, k_ex283082# : Bool, width
  : Nat, 0 < width ∧ width ≤ max_mem_access -/
def mem_read_meta (typ : (AccessType Unit)) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) (meta : Bool) : SailM (Result ((BitVec (8 * width)) × Unit) ExceptionType) := do
  (mem_read_priv_meta typ
    (← (effectivePrivilege typ (← readReg mstatus) (← readReg cur_privilege))) paddr width aq
    rl res meta)

/-- Type quantifiers: k_ex283088# : Bool, k_ex283087# : Bool, k_ex283086# : Bool, width : Nat, 0 <
  width ∧ width ≤ max_mem_access -/
def mem_read_priv (typ : (AccessType Unit)) (priv : Privilege) (paddr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExceptionType) := do
  (pure (MemoryOpResult_drop_meta (← (mem_read_priv_meta typ priv paddr width aq rl res false))))

/-- Type quantifiers: k_ex283091# : Bool, k_ex283090# : Bool, k_ex283089# : Bool, width : Nat, 0 <
  width ∧ width ≤ max_mem_access -/
def mem_read (typ : (AccessType Unit)) (paddr : physaddr) (width : Nat) (aq : Bool) (rel : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExceptionType) := do
  (mem_read_priv typ
    (← (effectivePrivilege typ (← readReg mstatus) (← readReg cur_privilege))) paddr width aq
    rel res)

/-- Type quantifiers: k_ex283094# : Bool, k_ex283093# : Bool, k_ex283092# : Bool, width : Nat, 0 <
  width ∧ width ≤ max_mem_access -/
def mem_write_ea (addr : physaddr) (width : Nat) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Unit ExceptionType) := do
  bif ((rl || con) && (not (is_aligned_paddr addr width)))
  then (pure (Err (E_SAMO_Addr_Align ())))
  else (pure (Ok (write_ram_ea (← (write_kind_of_flags aq rl con)) addr width)))

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def phys_mem_write (wk : write_kind) (paddr : physaddr) (width : Nat) (data : (BitVec (8 * width))) (meta : Unit) : SailM (Result Bool ExceptionType) := do
  (pure (Ok (← (write_ram wk paddr width data meta))))

/-- Type quantifiers: k_ex283109# : Bool, k_ex283108# : Bool, k_ex283107# : Bool, width : Nat, 0 <
  width ∧ width ≤ max_mem_access -/
def checked_mem_write (paddr : physaddr) (width : Nat) (data : (BitVec (8 * width))) (typ : (AccessType Unit)) (priv : Privilege) (meta : Unit) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  match (← (phys_access_check typ priv paddr width)) with
  | .some e => (pure (Err e))
  | none =>
    (do
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

/-- Type quantifiers: k_ex283123# : Bool, k_ex283122# : Bool, k_ex283121# : Bool, width : Nat, 0 <
  width ∧ width ≤ max_mem_access -/
def mem_write_value_priv_meta (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (typ : (AccessType Unit)) (priv : Privilege) (meta : Unit) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  bif ((rl || con) && (not (is_aligned_paddr paddr width)))
  then (pure (Err (E_SAMO_Addr_Align ())))
  else
    (do
      let result ← do (checked_mem_write paddr width value typ priv meta aq rl con)
      let _ : Unit :=
        match result with
        | .Ok _ => (mem_write_callback (bits_of_physaddr paddr) width value)
        | .Err e => (mem_exception_callback (bits_of_physaddr paddr) (num_of_ExceptionType e))
      (pure result))

/-- Type quantifiers: k_ex283136# : Bool, k_ex283135# : Bool, k_ex283134# : Bool, width : Nat, 0 <
  width ∧ width ≤ max_mem_access -/
def mem_write_value_priv (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (priv : Privilege) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  (mem_write_value_priv_meta paddr width value (Write default_write_acc) priv default_meta aq rl con)

/-- Type quantifiers: k_ex283139# : Bool, k_ex283138# : Bool, k_ex283137# : Bool, width : Nat, 0 <
  width ∧ width ≤ max_mem_access -/
def mem_write_value_meta (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (ext_acc : Unit) (meta : Unit) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  let typ := (Write ext_acc)
  let ep ← do (effectivePrivilege typ (← readReg mstatus) (← readReg cur_privilege))
  (mem_write_value_priv_meta paddr width value typ ep meta aq rl con)

/-- Type quantifiers: k_ex283142# : Bool, k_ex283141# : Bool, k_ex283140# : Bool, width : Nat, 0 <
  width ∧ width ≤ max_mem_access -/
def mem_write_value (paddr : physaddr) (width : Nat) (value : (BitVec (8 * width))) (aq : Bool) (rl : Bool) (con : Bool) : SailM (Result Bool ExceptionType) := do
  (mem_write_value_meta paddr width value default_write_acc default_meta aq rl con)

