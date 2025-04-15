import LeanRV64D.RiscvVmemTlb

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

/-- Type quantifiers: pte_size : Nat, pte_size ∈ {4, 8} -/
def write_pte (paddr : physaddr) (pte_size : Nat) (pte : (BitVec (pte_size * 8))) : SailM (Result Bool ExceptionType) := do
  (mem_write_value_priv paddr pte_size pte Supervisor false false false)

/-- Type quantifiers: pte_size : Nat, pte_size ∈ {4, 8} -/
def read_pte (paddr : physaddr) (pte_size : Nat) : SailM (Result (BitVec (8 * pte_size)) ExceptionType) := do
  (mem_read_priv (Read Data) Supervisor paddr pte_size false false false)

/-- Type quantifiers: k_ex323316# : Bool, level : Nat, k_ex323314# : Bool, k_ex323313# : Bool, sv_width
  : Nat, is_sv_mode(sv_width), 0 ≤ level ∧
  level ≤
  (bif sv_width = 32 then 1 else (bif sv_width = 39 then 2 else (bif sv_width = 48 then 3 else 4))) -/
def pt_walk (sv_width : Nat) (vpn : (BitVec (sv_width - 12))) (ac : (AccessType Unit)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (pt_base : (BitVec (bif sv_width
  = 32 then 22 else 44))) (level : Nat) (global : Bool) (ext_ptw : Unit) : SailM (PTW_Result sv_width) := do
  let vpn_i_size :=
    bif (BEq.beq sv_width 32)
    then 10
    else 9
  let vpn_i :=
    (Sail.BitVec.extractLsb vpn (((level +i 1) *i vpn_i_size) -i 1) (level *i vpn_i_size))
  let log_pte_size_bytes :=
    bif (BEq.beq sv_width 32)
    then 2
    else 3
  let pte_addr := (pt_base ++ (vpn_i ++ (zeros (n := log_pte_size_bytes))))
  assert (Bool.or (BEq.beq sv_width 32) (BEq.beq xlen 64)) "riscv_vmem.sail:100.36-100.37"
  let pte_addr := (Physaddr (zero_extend (m := 64) pte_addr))
  match (← (read_pte pte_addr (2 ^i log_pte_size_bytes))) with
  | .Err _ => (pure (PTW_Failure ((PTW_Access ()), ext_ptw)))
  | .Ok pte => (do
      let pte_flags := (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
      let pte_ext := (ext_bits_of_PTE pte)
      bif (← (pte_is_invalid pte_flags pte_ext))
      then (pure (PTW_Failure ((PTW_Invalid_PTE ()), ext_ptw)))
      else
        (do
          let ppn := (PPN_of_PTE pte)
          let global := (Bool.or global (BEq.beq (_get_PTE_Flags_G pte_flags) (0b1 : (BitVec 1))))
          bif (pte_is_non_leaf pte_flags)
          then
            (do
              bif (level >b 0)
              then (pt_walk sv_width vpn ac priv mxr do_sum ppn (level -i 1) global ext_ptw)
              else (pure (PTW_Failure ((PTW_Invalid_PTE ()), ext_ptw))))
          else
            (do
              let pte_check ← do
                (check_PTE_permission ac priv mxr do_sum pte_flags pte_ext ext_ptw)
              match pte_check with
              | .PTE_Check_Failure (ext_ptw, ext_ptw_fail) => (pure (PTW_Failure
                    ((ext_get_ptw_error ext_ptw_fail), ext_ptw)))
              | .PTE_Check_Success ext_ptw => (bif (level >b 0)
                then
                  (let ppn_size_bits :=
                    bif (BEq.beq sv_width 32)
                    then 10
                    else 9
                  let low_bits := (ppn_size_bits *i level)
                  bif (bne (Sail.BitVec.extractLsb ppn (low_bits -i 1) 0)
                       (zeros
                         (n := (((((bif (BEq.beq sv_width 32)
                                 then 10
                                 else 9) *i level) -i 1) -i 0) +i 1))))
                  then (pure (PTW_Failure ((PTW_Misaligned ()), ext_ptw)))
                  else
                    (let ppn :=
                      ((Sail.BitVec.extractLsb ppn ((Sail.BitVec.length ppn) -i 1) low_bits) ++ (Sail.BitVec.extractLsb
                          vpn (low_bits -i 1) 0))
                    (pure (PTW_Success
                        ({ ppn := ppn
                           pte := pte
                           pteAddr := pte_addr
                           level := level
                           global := global }, ext_ptw)))))
                else
                  (pure (PTW_Success
                      ({ ppn := ppn
                         pte := pte
                         pteAddr := pte_addr
                         level := level
                         global := global }, ext_ptw)))))))

/-- Type quantifiers: k_n : Nat, k_n ∈ {32, 64} -/
def satp_to_asid (satp_val : (BitVec k_n)) : (BitVec (bif k_n = 32 then 9 else 16)) :=
  bif (BEq.beq (Sail.BitVec.length satp_val) 32)
  then (_get_Satp32_Asid (Mk_Satp32 satp_val))
  else (_get_Satp64_Asid (Mk_Satp64 satp_val))

/-- Type quantifiers: k_n : Nat, k_n ∈ {32, 64} -/
def satp_to_ppn (satp_val : (BitVec k_n)) : (BitVec (bif k_n = 32 then 22 else 44)) :=
  bif (BEq.beq (Sail.BitVec.length satp_val) 32)
  then (_get_Satp32_PPN (Mk_Satp32 satp_val))
  else (_get_Satp64_PPN (Mk_Satp64 satp_val))

def translationMode (priv : Privilege) : SailM SATPMode := do
  bif (BEq.beq priv Machine)
  then (pure Bare)
  else
    (do
      let arch ← do (architecture_backwards (get_mstatus_SXL (← readReg mstatus)))
      let mbits ← (( do
        match arch with
        | RV64 => (do
            assert (xlen ≥b 64) "riscv_vmem.sail:186.25-186.26"
            (pure (_get_Satp64_Mode (Mk_Satp64 (← readReg satp)))))
        | RV32 => (pure ((0b000 : (BitVec 3)) ++ (_get_Satp32_Mode
                (Mk_Satp32 (Sail.BitVec.extractLsb (← readReg satp) 31 0)))))
        | RV128 => (internal_error "riscv_vmem.sail" 190 "RV128 not supported") ) : SailM satp_mode
        )
      match (satpMode_of_bits arch mbits) with
      | .some m => (pure m)
      | none => (internal_error "riscv_vmem.sail" 195 "invalid translation mode in satp"))

/-- Type quantifiers: tlb_index : Nat, k_ex323380# : Bool, k_ex323379# : Bool, sv_width : Nat, is_sv_mode(sv_width), 0
  ≤ tlb_index ∧ tlb_index ≤ (64 - 1) -/
def translate_TLB_hit (sv_width : Nat) (asid : (BitVec 16)) (vpn : (BitVec (sv_width - 12))) (ac : (AccessType Unit)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (ext_ptw : Unit) (tlb_index : Nat) (ent : TLB_Entry) : SailM (TR_Result (BitVec (bif sv_width
  = 32 then 22 else 44)) PTW_Error) := do
  let pte_width :=
    bif (BEq.beq sv_width 32)
    then 4
    else 8
  let pte := (tlb_get_pte pte_width ent)
  let ext_pte := (ext_bits_of_PTE pte)
  let pte_flags := (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
  let pte_check ← do (check_PTE_permission ac priv mxr do_sum pte_flags ext_pte ext_ptw)
  match pte_check with
  | .PTE_Check_Failure (ext_ptw, ext_ptw_fail) => (pure (TR_Failure
        ((ext_get_ptw_error ext_ptw_fail), ext_ptw)))
  | .PTE_Check_Success ext_ptw => (do
      match (update_PTE_Bits pte ac) with
      | none => (pure (TR_Address ((tlb_get_ppn sv_width ent vpn), ext_ptw)))
      | .some pte' => (do
          bif (not (plat_enable_dirty_update ()))
          then (pure (TR_Failure ((PTW_PTE_Update ()), ext_ptw)))
          else
            (do
              (write_TLB tlb_index (tlb_set_pte ent pte'))
              match (← (write_pte ent.pteAddr pte_width pte')) with
              | .Ok _ => (pure ())
              | .Err e => (internal_error "riscv_vmem.sail" 250 "invalid physical address in TLB")
              (pure (TR_Address ((tlb_get_ppn sv_width ent vpn), ext_ptw))))))

/-- Type quantifiers: k_ex323404# : Bool, k_ex323403# : Bool, sv_width : Nat, is_sv_mode(sv_width) -/
def translate_TLB_miss (sv_width : Nat) (asid : (BitVec 16)) (base_ppn : (BitVec (bif sv_width = 32 then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (ac : (AccessType Unit)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (ext_ptw : Unit) : SailM (TR_Result (BitVec (bif sv_width
  = 32 then 22 else 44)) PTW_Error) := do
  let initial_level :=
    bif (BEq.beq sv_width 32)
    then 1
    else
      (bif (BEq.beq sv_width 39)
      then 2
      else
        (bif (BEq.beq sv_width 48)
        then 3
        else 4))
  let pte_width :=
    bif (BEq.beq sv_width 32)
    then 4
    else 8
  let ptw_result ← do
    (pt_walk sv_width vpn ac priv mxr do_sum base_ppn initial_level false ext_ptw)
  match ptw_result with
  | .PTW_Failure (f, ext_ptw) => (pure (TR_Failure (f, ext_ptw)))
  | .PTW_Success ({ ppn := ppn, pte := pte, pteAddr := pteAddr, level := level, global := global }, ext_ptw) => (do
      let ext_pte := (ext_bits_of_PTE pte)
      match (update_PTE_Bits pte ac) with
      | none => (do
          (add_to_TLB sv_width asid vpn ppn pte pteAddr level global)
          (pure (TR_Address (ppn, ext_ptw))))
      | .some pte => (do
          bif (not (plat_enable_dirty_update ()))
          then (pure (TR_Failure ((PTW_PTE_Update ()), ext_ptw)))
          else
            (do
              match (← (write_pte pteAddr pte_width pte)) with
              | .Ok _ => (do
                  (add_to_TLB sv_width asid vpn ppn pte pteAddr level global)
                  (pure (TR_Address (ppn, ext_ptw))))
              | .Err e => (pure (TR_Failure ((PTW_Access ()), ext_ptw))))))

def satp_mode_width_forwards (arg_ : SATPMode) : SailM Int := do
  match arg_ with
  | Sv32 => (pure 32)
  | Sv39 => (pure 39)
  | Sv48 => (pure 48)
  | Sv57 => (pure 57)
  | _ => (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {32, 39, 48, 57} -/
def satp_mode_width_backwards (arg_ : Nat) : SATPMode :=
  match arg_ with
  | 32 => Sv32
  | 39 => Sv39
  | 48 => Sv48
  | _ => Sv57

def satp_mode_width_forwards_matches (arg_ : SATPMode) : Bool :=
  match arg_ with
  | Sv32 => true
  | Sv39 => true
  | Sv48 => true
  | Sv57 => true
  | _ => false

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {32, 39, 48, 57} -/
def satp_mode_width_backwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 32 => true
  | 39 => true
  | 48 => true
  | 57 => true
  | _ => false

/-- Type quantifiers: k_ex323447# : Bool, k_ex323446# : Bool, sv_width : Nat, is_sv_mode(sv_width) -/
def translate (sv_width : Nat) (asid : (BitVec 16)) (base_ppn : (BitVec (bif sv_width = 32 then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (ac : (AccessType Unit)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (ext_ptw : Unit) : SailM (TR_Result (BitVec (bif sv_width
  = 32 then 22 else 44)) PTW_Error) := do
  match (← (lookup_TLB sv_width asid vpn)) with
  | .some (index, ent) => (translate_TLB_hit sv_width asid vpn ac priv mxr do_sum ext_ptw index ent)
  | none => (translate_TLB_miss sv_width asid base_ppn vpn ac priv mxr do_sum ext_ptw)

/-- Type quantifiers: sv_width : Nat, is_sv_mode(sv_width) -/
def get_satp (sv_width : Nat) : SailM (BitVec (bif sv_width = 32 then 32 else 64)) := do
  assert (Bool.or (BEq.beq sv_width 32) (BEq.beq xlen 64)) "riscv_vmem.sail:346.30-346.31"
  bif (BEq.beq sv_width 32)
  then (pure (Sail.BitVec.extractLsb (← readReg satp) 31 0))
  else readReg satp

def translateAddr (vAddr : virtaddr) (ac : (AccessType Unit)) : SailM (TR_Result physaddr ExceptionType) := do
  let effPriv ← do (effectivePrivilege ac (← readReg mstatus) (← readReg cur_privilege))
  let mode ← do (translationMode effPriv)
  bif (BEq.beq mode Bare)
  then (pure (TR_Address ((Physaddr (zero_extend (m := 64) (virtaddr_bits vAddr))), init_ext_ptw)))
  else
    (do
      let sv_width ← do (satp_mode_width_forwards mode)
      let satp_sxlen ← do (get_satp sv_width)
      assert (Bool.or (BEq.beq sv_width 32) (BEq.beq xlen 64)) "riscv_vmem.sail:372.36-372.37"
      let svAddr := (Sail.BitVec.extractLsb (virtaddr_bits vAddr) (sv_width -i 1) 0)
      bif (bne (virtaddr_bits vAddr) (sign_extend (m := ((2 ^i 3) *i 8)) svAddr))
      then (pure (TR_Failure ((translationException ac (PTW_Invalid_Addr ())), init_ext_ptw)))
      else
        (do
          let mxr ← do
            (pure (BEq.beq (_get_Mstatus_MXR (← readReg mstatus)) (0b1 : (BitVec 1))))
          let do_sum ← do
            (pure (BEq.beq (_get_Mstatus_SUM (← readReg mstatus)) (0b1 : (BitVec 1))))
          let asid := (satp_to_asid satp_sxlen)
          let base_ppn := (satp_to_ppn satp_sxlen)
          let res ← do
            (translate sv_width (zero_extend (m := 16) asid) base_ppn
              (Sail.BitVec.extractLsb svAddr (sv_width -i 1) pagesize_bits) ac effPriv mxr do_sum
              init_ext_ptw)
          match res with
          | .TR_Address (ppn, ext_ptw) => (let paddr :=
              (ppn ++ (Sail.BitVec.extractLsb (virtaddr_bits vAddr) (pagesize_bits -i 1) 0))
            (pure (TR_Address ((Physaddr (zero_extend (m := 64) paddr)), ext_ptw))))
          | .TR_Failure (f, ext_ptw) => (pure (TR_Failure ((translationException ac f), ext_ptw)))))

def reset_vmem (_ : Unit) : SailM Unit := do
  (reset_TLB ())

