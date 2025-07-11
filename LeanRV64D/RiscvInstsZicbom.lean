import LeanRV64D.RiscvInstsVextFpRed

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

def cbo_clean_flush_enabled (p : Privilege) : SailM Bool := do
  (feature_enabled_for_priv p (BitVec.access (_get_MEnvcfg_CBCFE (← readReg menvcfg)) 0)
    (BitVec.access (_get_SEnvcfg_CBCFE (← readReg senvcfg)) 0))

def encdec_cbop_forwards (arg_ : cbop_zicbom) : (BitVec 12) :=
  match arg_ with
  | CBO_CLEAN => (0x001 : (BitVec 12))
  | CBO_FLUSH => (0x002 : (BitVec 12))
  | CBO_INVAL => (0x000 : (BitVec 12))

def encdec_cbop_backwards (arg_ : (BitVec 12)) : SailM cbop_zicbom := do
  match_bv arg_ with
  | 000000000001 => do (pure CBO_CLEAN)
  | 000000000010 => do (pure CBO_FLUSH)
  | 000000000000 => do (pure CBO_INVAL)
  | _ => do
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_cbop_forwards_matches (arg_ : cbop_zicbom) : Bool :=
  match arg_ with
  | CBO_CLEAN => true
  | CBO_FLUSH => true
  | CBO_INVAL => true
  | _ => false

def encdec_cbop_backwards_matches (arg_ : (BitVec 12)) : Bool :=
  match_bv arg_ with
  | 000000000001 => true
  | 000000000010 => true
  | 000000000000 => true
  | _ => false

def cbop_mnemonic_backwards (arg_ : String) : SailM cbop_zicbom := do
  match arg_ with
  | "cbo.clean" => (pure CBO_CLEAN)
  | "cbo.flush" => (pure CBO_FLUSH)
  | "cbo.inval" => (pure CBO_INVAL)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def cbop_mnemonic_forwards_matches (arg_ : cbop_zicbom) : Bool :=
  match arg_ with
  | CBO_CLEAN => true
  | CBO_FLUSH => true
  | CBO_INVAL => true
  | _ => false

def cbop_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "cbo.clean" => true
  | "cbo.flush" => true
  | "cbo.inval" => true
  | _ => false

def undefined_cbie (_ : Unit) : SailM cbie := do
  (internal_pick [CBIE_ILLEGAL, CBIE_EXEC_FLUSH, CBIE_EXEC_INVAL])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def cbie_of_num (arg_ : Nat) : cbie :=
  match arg_ with
  | 0 => CBIE_ILLEGAL
  | 1 => CBIE_EXEC_FLUSH
  | _ => CBIE_EXEC_INVAL

def num_of_cbie (arg_ : cbie) : Int :=
  match arg_ with
  | CBIE_ILLEGAL => 0
  | CBIE_EXEC_FLUSH => 1
  | CBIE_EXEC_INVAL => 2

def encdec_cbie_forwards (arg_ : cbie) : (BitVec 2) :=
  match arg_ with
  | CBIE_ILLEGAL => (0b00 : (BitVec 2))
  | CBIE_EXEC_FLUSH => (0b01 : (BitVec 2))
  | CBIE_EXEC_INVAL => (0b11 : (BitVec 2))

def encdec_cbie_backwards (arg_ : (BitVec 2)) : SailM cbie := do
  match_bv arg_ with
  | 00 => do (pure CBIE_ILLEGAL)
  | 01 => do (pure CBIE_EXEC_FLUSH)
  | 11 => do (pure CBIE_EXEC_INVAL)
  | _ => do (internal_error "riscv_insts_zicbom.sail" 44 "reserved CBIE")

def encdec_cbie_forwards_matches (arg_ : cbie) : Bool :=
  match arg_ with
  | CBIE_ILLEGAL => true
  | CBIE_EXEC_FLUSH => true
  | CBIE_EXEC_INVAL => true
  | _ => false

def encdec_cbie_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match_bv arg_ with
  | 00 => true
  | 01 => true
  | 11 => true
  | 10 => true
  | _ => false

def undefined_checked_cbop (_ : Unit) : SailM checked_cbop := do
  (internal_pick [CBOP_ILLEGAL, CBOP_ILLEGAL_VIRTUAL, CBOP_INVAL_FLUSH, CBOP_INVAL_INVAL])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def checked_cbop_of_num (arg_ : Nat) : checked_cbop :=
  match arg_ with
  | 0 => CBOP_ILLEGAL
  | 1 => CBOP_ILLEGAL_VIRTUAL
  | 2 => CBOP_INVAL_FLUSH
  | _ => CBOP_INVAL_INVAL

def num_of_checked_cbop (arg_ : checked_cbop) : Int :=
  match arg_ with
  | CBOP_ILLEGAL => 0
  | CBOP_ILLEGAL_VIRTUAL => 1
  | CBOP_INVAL_FLUSH => 2
  | CBOP_INVAL_INVAL => 3

def cbop_priv_check (p : Privilege) : SailM checked_cbop := do
  let mCBIE ← (( do (encdec_cbie_backwards (_get_MEnvcfg_CBIE (← readReg menvcfg))) ) : SailM
    cbie )
  let sCBIE ← (( do
    bif (← (currentlyEnabled Ext_S))
    then (encdec_cbie_backwards (_get_SEnvcfg_CBIE (← readReg senvcfg)))
    else (encdec_cbie_backwards (_get_MEnvcfg_CBIE (← readReg menvcfg))) ) : SailM cbie )
  match (p, mCBIE, sCBIE) with
  | (Machine, _, _) => (pure CBOP_INVAL_INVAL)
  | (_, CBIE_ILLEGAL, _) => (pure CBOP_ILLEGAL)
  | (User, _, CBIE_ILLEGAL) => (pure CBOP_ILLEGAL)
  | (_, CBIE_EXEC_FLUSH, _) => (pure CBOP_INVAL_FLUSH)
  | (User, _, CBIE_EXEC_FLUSH) => (pure CBOP_INVAL_FLUSH)
  | _ => (pure CBOP_INVAL_INVAL)

def process_clean_inval (rs1 : regidx) (cbop : cbop_zicbom) : SailM ExecutionResult := do
  let rs1_val ← do (rX_bits rs1)
  let cache_block_size_exp := (plat_cache_block_size_exp ())
  let cache_block_size := (2 ^i cache_block_size_exp)
  let negative_offset :=
    ((rs1_val &&& (Complement.complement
          (zero_extend (m := ((2 ^i 3) *i 8)) (ones (n := cache_block_size_exp))))) - rs1_val)
  match (← (ext_data_get_addr rs1 negative_offset (Read Data) cache_block_size)) with
  | .Ext_DataAddr_Error e => (pure (Ext_DataAddr_Check_Failure e))
  | .Ext_DataAddr_OK vaddr =>
    (do
      let res ← (( do
        match (← (translateAddr vaddr (Read Data))) with
        | .TR_Address (paddr, _) =>
          (do
            let ep ← do
              (effectivePrivilege (Read Data) (← readReg mstatus) (← readReg cur_privilege))
            let exc_read ← do (phys_access_check (Read Data) ep paddr cache_block_size)
            let exc_write ← do (phys_access_check (Write Data) ep paddr cache_block_size)
            match (exc_read, exc_write) with
            | (.some exc_read, .some exc_write) => (pure (some exc_write))
            | _ => (pure none))
        | .TR_Failure (e, _) => (pure (some e)) ) : SailM (Option ExceptionType) )
      match res with
      | none => (pure RETIRE_SUCCESS)
      | .some e =>
        (do
          let e ← (( do
            match e with
            | .E_Load_Access_Fault () => (pure (E_SAMO_Access_Fault ()))
            | .E_SAMO_Access_Fault () => (pure (E_SAMO_Access_Fault ()))
            | .E_Load_Page_Fault () => (pure (E_SAMO_Page_Fault ()))
            | .E_SAMO_Page_Fault () => (pure (E_SAMO_Page_Fault ()))
            | _ =>
              (internal_error "riscv_insts_zicbom.sail" 125
                "unexpected exception for cmo.clean/inval") ) : SailM ExceptionType )
          (pure (Memory_Exception ((sub_virtaddr_xlenbits vaddr negative_offset), e)))))

