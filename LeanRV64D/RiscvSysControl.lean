import LeanRV64D.RiscvSmcntrpmf

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

def csrAccess (csr : (BitVec 12)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb csr 11 10)

def csrPriv (csr : (BitVec 12)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb csr 9 8)

def check_CSR_priv (csr : (BitVec 12)) (p : Privilege) : Bool :=
  (zopz0zKzJ_u (privLevel_to_bits p) (csrPriv csr))

/-- Type quantifiers: k_ex344277# : Bool -/
def check_CSR_access (csr : (BitVec 12)) (isWrite : Bool) : Bool :=
  (not (Bool.and isWrite (BEq.beq (csrAccess csr) (0b11 : (BitVec 2)))))

def check_TVM_SATP (csr : (BitVec 12)) (p : Privilege) : SailM Bool := do
  (pure (not
      (Bool.and (BEq.beq csr (0x180 : (BitVec 12)))
        (Bool.and (BEq.beq p Supervisor)
          (BEq.beq (_get_Mstatus_TVM (← readReg mstatus)) (0b1 : (BitVec 1)))))))

def feature_enabled_for_priv (p : Privilege) (machine_enable_bit : (BitVec 1)) (supervisor_enable_bit : (BitVec 1)) : SailM Bool := do
  match p with
  | Machine => (pure true)
  | Supervisor => (pure (BEq.beq machine_enable_bit 1#1))
  | User => (pure (Bool.and (BEq.beq machine_enable_bit 1#1)
        (Bool.or (not (← (currentlyEnabled Ext_S))) (BEq.beq supervisor_enable_bit 1#1))))

def check_Counteren (csr : (BitVec 12)) (p : Privilege) : SailM Bool := do
  bif (Bool.or (zopz0zI_u csr (0xC00 : (BitVec 12))) (zopz0zI_u (0xC1F : (BitVec 12)) csr))
  then (pure true)
  else
    (do
      let index := (BitVec.toNat (Sail.BitVec.extractLsb csr 4 0))
      (feature_enabled_for_priv p (BitVec.access (← readReg mcounteren) index)
        (BitVec.access (← readReg scounteren) index)))

def check_Stimecmp (csr : (BitVec 12)) (p : Privilege) : SailM Bool := do
  bif (Bool.and (bne csr (0x14D : (BitVec 12))) (bne csr (0x15D : (BitVec 12))))
  then (pure true)
  else
    (pure (Bool.or (BEq.beq p Machine)
        (Bool.and (BEq.beq p Supervisor)
          (Bool.and (BEq.beq (_get_Counteren_TM (← readReg mcounteren)) (0b1 : (BitVec 1)))
            (BEq.beq (_get_MEnvcfg_STCE (← readReg menvcfg)) (0b1 : (BitVec 1)))))))

/-- Type quantifiers: k_ex344364# : Bool -/
def check_seed_CSR (csr : (BitVec 12)) (p : Privilege) (isWrite : Bool) : Bool :=
  bif (not (BEq.beq csr (0x015 : (BitVec 12))))
  then true
  else
    (bif (not isWrite)
    then false
    else
      (match p with
      | Machine => true
      | Supervisor => false
      | User => false))

def is_CSR_defined (b__0 : (BitVec 12)) : SailM Bool := do
  bif (BEq.beq b__0 (0x301 : (BitVec 12)))
  then (pure true)
  else
    (do
      bif (BEq.beq b__0 (0x300 : (BitVec 12)))
      then (pure true)
      else
        (do
          bif (BEq.beq b__0 (0x310 : (BitVec 12)))
          then (pure (BEq.beq xlen 32))
          else
            (do
              bif (BEq.beq b__0 (0x30A : (BitVec 12)))
              then (currentlyEnabled Ext_U)
              else
                (do
                  bif (BEq.beq b__0 (0x31A : (BitVec 12)))
                  then (pure (Bool.and (← (currentlyEnabled Ext_U)) (BEq.beq xlen 32)))
                  else
                    (do
                      bif (BEq.beq b__0 (0x10A : (BitVec 12)))
                      then (currentlyEnabled Ext_S)
                      else
                        (do
                          bif (BEq.beq b__0 (0x304 : (BitVec 12)))
                          then (pure true)
                          else
                            (do
                              bif (BEq.beq b__0 (0x344 : (BitVec 12)))
                              then (pure true)
                              else
                                (do
                                  bif (BEq.beq b__0 (0x302 : (BitVec 12)))
                                  then (currentlyEnabled Ext_S)
                                  else
                                    (do
                                      bif (BEq.beq b__0 (0x312 : (BitVec 12)))
                                      then
                                        (pure (Bool.and (← (currentlyEnabled Ext_S))
                                            (BEq.beq xlen 32)))
                                      else
                                        (do
                                          bif (BEq.beq b__0 (0x303 : (BitVec 12)))
                                          then (currentlyEnabled Ext_S)
                                          else
                                            (do
                                              bif (BEq.beq b__0 (0x342 : (BitVec 12)))
                                              then (pure true)
                                              else
                                                (do
                                                  bif (BEq.beq b__0 (0x343 : (BitVec 12)))
                                                  then (pure true)
                                                  else
                                                    (do
                                                      bif (BEq.beq b__0 (0x340 : (BitVec 12)))
                                                      then (pure true)
                                                      else
                                                        (do
                                                          bif (BEq.beq b__0 (0x106 : (BitVec 12)))
                                                          then (currentlyEnabled Ext_S)
                                                          else
                                                            (do
                                                              bif (BEq.beq b__0
                                                                   (0x306 : (BitVec 12)))
                                                              then (currentlyEnabled Ext_U)
                                                              else
                                                                (do
                                                                  bif (BEq.beq b__0
                                                                       (0x320 : (BitVec 12)))
                                                                  then (pure true)
                                                                  else
                                                                    (do
                                                                      bif (BEq.beq b__0
                                                                           (0xF11 : (BitVec 12)))
                                                                      then (pure true)
                                                                      else
                                                                        (do
                                                                          bif (BEq.beq b__0
                                                                               (0xF12 : (BitVec 12)))
                                                                          then (pure true)
                                                                          else
                                                                            (do
                                                                              bif (BEq.beq b__0
                                                                                   (0xF13 : (BitVec 12)))
                                                                              then (pure true)
                                                                              else
                                                                                (do
                                                                                  bif (BEq.beq b__0
                                                                                       (0xF14 : (BitVec 12)))
                                                                                  then (pure true)
                                                                                  else
                                                                                    (do
                                                                                      bif (BEq.beq
                                                                                           b__0
                                                                                           (0xF15 : (BitVec 12)))
                                                                                      then
                                                                                        (pure true)
                                                                                      else
                                                                                        (do
                                                                                          bif (BEq.beq
                                                                                               b__0
                                                                                               (0x100 : (BitVec 12)))
                                                                                          then
                                                                                            (currentlyEnabled
                                                                                              Ext_S)
                                                                                          else
                                                                                            (do
                                                                                              bif (BEq.beq
                                                                                                   b__0
                                                                                                   (0x144 : (BitVec 12)))
                                                                                              then
                                                                                                (currentlyEnabled
                                                                                                  Ext_S)
                                                                                              else
                                                                                                (do
                                                                                                  bif (BEq.beq
                                                                                                       b__0
                                                                                                       (0x104 : (BitVec 12)))
                                                                                                  then
                                                                                                    (currentlyEnabled
                                                                                                      Ext_S)
                                                                                                  else
                                                                                                    (do
                                                                                                      bif (BEq.beq
                                                                                                           b__0
                                                                                                           (0x140 : (BitVec 12)))
                                                                                                      then
                                                                                                        (currentlyEnabled
                                                                                                          Ext_S)
                                                                                                      else
                                                                                                        (do
                                                                                                          bif (BEq.beq
                                                                                                               b__0
                                                                                                               (0x142 : (BitVec 12)))
                                                                                                          then
                                                                                                            (currentlyEnabled
                                                                                                              Ext_S)
                                                                                                          else
                                                                                                            (do
                                                                                                              bif (BEq.beq
                                                                                                                   b__0
                                                                                                                   (0x143 : (BitVec 12)))
                                                                                                              then
                                                                                                                (currentlyEnabled
                                                                                                                  Ext_S)
                                                                                                              else
                                                                                                                (do
                                                                                                                  bif (BEq.beq
                                                                                                                       b__0
                                                                                                                       (0x7A0 : (BitVec 12)))
                                                                                                                  then
                                                                                                                    (pure true)
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      bif (BEq.beq
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             b__0
                                                                                                                             11
                                                                                                                             4)
                                                                                                                           (0x3A : (BitVec 8)))
                                                                                                                      then
                                                                                                                        (let idx : (BitVec 4) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            b__0
                                                                                                                            3
                                                                                                                            0)
                                                                                                                        (pure (Bool.and
                                                                                                                            ((sys_pmp_count
                                                                                                                                ()) >b (BitVec.toNat
                                                                                                                                idx))
                                                                                                                            (Bool.or
                                                                                                                              (BEq.beq
                                                                                                                                (BitVec.access
                                                                                                                                  idx
                                                                                                                                  0)
                                                                                                                                0#1)
                                                                                                                              (BEq.beq
                                                                                                                                xlen
                                                                                                                                32)))))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          bif (BEq.beq
                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                 b__0
                                                                                                                                 11
                                                                                                                                 4)
                                                                                                                               (0x3B : (BitVec 8)))
                                                                                                                          then
                                                                                                                            (let idx : (BitVec 4) :=
                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                b__0
                                                                                                                                3
                                                                                                                                0)
                                                                                                                            (pure ((sys_pmp_count
                                                                                                                                  ()) >b (BitVec.toNat
                                                                                                                                  ((0b00 : (BitVec 2)) ++ idx)))))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              bif (BEq.beq
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     b__0
                                                                                                                                     11
                                                                                                                                     4)
                                                                                                                                   (0x3C : (BitVec 8)))
                                                                                                                              then
                                                                                                                                (let idx : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    b__0
                                                                                                                                    3
                                                                                                                                    0)
                                                                                                                                (pure ((sys_pmp_count
                                                                                                                                      ()) >b (BitVec.toNat
                                                                                                                                      ((0b01 : (BitVec 2)) ++ idx)))))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  bif (BEq.beq
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         b__0
                                                                                                                                         11
                                                                                                                                         4)
                                                                                                                                       (0x3D : (BitVec 8)))
                                                                                                                                  then
                                                                                                                                    (let idx : (BitVec 4) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        b__0
                                                                                                                                        3
                                                                                                                                        0)
                                                                                                                                    (pure ((sys_pmp_count
                                                                                                                                          ()) >b (BitVec.toNat
                                                                                                                                          ((0b10 : (BitVec 2)) ++ idx)))))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      bif (BEq.beq
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             b__0
                                                                                                                                             11
                                                                                                                                             4)
                                                                                                                                           (0x3E : (BitVec 8)))
                                                                                                                                      then
                                                                                                                                        (let idx : (BitVec 4) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            b__0
                                                                                                                                            3
                                                                                                                                            0)
                                                                                                                                        (pure ((sys_pmp_count
                                                                                                                                              ()) >b (BitVec.toNat
                                                                                                                                              ((0b11 : (BitVec 2)) ++ idx)))))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          bif (BEq.beq
                                                                                                                                               b__0
                                                                                                                                               (0x008 : (BitVec 12)))
                                                                                                                                          then
                                                                                                                                            (currentlyEnabled
                                                                                                                                              Ext_V)
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              bif (BEq.beq
                                                                                                                                                   b__0
                                                                                                                                                   (0x009 : (BitVec 12)))
                                                                                                                                              then
                                                                                                                                                (currentlyEnabled
                                                                                                                                                  Ext_V)
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  bif (BEq.beq
                                                                                                                                                       b__0
                                                                                                                                                       (0x00A : (BitVec 12)))
                                                                                                                                                  then
                                                                                                                                                    (currentlyEnabled
                                                                                                                                                      Ext_V)
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      bif (BEq.beq
                                                                                                                                                           b__0
                                                                                                                                                           (0x00F : (BitVec 12)))
                                                                                                                                                      then
                                                                                                                                                        (currentlyEnabled
                                                                                                                                                          Ext_V)
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          bif (BEq.beq
                                                                                                                                                               b__0
                                                                                                                                                               (0xC20 : (BitVec 12)))
                                                                                                                                                          then
                                                                                                                                                            (currentlyEnabled
                                                                                                                                                              Ext_V)
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              bif (BEq.beq
                                                                                                                                                                   b__0
                                                                                                                                                                   (0xC21 : (BitVec 12)))
                                                                                                                                                              then
                                                                                                                                                                (currentlyEnabled
                                                                                                                                                                  Ext_V)
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  bif (BEq.beq
                                                                                                                                                                       b__0
                                                                                                                                                                       (0xC22 : (BitVec 12)))
                                                                                                                                                                  then
                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                      Ext_V)
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      bif (BEq.beq
                                                                                                                                                                           b__0
                                                                                                                                                                           (0x105 : (BitVec 12)))
                                                                                                                                                                      then
                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                          Ext_S)
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          bif (BEq.beq
                                                                                                                                                                               b__0
                                                                                                                                                                               (0x141 : (BitVec 12)))
                                                                                                                                                                          then
                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                              Ext_S)
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              bif (BEq.beq
                                                                                                                                                                                   b__0
                                                                                                                                                                                   (0x305 : (BitVec 12)))
                                                                                                                                                                              then
                                                                                                                                                                                (pure true)
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  bif (BEq.beq
                                                                                                                                                                                       b__0
                                                                                                                                                                                       (0x341 : (BitVec 12)))
                                                                                                                                                                                  then
                                                                                                                                                                                    (pure true)
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      bif (Bool.and
                                                                                                                                                                                           (BEq.beq
                                                                                                                                                                                             (Sail.BitVec.extractLsb
                                                                                                                                                                                               b__0
                                                                                                                                                                                               11
                                                                                                                                                                                               5)
                                                                                                                                                                                             (0b0011001 : (BitVec 7)))
                                                                                                                                                                                           (let index : (BitVec 5) :=
                                                                                                                                                                                             (Sail.BitVec.extractLsb
                                                                                                                                                                                               b__0
                                                                                                                                                                                               4
                                                                                                                                                                                               0)
                                                                                                                                                                                           ((BitVec.toNat
                                                                                                                                                                                               index) ≥b 3) : Bool))
                                                                                                                                                                                      then
                                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                                          Ext_Zihpm)
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          bif (Bool.and
                                                                                                                                                                                               (BEq.beq
                                                                                                                                                                                                 (Sail.BitVec.extractLsb
                                                                                                                                                                                                   b__0
                                                                                                                                                                                                   11
                                                                                                                                                                                                   5)
                                                                                                                                                                                                 (0b1011000 : (BitVec 7)))
                                                                                                                                                                                               (let index : (BitVec 5) :=
                                                                                                                                                                                                 (Sail.BitVec.extractLsb
                                                                                                                                                                                                   b__0
                                                                                                                                                                                                   4
                                                                                                                                                                                                   0)
                                                                                                                                                                                               ((BitVec.toNat
                                                                                                                                                                                                   index) ≥b 3) : Bool))
                                                                                                                                                                                          then
                                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                                              Ext_Zihpm)
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              bif (Bool.and
                                                                                                                                                                                                   (BEq.beq
                                                                                                                                                                                                     (Sail.BitVec.extractLsb
                                                                                                                                                                                                       b__0
                                                                                                                                                                                                       11
                                                                                                                                                                                                       5)
                                                                                                                                                                                                     (0b1011100 : (BitVec 7)))
                                                                                                                                                                                                   (let index : (BitVec 5) :=
                                                                                                                                                                                                     (Sail.BitVec.extractLsb
                                                                                                                                                                                                       b__0
                                                                                                                                                                                                       4
                                                                                                                                                                                                       0)
                                                                                                                                                                                                   ((BitVec.toNat
                                                                                                                                                                                                       index) ≥b 3) : Bool))
                                                                                                                                                                                              then
                                                                                                                                                                                                (pure (Bool.and
                                                                                                                                                                                                    (← (currentlyEnabled
                                                                                                                                                                                                        Ext_Zihpm))
                                                                                                                                                                                                    (BEq.beq
                                                                                                                                                                                                      xlen
                                                                                                                                                                                                      32)))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  bif (Bool.and
                                                                                                                                                                                                       (BEq.beq
                                                                                                                                                                                                         (Sail.BitVec.extractLsb
                                                                                                                                                                                                           b__0
                                                                                                                                                                                                           11
                                                                                                                                                                                                           5)
                                                                                                                                                                                                         (0b1100000 : (BitVec 7)))
                                                                                                                                                                                                       (let index : (BitVec 5) :=
                                                                                                                                                                                                         (Sail.BitVec.extractLsb
                                                                                                                                                                                                           b__0
                                                                                                                                                                                                           4
                                                                                                                                                                                                           0)
                                                                                                                                                                                                       ((BitVec.toNat
                                                                                                                                                                                                           index) ≥b 3) : Bool))
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (pure (Bool.and
                                                                                                                                                                                                        (← (currentlyEnabled
                                                                                                                                                                                                            Ext_Zihpm))
                                                                                                                                                                                                        (← (currentlyEnabled
                                                                                                                                                                                                            Ext_U))))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      bif (Bool.and
                                                                                                                                                                                                           (BEq.beq
                                                                                                                                                                                                             (Sail.BitVec.extractLsb
                                                                                                                                                                                                               b__0
                                                                                                                                                                                                               11
                                                                                                                                                                                                               5)
                                                                                                                                                                                                             (0b1100100 : (BitVec 7)))
                                                                                                                                                                                                           (let index : (BitVec 5) :=
                                                                                                                                                                                                             (Sail.BitVec.extractLsb
                                                                                                                                                                                                               b__0
                                                                                                                                                                                                               4
                                                                                                                                                                                                               0)
                                                                                                                                                                                                           ((BitVec.toNat
                                                                                                                                                                                                               index) ≥b 3) : Bool))
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (pure (Bool.and
                                                                                                                                                                                                            (← (currentlyEnabled
                                                                                                                                                                                                                Ext_Zihpm))
                                                                                                                                                                                                            (Bool.and
                                                                                                                                                                                                              (← (currentlyEnabled
                                                                                                                                                                                                                  Ext_U))
                                                                                                                                                                                                              (BEq.beq
                                                                                                                                                                                                                xlen
                                                                                                                                                                                                                32))))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          bif (Bool.and
                                                                                                                                                                                                               (BEq.beq
                                                                                                                                                                                                                 (Sail.BitVec.extractLsb
                                                                                                                                                                                                                   b__0
                                                                                                                                                                                                                   11
                                                                                                                                                                                                                   5)
                                                                                                                                                                                                                 (0b0111001 : (BitVec 7)))
                                                                                                                                                                                                               (let index : (BitVec 5) :=
                                                                                                                                                                                                                 (Sail.BitVec.extractLsb
                                                                                                                                                                                                                   b__0
                                                                                                                                                                                                                   4
                                                                                                                                                                                                                   0)
                                                                                                                                                                                                               ((BitVec.toNat
                                                                                                                                                                                                                   index) ≥b 3) : Bool))
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (pure (Bool.and
                                                                                                                                                                                                                (← (currentlyEnabled
                                                                                                                                                                                                                    Ext_Sscofpmf))
                                                                                                                                                                                                                (BEq.beq
                                                                                                                                                                                                                  xlen
                                                                                                                                                                                                                  32)))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              bif (BEq.beq
                                                                                                                                                                                                                   b__0
                                                                                                                                                                                                                   (0xDA0 : (BitVec 12)))
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (pure (Bool.and
                                                                                                                                                                                                                    (← (currentlyEnabled
                                                                                                                                                                                                                        Ext_Sscofpmf))
                                                                                                                                                                                                                    (← (currentlyEnabled
                                                                                                                                                                                                                        Ext_S))))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  bif (BEq.beq
                                                                                                                                                                                                                       b__0
                                                                                                                                                                                                                       (0x015 : (BitVec 12)))
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                      Ext_Zkr)
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      bif (BEq.beq
                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                           (0xC00 : (BitVec 12)))
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (currentlyEnabled
                                                                                                                                                                                                                          Ext_Zicntr)
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          bif (BEq.beq
                                                                                                                                                                                                                               b__0
                                                                                                                                                                                                                               (0xC01 : (BitVec 12)))
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                                                                              Ext_Zicntr)
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              bif (BEq.beq
                                                                                                                                                                                                                                   b__0
                                                                                                                                                                                                                                   (0xC02 : (BitVec 12)))
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (currentlyEnabled
                                                                                                                                                                                                                                  Ext_Zicntr)
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  bif (BEq.beq
                                                                                                                                                                                                                                       b__0
                                                                                                                                                                                                                                       (0xC80 : (BitVec 12)))
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (pure (Bool.and
                                                                                                                                                                                                                                        (← (currentlyEnabled
                                                                                                                                                                                                                                            Ext_Zicntr))
                                                                                                                                                                                                                                        (BEq.beq
                                                                                                                                                                                                                                          xlen
                                                                                                                                                                                                                                          32)))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      bif (BEq.beq
                                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                                           (0xC81 : (BitVec 12)))
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (pure (Bool.and
                                                                                                                                                                                                                                            (← (currentlyEnabled
                                                                                                                                                                                                                                                Ext_Zicntr))
                                                                                                                                                                                                                                            (BEq.beq
                                                                                                                                                                                                                                              xlen
                                                                                                                                                                                                                                              32)))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          bif (BEq.beq
                                                                                                                                                                                                                                               b__0
                                                                                                                                                                                                                                               (0xC82 : (BitVec 12)))
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (pure (Bool.and
                                                                                                                                                                                                                                                (← (currentlyEnabled
                                                                                                                                                                                                                                                    Ext_Zicntr))
                                                                                                                                                                                                                                                (BEq.beq
                                                                                                                                                                                                                                                  xlen
                                                                                                                                                                                                                                                  32)))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              bif (BEq.beq
                                                                                                                                                                                                                                                   b__0
                                                                                                                                                                                                                                                   (0xB00 : (BitVec 12)))
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (currentlyEnabled
                                                                                                                                                                                                                                                  Ext_Zicntr)
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  bif (BEq.beq
                                                                                                                                                                                                                                                       b__0
                                                                                                                                                                                                                                                       (0xB02 : (BitVec 12)))
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                                                      Ext_Zicntr)
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      bif (BEq.beq
                                                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                                                           (0xB80 : (BitVec 12)))
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (pure (Bool.and
                                                                                                                                                                                                                                                            (← (currentlyEnabled
                                                                                                                                                                                                                                                                Ext_Zicntr))
                                                                                                                                                                                                                                                            (BEq.beq
                                                                                                                                                                                                                                                              xlen
                                                                                                                                                                                                                                                              32)))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          bif (BEq.beq
                                                                                                                                                                                                                                                               b__0
                                                                                                                                                                                                                                                               (0xB82 : (BitVec 12)))
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (pure (Bool.and
                                                                                                                                                                                                                                                                (← (currentlyEnabled
                                                                                                                                                                                                                                                                    Ext_Zicntr))
                                                                                                                                                                                                                                                                (BEq.beq
                                                                                                                                                                                                                                                                  xlen
                                                                                                                                                                                                                                                                  32)))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              bif (BEq.beq
                                                                                                                                                                                                                                                                   b__0
                                                                                                                                                                                                                                                                   (0x001 : (BitVec 12)))
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (pure (Bool.or
                                                                                                                                                                                                                                                                    (← (currentlyEnabled
                                                                                                                                                                                                                                                                        Ext_F))
                                                                                                                                                                                                                                                                    (← (currentlyEnabled
                                                                                                                                                                                                                                                                        Ext_Zfinx))))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  bif (BEq.beq
                                                                                                                                                                                                                                                                       b__0
                                                                                                                                                                                                                                                                       (0x002 : (BitVec 12)))
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (pure (Bool.or
                                                                                                                                                                                                                                                                        (← (currentlyEnabled
                                                                                                                                                                                                                                                                            Ext_F))
                                                                                                                                                                                                                                                                        (← (currentlyEnabled
                                                                                                                                                                                                                                                                            Ext_Zfinx))))
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      bif (BEq.beq
                                                                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                                                                           (0x003 : (BitVec 12)))
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (pure (Bool.or
                                                                                                                                                                                                                                                                            (← (currentlyEnabled
                                                                                                                                                                                                                                                                                Ext_F))
                                                                                                                                                                                                                                                                            (← (currentlyEnabled
                                                                                                                                                                                                                                                                                Ext_Zfinx))))
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          bif (BEq.beq
                                                                                                                                                                                                                                                                               b__0
                                                                                                                                                                                                                                                                               (0x321 : (BitVec 12)))
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                                                                                                                              Ext_Smcntrpmf)
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              bif (BEq.beq
                                                                                                                                                                                                                                                                                   b__0
                                                                                                                                                                                                                                                                                   (0x721 : (BitVec 12)))
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (pure (Bool.and
                                                                                                                                                                                                                                                                                    (← (currentlyEnabled
                                                                                                                                                                                                                                                                                        Ext_Smcntrpmf))
                                                                                                                                                                                                                                                                                    (BEq.beq
                                                                                                                                                                                                                                                                                      xlen
                                                                                                                                                                                                                                                                                      32)))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  bif (BEq.beq
                                                                                                                                                                                                                                                                                       b__0
                                                                                                                                                                                                                                                                                       (0x322 : (BitVec 12)))
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (currentlyEnabled
                                                                                                                                                                                                                                                                                      Ext_Smcntrpmf)
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      bif (BEq.beq
                                                                                                                                                                                                                                                                                           b__0
                                                                                                                                                                                                                                                                                           (0x722 : (BitVec 12)))
                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                        (pure (Bool.and
                                                                                                                                                                                                                                                                                            (← (currentlyEnabled
                                                                                                                                                                                                                                                                                                Ext_Smcntrpmf))
                                                                                                                                                                                                                                                                                            (BEq.beq
                                                                                                                                                                                                                                                                                              xlen
                                                                                                                                                                                                                                                                                              32)))
                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          bif (BEq.beq
                                                                                                                                                                                                                                                                                               b__0
                                                                                                                                                                                                                                                                                               (0x180 : (BitVec 12)))
                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                            (currentlyEnabled
                                                                                                                                                                                                                                                                                              Ext_S)
                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                            (pure false)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Type quantifiers: k_ex344840# : Bool -/
def check_CSR (csr : (BitVec 12)) (p : Privilege) (isWrite : Bool) : SailM Bool := do
  (pure (Bool.and (← (is_CSR_defined csr))
      (Bool.and (check_CSR_priv csr p)
        (Bool.and (check_CSR_access csr isWrite)
          (Bool.and (← (check_TVM_SATP csr p))
            (Bool.and (← (check_Counteren csr p))
              (Bool.and (← (check_Stimecmp csr p)) (check_seed_CSR csr p isWrite))))))))

def exception_delegatee (e : ExceptionType) (p : Privilege) : SailM Privilege := do
  let idx := (num_of_ExceptionType e)
  let super ← do (bit_to_bool (BitVec.access (← readReg medeleg) idx))
  let deleg ← do
    bif (Bool.and (← (currentlyEnabled Ext_S)) super)
    then (pure Supervisor)
    else (pure Machine)
  bif (zopz0zI_u (privLevel_to_bits deleg) (privLevel_to_bits p))
  then (pure p)
  else (pure deleg)

def findPendingInterrupt (ip : (BitVec (2 ^ 3 * 8))) : (Option InterruptType) :=
  let ip := (Mk_Minterrupts ip)
  bif (BEq.beq (_get_Minterrupts_MEI ip) (0b1 : (BitVec 1)))
  then (some I_M_External)
  else
    (bif (BEq.beq (_get_Minterrupts_MSI ip) (0b1 : (BitVec 1)))
    then (some I_M_Software)
    else
      (bif (BEq.beq (_get_Minterrupts_MTI ip) (0b1 : (BitVec 1)))
      then (some I_M_Timer)
      else
        (bif (BEq.beq (_get_Minterrupts_SEI ip) (0b1 : (BitVec 1)))
        then (some I_S_External)
        else
          (bif (BEq.beq (_get_Minterrupts_SSI ip) (0b1 : (BitVec 1)))
          then (some I_S_Software)
          else
            (bif (BEq.beq (_get_Minterrupts_STI ip) (0b1 : (BitVec 1)))
            then (some I_S_Timer)
            else none)))))

def getPendingSet (priv : Privilege) : SailM (Option ((BitVec (2 ^ 3 * 8)) × Privilege)) := do
  assert (Bool.or (← (currentlyEnabled Ext_S))
    (BEq.beq (← readReg mideleg) (zeros (n := ((2 ^i 3) *i 8))))) "riscv_sys_control.sail:137.58-137.59"
  let pending_m ← do
    (pure ((← readReg mip) &&& ((← readReg mie) &&& (Complement.complement (← readReg mideleg)))))
  let pending_s ← do (pure ((← readReg mip) &&& ((← readReg mie) &&& (← readReg mideleg))))
  let mIE ← do
    (pure (Bool.or
        (Bool.and (BEq.beq priv Machine)
          (BEq.beq (_get_Mstatus_MIE (← readReg mstatus)) (0b1 : (BitVec 1))))
        (Bool.or (BEq.beq priv Supervisor) (BEq.beq priv User))))
  let sIE ← do
    (pure (Bool.or
        (Bool.and (BEq.beq priv Supervisor)
          (BEq.beq (_get_Mstatus_SIE (← readReg mstatus)) (0b1 : (BitVec 1)))) (BEq.beq priv User)))
  bif (Bool.and mIE (bne pending_m (zeros (n := ((2 ^i 3) *i 8)))))
  then (pure (some (pending_m, Machine)))
  else
    (bif (Bool.and sIE (bne pending_s (zeros (n := ((2 ^i 3) *i 8)))))
    then (pure (some (pending_s, Supervisor)))
    else (pure none))

def shouldWakeForInterrupt (_ : Unit) : SailM Bool := do
  (pure (bne ((← readReg mip) &&& (← readReg mie)) (zeros (n := ((2 ^i 3) *i 8)))))

def dispatchInterrupt (priv : Privilege) : SailM (Option (InterruptType × Privilege)) := do
  match (← (getPendingSet priv)) with
  | none => (pure none)
  | .some (ip, p) => (match (findPendingInterrupt ip) with
    | none => (pure none)
    | .some i => (pure (some (i, p))))

def tval (excinfo : (Option (BitVec (2 ^ 3 * 8)))) : (BitVec (2 ^ 3 * 8)) :=
  match excinfo with
  | .some e => e
  | none => (zeros (n := ((2 ^i 3) *i 8)))

def rvfi_trap (_ : Unit) : Unit :=
  ()

/-- Type quantifiers: k_ex345086# : Bool -/
def trap_handler (del_priv : Privilege) (intr : Bool) (c : (BitVec 8)) (pc : (BitVec (2 ^ 3 * 8))) (info : (Option (BitVec (2 ^ 3 * 8)))) (ext : (Option Unit)) : SailM (BitVec (2 ^ 3 * 8)) := do
  let _ : Unit := (rvfi_trap ())
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
  | Machine => (do
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
      bif (get_config_print_reg ())
      then
        (pure (print_endline
            (HAppend.hAppend "CSR mstatus <- " (BitVec.toFormatted (← readReg mstatus)))))
      else (pure ())
      (prepare_trap_vector del_priv (← readReg mcause)))
  | Supervisor => (do
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
          | Machine => (internal_error "riscv_sys_control.sail" 255
              "invalid privilege for s-mode trap")))
      writeReg stval (tval info)
      writeReg sepc pc
      writeReg cur_privilege del_priv
      let _ : Unit := (handle_trap_extension del_priv pc ext)
      bif (get_config_print_reg ())
      then
        (pure (print_endline
            (HAppend.hAppend "CSR mstatus <- " (BitVec.toFormatted (← readReg mstatus)))))
      else (pure ())
      (prepare_trap_vector del_priv (← readReg scause)))
  | User => (internal_error "riscv_sys_control.sail" 269 "Invalid privilege level")

def exception_handler (cur_priv : Privilege) (ctl : ctl_result) (pc : (BitVec (2 ^ 3 * 8))) : SailM (BitVec (2 ^ 3 * 8)) := do
  match (cur_priv, ctl) with
  | (_, .CTL_TRAP e) => (do
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
  | (_, .CTL_MRET ()) => (do
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
      bif (get_config_print_reg ())
      then
        (pure (print_endline
            (HAppend.hAppend "CSR mstatus <- " (BitVec.toFormatted (← readReg mstatus)))))
      else (pure ())
      bif (get_config_print_platform ())
      then
        (pure (print_endline
            (HAppend.hAppend "ret-ing from "
              (HAppend.hAppend (privLevel_to_str prev_priv)
                (HAppend.hAppend " to " (privLevel_to_str (← readReg cur_privilege)))))))
      else (pure ())
      (prepare_xret_target Machine))
  | (_, .CTL_SRET ()) => (do
      let prev_priv ← do readReg cur_privilege
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 1 1
        (_get_Mstatus_SPIE (← readReg mstatus)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 5 5 (0b1 : (BitVec 1)))
      writeReg cur_privilege (← do
        bif (BEq.beq (_get_Mstatus_SPP (← readReg mstatus)) (0b1 : (BitVec 1)))
        then (pure Supervisor)
        else (pure User))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 8 8 (0b0 : (BitVec 1)))
      bif (bne (← readReg cur_privilege) Machine)
      then
        writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 (0b0 : (BitVec 1)))
      else (pure ())
      bif (get_config_print_reg ())
      then
        (pure (print_endline
            (HAppend.hAppend "CSR mstatus <- " (BitVec.toFormatted (← readReg mstatus)))))
      else (pure ())
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
  bif (Bool.and (hartSupports Ext_F) (hartSupports Ext_Zfinx))
  then (internal_error "riscv_sys_control.sail" 348 "F and Zfinx cannot both be enabled!")
  else (pure ())
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 5 5
    (bool_to_bits (hartSupports Ext_F)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 3 3
    (bool_to_bits (hartSupports Ext_D)))

def reset_sys (_ : Unit) : SailM Unit := do
  writeReg cur_privilege Machine
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3 (0b0 : (BitVec 1)))
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 (0b0 : (BitVec 1)))
  (reset_misa ())
  (cancel_reservation ())
  writeReg mcause (zeros (n := ((2 ^i 3) *i 8)))
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
  bif (get_config_print_reg ())
  then
    (pure (print_endline
        (HAppend.hAppend "CSR mstatus <- "
          (HAppend.hAppend (BitVec.toFormatted (← readReg mstatus))
            (HAppend.hAppend " (input: "
              (HAppend.hAppend (BitVec.toFormatted ((zeros (n := ((2 ^i 3) *i 8))) : xlenbits)) ")"))))))
  else (pure ())

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

