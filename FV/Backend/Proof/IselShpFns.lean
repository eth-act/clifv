import FV.Backend.Proof.IselCovFns

/-!
# Control shapes of the ISLE lowering (V4): the transfer functions

The control-shape analysis is V3's abstract interpreter (`IselCovCheck`, domain `AW`) with a
stronger precondition and more oracles:

* `apreS`: V3's `apre`, and an `emit`ted instruction that is a control form has its shape
  (`ctlA`: a `CondBr`/`TrapIf` on a condition or on an int vreg, a `TestBitAndBranch` on an int
  vreg, `Udf`, `EmitIsland`, `Jump`; the other control forms are emitted only by the oracles
  and the hand-checked root rules); `gen_return` returns int vregs;
* `aOracleS`: V3's `aOracle`, and the helpers whose control form has fresh defs
  (`load_ext_name_got`, `load_ext_name_near`, `atomic_rmw_loop`, `atomic_cas_loop`,
  `elf_tls_get_addr`), on int-vreg operands: an int vreg.
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Isle Isle.Aarch64

/-- A `CondBrKind` on a condition or on an int vreg. -/
def kindA1 : AW → Bool
  | .data _ k (r :: _) =>
    if k == VIdx.CondBrKind.Zero || k == VIdx.CondBrKind.NotZero then r.isV
    else k == VIdx.CondBrKind.Cond
  | .data _ k [] => k == VIdx.CondBrKind.Cond
  | _ => false

/-- `kindA1` of every alternative. -/
def kindA : AW → Bool
  | .alts as => !as.isEmpty && as.all kindA1
  | a => kindA1 a

/-- The control forms with defs (calls, `JTSequence`, the `LoadExtName`s, the LL/SC loops,
`ElfTlsGetAddr`): not checked here. -/
def defCtl : List Nat :=
  [VIdx.MInst.Call, VIdx.MInst.CallInd, VIdx.MInst.JTSequence, VIdx.MInst.LoadExtNameGot,
   VIdx.MInst.LoadExtNameNear, VIdx.MInst.AtomicRMWLoop, VIdx.MInst.AtomicCASLoop,
   VIdx.MInst.ElfTlsGetAddr]

/-- The shape check of an `MInst` of variant `k` with fields `fs`. -/
def ctl1 (k : Nat) (fs : List AW) : Bool :=
  if k == VIdx.MInst.CondBr then
    match fs with
    | [_, _, kd] => kindA kd
    | _ => false
  else if k == VIdx.MInst.TrapIf then
    match fs with
    | [kd, _] => kindA kd
    | _ => false
  else if k == VIdx.MInst.TestBitAndBranch then
    match fs with
    | [_, _, _, rn, _] => rn.isV
    | _ => false
  else !defCtl.contains k

/-- `ctl1` of an `MInst` value (of every alternative). -/
def ctlA1 : AW → Bool
  | .data _ k fs => ctl1 k fs
  | _ => false

/-- **The shape check of an `emit`ted instruction.** -/
def ctlA : AW → Bool
  | .alts as => !as.isEmpty && as.all ctlA1
  | a => ctlA1 a

/-- **Preconditions** of extern constructor calls: V3's, an `emit`ted control form has its shape,
`gen_return` returns int vregs. -/
def apreS (id : TermId) (as : List AW) : Bool :=
  apre id as &&
  if id == TId.emit then
    match as with
    | [a] => ctlA a
    | _ => false
  else if id == TId.gen_return then
    match as with
    | [a] => (AW.deep a).1 &&& 14 == 0
    | _ => false
  else true

/-- The helpers emitting a control form with fresh defs, by their int-vreg operands. -/
def ctlOracle (t : TermId) (as : List AW) : Bool :=
  if t == TId.load_ext_name_got || t == TId.load_ext_name_near || t == TId.elf_tls_get_addr then true
  else if t == TId.atomic_rmw_loop then
    match as with
    | [_, a, b, _, _] => a.isV && b.isV
    | _ => false
  else if t == TId.atomic_cas_loop then
    match as with
    | [a, b, c, _, _] => a.isV && b.isV && c.isV
    | _ => false
  else false

/-- **Oracles**: `operand_size`, and the helpers emitting a control form with fresh defs. -/
def aOracleS (t : TermId) (as : List AW) : Option AW :=
  match aOracle t as with
  | some a => some a
  | none => if ctlOracle t as then some (.reg 1) else none

/-- The root rules checked by hand, not by the abstract interpreter: the calls (`lower` rules
1031–1033) and `try_call`s (`lower_branch` rules 1034–1036), and `br_table` (1140). -/
def shpHandIds : List Nat := [1031, 1032, 1033, 1034, 1035, 1036, 1140]

end Backend.Proof.Cov
