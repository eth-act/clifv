import FV.Backend.Proof.IselCovTFns
import FV.Backend.Proof.IselShpFns

/-!
# Control shapes of the typed ISLE lowering: the transfer functions (S11 #35)

`IselShpFns` over the typed domain `AT` (`IselCovTFns`): the typed coverage interpreter with a
stronger precondition and more oracles.

* `apreST`: the typed `apre`, and an `emit`ted control form has its shape (`ctlAT`: a
  `CondBr`/`TrapIf` on a condition or on an int vreg, a `TestBitAndBranch` on an int vreg, not a
  control form with defs); `gen_return` returns vregs (of either class: their `Rets` pairs them
  with the return registers of their classes, `rets_shapeT`);
* `aOracleST`: the typed `aOracle`, and the helpers whose control form has fresh defs, on
  int-vreg operands: an int vreg.
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Isle Isle.Aarch64
open Backend.Proof.Cov (defCtl shpHandIds)

/-- A `CondBrKind` on a condition or on an int vreg. -/
def kindAT1 : AT → Bool
  | .data _ k (r :: _) =>
    if k == VIdx.CondBrKind.Zero || k == VIdx.CondBrKind.NotZero then r.isV
    else k == VIdx.CondBrKind.Cond
  | .data _ k [] => k == VIdx.CondBrKind.Cond
  | _ => false

/-- `kindAT1` of every alternative. -/
def kindAT : AT → Bool
  | .alts as => !as.isEmpty && as.all kindAT1
  | a => kindAT1 a

/-- The shape check of an `MInst` of variant `k` with fields `fs`. -/
def ctlT1 (k : Nat) (fs : List AT) : Bool :=
  if k == VIdx.MInst.CondBr then
    match fs with
    | [_, _, kd] => kindAT kd
    | _ => false
  else if k == VIdx.MInst.TrapIf then
    match fs with
    | [kd, _] => kindAT kd
    | _ => false
  else if k == VIdx.MInst.TestBitAndBranch then
    match fs with
    | [_, _, _, rn, _] => rn.isV
    | _ => false
  else !defCtl.contains k

/-- `ctlT1` of an `MInst` value. -/
def ctlAT1 : AT → Bool
  | .data _ k fs => ctlT1 k fs
  | _ => false

/-- **The shape check of an `emit`ted instruction.** -/
def ctlAT : AT → Bool
  | .alts as => !as.isEmpty && as.all ctlAT1
  | a => ctlAT1 a

/-- **Preconditions** of extern constructor calls: the typed ones, an `emit`ted control form
has its shape; no `gen_return` call (#587: `gen_return` returns an `sret` function's struct
pointer in x8 whatever its vreg's class, and only the entry block's typing, `EntryClassOk`, makes
that vreg an integer one: the `return` rule is checked by hand, `IselShpTRet`, so the table
covers the other roots, which reach no `gen_return`). -/
def apreST (id : TermId) (as : List AT) : Bool :=
  apre id as &&
  if id == TId.emit then
    match as with
    | [a] => ctlAT a
    | _ => false
  else id != TId.gen_return

/-- The helpers emitting a control form with fresh defs, by their int-vreg operands. -/
def ctlOracleT (t : TermId) (as : List AT) : Bool :=
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

/-- **Oracles**: the typed ones, and the helpers emitting a control form with fresh defs. -/
def aOracleST (t : TermId) (as : List AT) : Option AT :=
  match aOracle t as with
  | some a => some a
  | none => if ctlOracleT t as then some (.reg 1) else none

end Backend.Proof.CovT
