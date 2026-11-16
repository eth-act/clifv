import FV.E2E.PoolRefinesFP
import FV.E2E.DeadCleanupT
import FV.E2E.DeadCleanupGuardedFP

/-!
# The literal-pool load of the value semantics (#1002 part 2)

The value semantics of the dead-cleanup route (`valueSem`) and its guarded form (`valueSemGF`)
are `csem` and `csemGF` on the float loads (they are not pure forms), so they refine the
literal-pool load (`PoolRefinesFP`): `poolRefinesFP_valueSem`, `poolRefinesFP_valueSemGF`.
`memRefinesFP_valueSem`, `memRefinesFP_valueSemGF` and the definitions are unchanged.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **`valueSem` refines the literal-pool load** (`PoolRefinesFP`: it is `csem` there). -/
theorem poolRefinesFP_valueSem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    PoolRefinesFP F (valueSem F ctx X) := by
  intro sz d v fl w hsz
  obtain ⟨w', e, hw⟩ := poolRefinesFP_csem F ctx X sz d v fl w hsz
  exact ⟨w', by simp only [valueSem, specForm, pureForm, cmpForm, Bool.false_or]; exact e, hw⟩

/-- **`valueSemGF` refines the literal-pool load** (`PoolRefinesFP`: it is `csemGF` there). -/
theorem poolRefinesFP_valueSemGF {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {Rd : BitVec 64 → Prop} {syms : String → Option Nat} {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {sp0 : BitVec 64}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} :
    PoolRefinesFP F (valueSemGF F ctx X Rd syms exts sigs sp0 Pc) := by
  intro sz d v fl w hsz
  obtain ⟨w', e, hw⟩ := poolRefinesFP_csemGF (F := F) (ctx := ctx) (X := X) (Rd := Rd)
    (syms := syms) (exts := exts) (sigs := sigs) (sp0 := sp0) (Pc := Pc) sz d v fl w hsz
  exact ⟨w', by simp only [valueSemGF, specForm, pureForm, cmpForm, Bool.false_or]; exact e, hw⟩

end E2E
