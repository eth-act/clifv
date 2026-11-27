import FV.E2E.PoolRefinesFP
import FV.E2E.DeadCleanupT
import FV.E2E.DeadCleanupGuardedFP

/-!
# The literal-pool load of the value semantics (#1002 part 2)

The value semantics of the dead-cleanup route (`valueSem`) and its guarded form (`valueSemGF`)
refine the literal-pool load (`PoolRefinesFP`): `poolRefinesFP_valueSem`,
`poolRefinesFP_valueSemGF`. Since #1181 the literal-pool load is a pure form (`pureForm`), so both
run it by its specification (`mspec`'s literal-pool clause, `poolVal`: the entry's value, the
world unchanged). `memRefinesFP_valueSem`, `memRefinesFP_valueSemGF` and the definitions are
unchanged.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **`valueSem` refines the literal-pool load** (`PoolRefinesFP`: it is `mspec` there). -/
theorem poolRefinesFP_valueSem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    PoolRefinesFP F (valueSem F ctx X) := by
  intro sz d v fl w hsz
  exact ⟨w, by simp [valueSem, specForm, pureForm, mspec, hsz, poolVal], SameWorld.refl F w⟩

/-- **`valueSemGF` refines the literal-pool load** (`PoolRefinesFP`: it is `mspec` there). -/
theorem poolRefinesFP_valueSemGF {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {Rd : BitVec 64 → Prop} {syms : String → Option Nat} {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {sp0 : BitVec 64}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} :
    PoolRefinesFP F (valueSemGF F ctx X Rd syms exts sigs sp0 Pc) := by
  intro sz d v fl w hsz
  exact ⟨w, by simp [valueSemGF, specForm, pureForm, mspec, hsz, poolVal], SameWorld.refl F w⟩

end E2E
