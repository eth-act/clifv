import FV.E2E.GuardedFP
import FV.Backend.Proof.IselFloatConstPool

/-!
# The literal-pool load of `csem` and `csemGF` (#1002 part 2)

`PoolRefinesFP F isem` (`IselFloatConstPool.lean`): `ldr s/d, <entry>` of a constant-pool entry
gives the entry's value. `csem` gives it (`mspec`'s literal-pool clause, `poolVal`, #565), and so
does the guarded semantics `csemGF` (`GuardFP` admits the literal-pool load, `fspec`'s
literal-pool clause): `poolRefinesFP_csem`, `poolRefinesFP_csemGF`. `MemRefinesFP` and its
theorems are unchanged.
-/

namespace E2E

open Backend Backend.Proof

/-- **`csem` refines the literal-pool load** (`PoolRefinesFP`). -/
theorem poolRefinesFP_csem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    PoolRefinesFP F (csem F ctx X) :=
  fun sz d v fl w hsz => ⟨w, csem_poolLoad F ctx X sz hsz d v fl w, SameWorld.refl F w⟩

section
variable {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {Rd : BitVec 64 → Prop}
  {syms : String → Option Nat} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
  {sp0 : BitVec 64}
  {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}

/-- **`csemGF` refines the literal-pool load** (`PoolRefinesFP`): `GuardFP` admits it, and it is
`csem` (well-formed worlds) or `fspec` (elsewhere), both the entry's value. -/
theorem poolRefinesFP_csemGF : PoolRefinesFP F (csemGF F ctx X Rd syms exts sigs sp0 Pc) := by
  intro sz d v fl w hsz
  have hg : GuardFP F Rd ctx.slotBase (.fpuLoad sz (.vreg d .float) (.const v) fl) [] w := by
    simp only [GuardFP]; exact hsz
  refine ⟨w, ?_, SameWorld.refl F w⟩
  simp only [csemGF, if_pos hg]
  split
  · rw [csem_poolLoad F ctx X sz hsz d v fl w]; rfl
  · simp [fspec, hsz, poolVal]

end

end E2E
