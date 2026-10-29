module

public import FV.Backend.Proof.LowerLoopCtxT
public import FV.Compile.SubsetTF

public section

/-!
# The supported instructions with the proven float operations (S11f, #35)

`InstScopeTF ctx`: every instruction of `ctx` is in `Compile.instETF` (the typed movement scope,
the S11f float arithmetic and rounding, the saturating and `from` conversions, the scalar
`fcmp`). It is the scope
premise of the typed rule contexts (`CtxT.scope`) and of the typed shapes with typed `try_call`s
(`Driver.LowerShapeTC.scope`); `InstScopeT` (the movement scope alone) gives it
(`InstScopeT.toTF`). `Driver.instScopeOkF` decides it (`instScopeOkF_sound`,
`instScopeOkF_complete`).
-/

namespace Backend.Proof

open Backend

/-- **The supported instructions of a float-capable context with the proven float
operations**: every instruction of `ctx` is in `Compile.instETF`. -/
def InstScopeTF (ctx : Ctx) : Prop :=
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
    info.clif = some inst → Compile.instETF inst = true

/-- The typed movement scope's instructions are among them. -/
theorem InstScopeT.toTF {ctx : Ctx} (h : InstScopeT ctx) : InstScopeTF ctx :=
  fun ii info inst hi hc => Compile.instETF_of_instET (h ii info inst hi hc)

end Backend.Proof

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- `InstScopeTF ctx`, decided. -/
def instScopeOkF (ctx : Ctx) : Bool :=
  ctx.insts.toList.all fun info => match info.clif with
    | some i => Compile.instETF i
    | none => true

theorem instScopeOkF_sound {ctx : Ctx} (h : instScopeOkF ctx = true) : InstScopeTF ctx := by
  intro ii info inst hi hc
  have := List.all_eq_true.mp h info (by rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? hi)
  simpa [hc] using this

theorem instScopeOkF_complete {ctx : Ctx} (h : InstScopeTF ctx) : instScopeOkF ctx = true := by
  refine List.all_eq_true.mpr fun info hi => ?_
  obtain ⟨ii, hii, e⟩ := List.getElem_of_mem hi
  have hget : ctx.insts[ii]? = some info := by
    rw [← Array.getElem?_toList, List.getElem?_eq_getElem hii, e]
  split
  · exact h ii info _ hget ‹_›
  · rfl

end Backend.Proof.Driver
