import FV.Backend.Proof.LowerLoopCtxT
import FV.Compile.SubsetTF

/-!
# The supported instructions with the proven float operations (S11f, #35)

`InstScopeTF ctx`: every instruction of `ctx` is in `Compile.instETF` (the typed movement scope,
the S11f float arithmetic and rounding, the saturating and `from` conversions, the scalar
`fcmp`). It is the scope
premise of the typed rule contexts (`CtxT.scope`) and of the typed shapes with typed `try_call`s
(`Driver.LowerShapeTC.scope`); `InstScopeT` (the movement scope alone) gives it
(`InstScopeT.toTF`). `Driver.instScopeOkF` decides it (`instScopeOkF_sound`,
`instScopeOkF_complete`).

#1002 part 2: `InstScopeTFL ctx`, every instruction of `ctx` in `Compile.instETFL` (`instETF` or
an `f64const` of any bits, one from the literal pool among them), is the scope that the float
validator `Driver.lowerCheckTCF` checks (`Driver.instScopeOkFL` decides it); `InstScopeTF` gives
it (`InstScopeTF.toTFL`). The typed contexts and shapes over it are the scope-generic ones
(`InstScope.tfl`, `ScopeS.lean`).

#35: `InstScopeTFLO ctx`, every instruction of `ctx` in `Compile.instETFLO` (`instETFL`, an
`fcopysign` or an `fma` at `f32`/`f64`), is the scope that `Driver.lowerCheckTCF` checks
(`Driver.instScopeOkFLO` decides it; it was `instScopeOkFL`); `InstScopeTFL` gives it
(`InstScopeTFL.toTFLO`). The typed contexts and shapes over it are the scope-generic ones
(`InstScope.tflo`).
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

/-- **The supported instructions of a float-capable context with the proven float operations
and the literal pool** (#1002 part 2): every instruction of `ctx` is in `Compile.instETFL`. -/
def InstScopeTFL (ctx : Ctx) : Prop :=
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
    info.clif = some inst → Compile.instETFL inst = true

theorem InstScopeTF.toTFL {ctx : Ctx} (h : InstScopeTF ctx) : InstScopeTFL ctx :=
  fun ii info inst hi hc => Compile.instETFL_of_instETF (h ii info inst hi hc)

/-- **The supported instructions of a float-capable context with the proven float operations,
the literal pool, `fcopysign` and `fma`** (#35): every instruction of `ctx` is in
`Compile.instETFLO`. -/
def InstScopeTFLO (ctx : Ctx) : Prop :=
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
    info.clif = some inst → Compile.instETFLO inst = true

theorem InstScopeTFL.toTFLO {ctx : Ctx} (h : InstScopeTFL ctx) : InstScopeTFLO ctx :=
  fun ii info inst hi hc => Compile.instETFLO_of_instETFL (h ii info inst hi hc)

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

/-- `InstScopeTFL ctx`, decided (#1002 part 2). -/
def instScopeOkFL (ctx : Ctx) : Bool :=
  ctx.insts.toList.all fun info => match info.clif with
    | some i => Compile.instETFL i
    | none => true

theorem instScopeOkFL_sound {ctx : Ctx} (h : instScopeOkFL ctx = true) : InstScopeTFL ctx := by
  intro ii info inst hi hc
  have := List.all_eq_true.mp h info (by rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? hi)
  simpa [hc] using this

theorem instScopeOkFL_complete {ctx : Ctx} (h : InstScopeTFL ctx) : instScopeOkFL ctx = true := by
  refine List.all_eq_true.mpr fun info hi => ?_
  obtain ⟨ii, hii, e⟩ := List.getElem_of_mem hi
  have hget : ctx.insts[ii]? = some info := by
    rw [← Array.getElem?_toList, List.getElem?_eq_getElem hii, e]
  split
  · exact h ii info _ hget ‹_›
  · rfl

/-- `InstScopeTFLO ctx`, decided (#35). -/
def instScopeOkFLO (ctx : Ctx) : Bool :=
  ctx.insts.toList.all fun info => match info.clif with
    | some i => Compile.instETFLO i
    | none => true

theorem instScopeOkFLO_sound {ctx : Ctx} (h : instScopeOkFLO ctx = true) : InstScopeTFLO ctx := by
  intro ii info inst hi hc
  have := List.all_eq_true.mp h info (by rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? hi)
  simpa [hc] using this

theorem instScopeOkFLO_complete {ctx : Ctx} (h : InstScopeTFLO ctx) :
    instScopeOkFLO ctx = true := by
  refine List.all_eq_true.mpr fun info hi => ?_
  obtain ⟨ii, hii, e⟩ := List.getElem_of_mem hi
  have hget : ctx.insts[ii]? = some info := by
    rw [← Array.getElem?_toList, List.getElem?_eq_getElem hii, e]
  split
  · exact h ii info _ hget ‹_›
  · rfl

end Backend.Proof.Driver
