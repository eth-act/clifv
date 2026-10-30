import Lean
import FV.Backend.Lowering.StockPrologue
import FV.Backend.Proof.LowerDecide

set_option autoImplicit false
namespace Backend.Stock.Prologue
open Backend.Proof.Driver
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

/-- Finite context facts, excluding the dataflow fixpoint computation. -/
theorem systemV_i64_context_scope (name : String) (runs : List Clif.RunCommand) :
    ((Backend.buildCtx (source name .systemVI64 runs)).toOption.map
      (fun s => decide (s.1.valDef = #[none]))).getD false = true ∧
    lowerScopeB (source name .systemVI64 runs) = true := by
  change ((Backend.buildCtx (source "" .systemVI64 [])).toOption.map
      (fun s => decide (s.1.valDef = #[none]))).getD false = true ∧
    lowerScopeB (source "" .systemVI64 []) = true
  decide +kernel

/-- Dominance follows from the actual CFG's availability solution: v0 is an
entry parameter in block0 and available in block1. No caller premise or runtime
fixpoint evaluation is used to assert this fact. -/
theorem systemV_i64_lowering_domain (name : String) (runs : List Clif.RunCommand) :
    Dominated (source name .systemVI64 runs) ∧ LowerScope (source name .systemVI64 runs) := by
  let f := source name .systemVI64 runs
  have finite := systemV_i64_context_scope name runs
  have stored : ∀ {ctx ranges st0}, Backend.buildCtx f = .ok (ctx, ranges, st0) →
      ctx.valDef = #[none] := by
    intro ctx ranges st0 hb
    have h := finite.1
    change ((Backend.buildCtx f).toOption.map (fun s => decide (s.1.valDef = #[none]))).getD false = true at h
    rw [hb] at h
    change decide (ctx.valDef = #[none]) = true at h
    exact of_decide_eq_true h
  have noDefs : ∀ {ctx ranges st0}, Backend.buildCtx f = .ok (ctx, ranges, st0) →
      ∀ x, defArgs ctx x = [] := by
    intro ctx ranges st0 hb x
    have hv := stored hb
    cases x <;> simp [defArgs, Ctx.defInst?, hv]
  have available : ∀ {ctx ranges st0}, Backend.buildCtx f = .ok (ctx, ranges, st0) →
      0 ∈ (availIn f ctx).getD 1 [] := by
    intro ctx ranges st0 hb
    have hv := stored hb
    have solution : FixOk f ctx id (fun tl x => tl = 1 ∧ x = 0) := by
      constructor
      · intro tl x h
        obtain ⟨rfl, rfl⟩ := h
        simp [f, source, D0.source, hv, valueDefs, parsOf]
      · intro tl x h p hp
        obtain ⟨rfl, rfl⟩ := h
        cases p with
        | zero => exact .inl (by simp [parsOf, f, source, D0.source])
        | succ p =>
          cases p with
          | zero => simp [succIdx, f, source, D0.source, succIds, dests] at hp
          | succ p => simp [succIdx, f, source, D0.source] at hp
      · intro tl x h y hy
        rw [noDefs hb x] at hy
        cases hy
    exact inFix_greatest solution ⟨rfl, rfl⟩
  refine ⟨?_, lowerScope_of finite.2⟩
  constructor
  · change ([0] : List Nat).Nodup
    decide
  · intro ctx ranges st0 hb bi B hB
    have av := available hb
    cases bi with
    | zero =>
      have same : B = f.blocks[0]! := by simpa [f, source, D0.source] using hB.symm
      subst B
      constructor
      · intro j stm hj y hy
        cases j with
        | zero =>
          have same : stm = {inst := .nop} := by simpa [f, source, D0.source] using hj.symm
          subst stm
          cases hy
        | succ j => simp [f, source, D0.source] at hj
      · simp [f, source, D0.source, abiTerm, Backend.Proof.Driver.termArgs]
    | succ bi =>
      cases bi with
      | zero =>
        have same : B = f.blocks[1]! := by simpa [f, source, D0.source] using hB.symm
        subst B
        constructor
        · intro j stm hj y hy
          cases j with
          | zero =>
            have same : stm = {inst := .nop} := by simpa [f, source, D0.source] using hj.symm
            subst stm
            cases hy
          | succ j => simp [f, source, D0.source] at hj
        · simpa [f, source, D0.source, abiTerm, sretRet, Backend.Proof.Driver.termArgs,
            availOf, defsBefore, defsFrom] using av
      | succ bi => simp [f, source, D0.source] at hB
  · intro ctx ranges st0 hb tl x hx hndef y hy
    rw [noDefs hb x] at hy
    cases hy

end Backend.Stock.Prologue
