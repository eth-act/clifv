import FV.Backend.Lowering.Stock

/-!
Local safety facts for the stock lowering policy. These are the first pieces of
the replacement schedule proof; they do not establish whole-function refinement.
In particular, a successful sink requires an ordering barrier immediately before
the scan position and no outstanding demand for any of its results.
-/

namespace Backend.Stock.Proof

open Isle Isle.Aarch64

theorem sink_ctor_eq (ctx : Ctx) (st : State) (i : Nat) :
    externCtor ctx T.sink_inst [.inst i] st =
      if st.entryColor[i]! == 0 || st.color != some (st.entryColor[i]! + 1) ||
          ctx.insts[i]!.results.any (fun v => st.demand[v]! != 0) then
        .unmodeled s!"invalid sink of instruction {i}"
      else .ok (.op .unit,
        { st with color := some st.entryColor[i]!, sunk := st.sunk.set! i true }) := rfl

theorem sink_accepted {ctx : Ctx} {st next : State} {i : Nat} {out : V}
    (h : externCtor ctx T.sink_inst [.inst i] st = .ok (out, next)) :
    st.entryColor[i]! ≠ 0 ∧ st.color = some (st.entryColor[i]! + 1) ∧
      (∀ v ∈ ctx.insts[i]!.results, st.demand[v]! = 0) ∧
      out = .op .unit ∧
      next = { st with color := some st.entryColor[i]!, sunk := st.sunk.set! i true } := by
  rw [sink_ctor_eq] at h
  split at h
  · cases h
  · rename_i good
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, List.any_eq_true] at good
    have hc : st.entryColor[i]! ≠ 0 := fun hz => good (Or.inl (Or.inl hz))
    have hscan : st.color = some (st.entryColor[i]! + 1) :=
      Classical.byContradiction fun hn => good (Or.inl (Or.inr hn))
    have hzero : ∀ v ∈ ctx.insts[i]!.results, st.demand[v]! = 0 := by
      intro v hv
      exact Classical.byContradiction fun hn => good (Or.inr ⟨v, hv, hn⟩)
    cases h
    exact ⟨hc, hscan, hzero, rfl, rfl⟩

/-! Non-vacuity witnesses use an ordinary load with a single result, zero demand
and the adjacent memory color. No generated ISLE program is reduced in proofs. -/

def sinkCtx : Ctx := {
  func := default
  insts := #[⟨.op .unit, [0], [.int 8], some (.load .load .i8 {} 1 0)⟩]
  valTy := #[some (.int 8), some (.int 64)]
  valDef := #[some 0, none]
  valReg := #[some (.vreg 192 .int), some (.vreg 193 .int)]
  slotOff := [] }

def sinkState : State := {
  base := ⟨194, Array.replicate 194 .int, #[], 0⟩
  demand := #[0, 0]
  uses := #[.once, .once]
  instBlock := #[0]
  entryColor := #[1]
  endColor := #[3]
  tryRegs := #[([], [])]
  current := some 1
  color := some 2
  sunk := #[false]
  opportunistic := #[none, none] }

def sinkNext : State := { sinkState with color := some 1, sunk := #[true] }

theorem sink_ctor_eq_witness :
    externCtor sinkCtx T.sink_inst [.inst 0] sinkState = .ok (.op .unit, sinkNext) := rfl

theorem sink_accepted_witness :
    sinkState.entryColor[0]! ≠ 0 ∧ sinkState.color = some (sinkState.entryColor[0]! + 1) ∧
      (∀ v ∈ sinkCtx.insts[0]!.results, sinkState.demand[v]! = 0) ∧
      (V.op .unit) = .op .unit ∧
      sinkNext = { sinkState with
        color := some sinkState.entryColor[0]!
        sunk := sinkState.sunk.set! 0 true } :=
  sink_accepted sink_ctor_eq_witness

theorem source_effect_eligible {ctx : Ctx} {st : State} {v i : Nat}
    (h : source ctx st v = some (i, true)) (hc : st.entryColor[i]! ≠ 0) :
    ctx.defInst? v = some i ∧ st.uses[v]! = .once ∧
      ctx.insts[i]!.results.length = 1 ∧ st.color = some (st.entryColor[i]! + 1) := by
  unfold source at h
  cases hd : ctx.defInst? v with
  | none => simp [hd, bind, Option.bind] at h
  | some j =>
    simp only [hd, bind, Option.bind] at h
    split at h
    · rename_i hz
      have hij : j = i := (Prod.mk.inj (Option.some.inj h)).1
      subst j
      exact False.elim (hc (by simpa only [beq_iff_eq] using hz))
    · split at h
      · rename_i eligible
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq] at eligible
        exact ⟨rfl, eligible.1.1, eligible.1.2, eligible.2⟩
      · cases h

theorem source_effect_eligible_witness :
    sinkCtx.defInst? 0 = some 0 ∧ sinkState.uses[0]! = .once ∧
      sinkCtx.insts[0]!.results.length = 1 ∧
      sinkState.color = some (sinkState.entryColor[0]! + 1) :=
  source_effect_eligible (show source sinkCtx sinkState 0 = some (0, true) from rfl)
    (show sinkState.entryColor[0]! ≠ 0 from by decide)

end Backend.Stock.Proof
