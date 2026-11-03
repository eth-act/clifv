import FV.Backend.Proof.StockAcquirePureExtendTotal

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Successful actual extension helper execution derives its complete total fragment internally.
The theorem accepts arbitrary machine values and requires no source execution after a fault. -/
theorem stock_ext_helper_total {p : Program} (data : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (signed wide : Bool) {fuel x : Nat} (enough : 60 ≤ fuel)
    {st next : State} {trace nextTrace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) {} fuel 27 (ScalarShift.extTerm signed wide) [.value x]
      (st,trace) out (next,nextTrace)) :
    ∃ fragment : List MInst,
      next.base.emitted = st.base.emitted++fragment.toArray ∧
      ∀ (aliases : Array (Option Nat)) (regs : Nat → CV),∃ nextRegs,
        PRun F isem (fragment.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) regs nextRegs ∧
        ∀ key,(∀ inst ∈ fragment.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))),key ∉ vdefs inst) →
          nextRegs key = regs key := by
  have shape : ScalarShift.MappedExtOut ctx x signed (ScalarShift.extTarget wide) (ScalarShift.extPass wide) st next out := by
    cases wide <;> cases signed
    · exact ScalarShift.stock_zext32_out data rfl enough run
    · exact ScalarShift.stock_sext32_out data rfl enough run
    · exact ScalarShift.stock_zext64_out data rfl enough run
    · exact ScalarShift.stock_sext64_out data rfl enough run
  apply stock_ext_shape_total inv refines (by cases wide <;> simp [ScalarShift.extTarget]) ?_ shape
  intro target
  cases wide
  · simp [ScalarShift.extPass]
  · change 64 = 32 at target
    cases target

end Backend.Stock.Proof.Acquire810
