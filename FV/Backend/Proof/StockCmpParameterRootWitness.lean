module

public import FV.Backend.Proof.StockCmpParameterRootValues
public import FV.Backend.Proof.StockCmpSourceMatchWitness

@[expose] public section

namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def frameOf {f : Clif.Function} {ctx : Ctx} (_ : MappedCtxInv f ctx) : Clif.Frame := {
  func := f
  regs := fun z => if z = 7 then some ⟨.i64,0#64⟩ else if z = 31 then some ⟨.i64,1#64⟩ else none
  slots := [],body := [⟨[100],.icmp .eq .i64 7 31⟩],term := .ret [100] }
private def witnessRegs (key : Nat) : CV := if key = 193 then 1#128 else 0
private def mappedContext {f : Clif.Function} {ctx : Ctx} (_ : MappedCtxInv f ctx) : Ctx := ctx
/-- An actual accepted original sparse-ID named comparison lower call inhabits
the complete selected-root value composition, including the real emitter rule
trace, fresh output vector, code and outside-result register preservation. -/
theorem stock_cmp_parameter_root_source_witness :
    ∃ ctx st next out trace ms d,Stock.runTerm ctx "lower" [.inst 0] st = .ok (some out,next,trace) ∧
      out = .regsVec [[.vreg d .int]] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base ms ∧
      ∀ world,Runs (fun _ => True) ispec (ms.map (·.mapRegs (Backend.lowerFunction.resolve #[] 1)))
        witnessRegs world (fun ρ' _ => VHolds ⟨.i8,0#8⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = witnessRegs k) := by
  obtain ⟨out,next,trace,run,selected,id,inv,data,type⟩ := stock_cmp_original_selection_witness
  let fr := frameOf inv
  have held : ValuesHeld (Demanded next) (mappedContext inv) fr witnessRegs := by
    intro z needed value lookup
    by_cases first : z = 7
    · subst z
      simp only [fr,frameOf,ite_true,Option.some.injEq] at lookup
      subst value
      exact ⟨192,rfl,by unfold VHolds witnessRegs; decide +kernel⟩
    · by_cases second : z = 31
      · subst z
        simp only [fr,frameOf,first,ite_false,ite_true,Option.some.injEq] at lookup
        subst value
        exact ⟨193,rfl,by unfold VHolds witnessRegs; decide +kernel⟩
      · simp only [fr,frameOf,first,second,ite_false] at lookup
        cases lookup
  obtain ⟨nx,ny,d,mapX,mapY,output,lower,upper,fragment,execution⟩ := stock_cmp_parameter_selected_source_values
    inv (cc := .eq) (ty := .i64) (by decide) (i := 0) (x := 7) (y := 31) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) selected (fr := fr) (u := 0#64) (v := 1#64) (by rfl) (by rfl)
    (F := fun _ => True) (isem := ispec) (fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩)
    (aliases := #[]) (ρ := witnessRegs) (Nat.zero_le _)
    (fun z r mapped => by
      change z < 101
      by_cases bound : z < 101
      · exact bound
      · unfold Ctx.valueReg? at mapped
        rw [Array.getElem?_eq_none (by change 101 ≤ z; omega)] at mapped
        cases mapped) held
  exact ⟨_,_,next,out,trace,_,d,run,output,lower,upper,fragment,execution⟩
end Backend.Stock.Proof.ScalarCmp
