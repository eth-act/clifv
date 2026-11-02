import FV.Backend.Proof.StockShiftBodyRefines
namespace Backend.Stock.Proof.CastBody
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

def Family (inst : Clif.Inst) : Prop :=
  ShiftBody.Family inst ∨ (∃ op ty x, inst = .extend op ty x) ∨ (∃ ty x, inst = .ireduce ty x)

def SafeFormat (inst : Clif.Inst) : Prop :=
  (instNames inst).1 ≠ "LoadNoOffset" ∧ (instNames inst).1 ≠ "Load" ∧ (instNames inst).1 ≠ "IntCompare"

theorem family_pure {inst : Clif.Inst} (family : Family inst) : pureInst inst = true := by
  rcases family with old | ⟨op,ty,x,rfl⟩ | ⟨ty,x,rfl⟩
  · exact ShiftBody.family_pure old
  · rfl
  · rfl

theorem family_quiet {inst : Clif.Inst} (family : Family inst) : colored inst = false := by
  rcases family with old | ⟨op,ty,x,rfl⟩ | ⟨ty,x,rfl⟩
  · exact ShiftBody.family_quiet old
  · rfl
  · rfl

theorem family_single {inst : Clif.Inst} (family : Family inst) (f : Clif.Function) :
    (inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·)).map List.length = some 1 := by
  rcases family with old | ⟨op,ty,x,rfl⟩ | ⟨ty,x,rfl⟩
  · exact ShiftBody.family_single old f
  · rfl
  · rfl

private theorem shift_formats {inst : Clif.Inst} (family : ShiftBody.Family inst) : SafeFormat inst := by
  rcases family with
    ((((⟨sub,ty,x,y,rfl⟩ | ⟨ty,c,x,y,rfl⟩ | ⟨kind,ty,x,y,rfl⟩) | ⟨ty,imm,rfl⟩) |
      ⟨ty,x,rfl⟩) | ⟨ty,x,y,rfl⟩) | ⟨kind,ty,x,y,rfl⟩
  all_goals simp [SafeFormat,instNames]

/-- Cast syntax derives exclusions for load/comparison look-through roots.
No extra runtime checker or selected-root premise is introduced. -/
theorem family_formats {inst : Clif.Inst} (family : Family inst) : SafeFormat inst := by
  rcases family with old | ⟨op,ty,x,rfl⟩ | ⟨ty,x,rfl⟩
  · exact shift_formats old
  · simp [SafeFormat,instNames]
  · simp [SafeFormat,instNames]
end Backend.Stock.Proof.CastBody
