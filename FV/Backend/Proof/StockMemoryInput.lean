import FV.Backend.Proof.StockMemoryLoadWitness

namespace Backend.Stock.Memory.LoadFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private def original : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx function).toOption.getD (sinkCtx,#[],default)
private theorem original_build : Backend.buildCtx function = .ok original := rfl

theorem scope : LowerScope function := lowerScope_of rfl

private theorem pointer_available : 0 ∈ (availIn function original.1).getD 1 [] := by
  have good : FixOk function original.1 id (fun tl x => tl = 1 ∧ x = 0) := by
    constructor
    · intro tl x pair
      obtain ⟨rfl,rfl⟩ := pair
      exact ⟨by decide,by decide,by decide +kernel,by decide,by decide,by decide⟩
    · intro tl x pair p predecessor
      obtain ⟨rfl,rfl⟩ := pair
      cases p with
      | zero => exact Or.inl (by simp [parsOf,function])
      | succ p => cases p <;> simp [succIdx,succIds,dests,function] at predecessor
    · intro tl x pair y member
      obtain ⟨rfl,rfl⟩ := pair
      change y ∈ ([] : List Nat) at member
      cases member
  exact inFix_greatest good ⟨rfl,rfl⟩

/-- Original SSA and dominance hold for the inherited pointer and real load. -/
theorem dominated : Dominated function := by
  constructor
  · change ([0,2] : List Nat).Nodup
    decide +kernel
  · intro ctx ranges st build bi b found
    have context : ctx = original.1 := congrArg Prod.fst (Except.ok.inj (build.symm.trans original_build))
    subst ctx
    have bound : bi < 2 := by have h := lt_of_getElem? found; simpa [function] using h
    have cases : bi = 0 ∨ bi = 1 := by omega
    rcases cases with rfl | rfl
    · simp [function] at found
      subst b
      constructor
      · intro j stm present
        simp [function] at present
      · intro x member
        simp [abiTerm,Driver.termArgs,sretRet,sigRets,function] at member
    · simp [function] at found
      subst b
      constructor
      · intro j stm present
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at present
          subst stm
          intro x member
          have equal : x = 0 := List.mem_singleton.mp member
          subst x
          have member := pointer_available
          simpa [availOf,function,defsBefore,defsFrom] using member
        | succ j => simp at present
      · intro x member
        have equal : x = 2 := by simpa [abiTerm,Driver.termArgs,sretRet,sigRets,function] using member
        subst x
        simp [availOf,function,defsBefore,defsFrom]
  · intro ctx ranges st build tl x available notLocal y member
    cases tl with
    | zero =>
      have fixed := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand 0 x available
      omega
    | succ tl =>
      cases tl with
      | zero => change y ∉ ([] : List Nat); simp
      | succ tl => simp [parsOf,function]

end Backend.Stock.Memory.LoadFixture
