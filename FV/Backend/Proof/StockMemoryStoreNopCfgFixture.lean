import FV.Backend.Proof.StockMemoryStoreRecordFixture

namespace Backend.Stock.Memory.StoreNopCfgFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory.StoreRoots
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Fixed successor-store functions retain the original entry parameters. -/
def function (kind : Kind) : Clif.Function := { Fixture.function kind with
  name := "stock_integer_store_nop_cfg"
  blocks := [
    {id := 0,params := [(0,.i64),(1,kind.sourceTy)],body := [⟨[],.nop⟩],term := .jump ⟨1,[]⟩},
    {id := 1,body := [⟨[],.nop⟩,⟨[],.store kind.sourceOp kind.sourceTy Fixture.flags 1 0 0⟩,⟨[],.nop⟩,⟨[],.nop⟩],term := .ret []}] }

private def original (kind : Kind) : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx (function kind)).toOption.getD (sinkCtx,#[],default)
private theorem original_build (kind : Kind) : Backend.buildCtx (function kind) = .ok (original kind) := by
  cases kind <;> rfl

theorem scope (kind : Kind) : LowerScope (function kind) := by
  cases kind <;> exact lowerScope_of rfl

private theorem parameter_available (kind : Kind) {x : Nat} (which : x = 0 ∨ x = 1) :
    x ∈ (availIn (function kind) (original kind).1).getD 1 [] := by
  have good : FixOk (function kind) (original kind).1 id (fun tl x => tl = 1 ∧ (x = 0 ∨ x = 1)) := by
    constructor
    · intro tl x pair
      obtain ⟨rfl,which⟩ := pair
      rcases which with rfl | rfl
      all_goals cases kind <;> exact ⟨by decide,by decide,by decide +kernel,by decide,by decide,by decide⟩
    · intro tl x pair p predecessor
      obtain ⟨rfl,which⟩ := pair
      cases p with
      | zero => exact Or.inl (by rcases which with rfl | rfl <;> simp [parsOf,function])
      | succ p => cases p <;> simp [succIdx,succIds,dests,function] at predecessor
    · intro tl x pair y member
      obtain ⟨rfl,which⟩ := pair
      rcases which with rfl | rfl
      all_goals cases kind <;> change y ∈ ([] : List Nat) at member <;> cases member
  exact inFix_greatest good ⟨rfl,which⟩

/-- Both store operands remain available after the actual source jump. -/
theorem dominated (kind : Kind) : Dominated (function kind) := by
  constructor
  · change ([0,1] : List Nat).Nodup
    decide +kernel
  · intro ctx ranges st build bi b found
    have context : ctx = (original kind).1 := congrArg Prod.fst (Except.ok.inj (build.symm.trans (original_build kind)))
    subst ctx
    have bound : bi < 2 := by have h := lt_of_getElem? found; simpa [function] using h
    have cases : bi = 0 ∨ bi = 1 := by omega
    rcases cases with rfl | rfl
    · simp [function] at found
      subst b
      constructor
      · intro j stm present
        cases j with
        | zero =>
          simp at present
          subst stm
          intro x member
          simp [Driver.instArgs] at member
        | succ j => simp at present
      · intro x member
        simp [abiTerm,Driver.termArgs,sretRet,sigRets,function,Fixture.function] at member
    · simp [function] at found
      subst b
      constructor
      · intro j stm present
        have indices : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
          have bound := lt_of_getElem? present
          simp only [List.length_cons,List.length_nil] at bound
          omega
        rcases indices with rfl | rfl | rfl | rfl
        all_goals simp at present; subst stm; intro x member
        all_goals try simp [Driver.instArgs] at member
        have which : x = 0 ∨ x = 1 := by simpa [Driver.instArgs,or_comm] using member
        have available := parameter_available kind which
        simpa [availOf,function,defsBefore,defsFrom] using available
      · intro x member
        simp [abiTerm,Driver.termArgs,sretRet,sigRets,function,Fixture.function] at member
  · intro ctx ranges st build tl x available notLocal y member
    cases tl with
    | zero =>
      have fixed := (inFix_fixOk (f := function kind) (ctx := ctx) (gn := id)).cand 0 x available
      omega
    | succ tl =>
      cases tl with
      | zero => change y ∉ ([] : List Nat); simp
      | succ tl => simp [parsOf,function]

-- witness: native_decide
-- This fixed acceptance check is not used by a generic correctness theorem.
theorem lowered (kind : Kind) : (Stock.lower (function kind)).isOk = true := by
  cases kind <;> native_decide

end Backend.Stock.Memory.StoreNopCfgFixture
