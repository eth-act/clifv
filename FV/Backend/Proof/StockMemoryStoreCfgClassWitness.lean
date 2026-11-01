import FV.Backend.Proof.StockMemoryStoreCfgCheck
import FV.Backend.Proof.StockMemoryStoreNopCfgDomainWitness

namespace Backend.Stock.Memory.StoreNopCfgFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory.StoreRoots
set_option autoImplicit false
set_option Elab.async false

/-- All seven complete source forms inhabit the class without a compiler certificate. -/
theorem family (kind : Kind) : CfgClass kind kind.sourceTy (function kind) := by
  refine ⟨scope kind,dominated kind,by cases kind <;> rfl,rfl,?_,?_⟩
  · intro loc member
    have locations : locsOf (function kind).sig = [ArgLoc.reg (.x 0),ArgLoc.reg (.x 1)] := by
      cases kind <;> rfl
    rw [locations] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact ⟨_,rfl⟩
  · refine ⟨(function kind).blocks[0]!, (function kind).blocks[1]!,1,1,0,
      Fixture.flags,kind.sourceTy,rfl,?_,rfl,rfl,?_,rfl,by simp [function],by simp [function],?_,rfl⟩
    · intro stm member
      have same : stm = ⟨[],.nop⟩ := by simpa [function] using member
      subst stm
      rfl
    · intro j stm found
      have indices : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
        have bound := lt_of_getElem? found
        simp [function] at bound
        omega
      rcases indices with rfl | rfl | rfl | rfl
      all_goals simp [function] at found; subst stm; simp
    · cases kind <;> intro h <;> first | rfl | cases h

-- witness: native_decide
/-- The actual source checker accepts every complete fixed source form. -/
theorem source_checked (kind : Kind) : MemoryStoreCfg.sourceOk (function kind) = true := by
  cases kind <;> native_decide

-- witness: native_decide
/-- The actual checker accepts the exact code from a successful Stock run. -/
theorem actual_checked (kind : Kind) :
    ∃ result,Stock.lower (function kind) = .ok result ∧
      MemoryStoreCfg.check (function kind) result.code = true := by
  have good : (do
      let result ← Stock.lower (function kind)
      pure (MemoryStoreCfg.check (function kind) result.code)).toOption = some true := by
    cases kind <;> native_decide
  cases run : Stock.lower (function kind) with
  | error error => simp [Except.toOption,run] at good
  | ok result =>
    refine ⟨result,rfl,?_⟩
    simpa [Except.toOption,run] using good

end Backend.Stock.Memory.StoreNopCfgFixture
