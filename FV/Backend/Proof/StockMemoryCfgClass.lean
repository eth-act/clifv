import FV.Backend.StockMemoryCfgCheck
import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.StockMemoryClass

namespace Backend.Stock.MemoryCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Original source conditions for the captured memory CFG class. -/
structure TwoBlockClass (f : Clif.Function) : Prop where
  scope : LowerScope f
  dominated : Dominated f
  abi : sigAbiOk f.sig = true
  ordinary : (sigRets f.sig).any (·.purpose == .sret) = false
  registers : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin
  shape : ∃ (entry target : Clif.Block) (x z : Nat) (flags : Clif.MemFlags),
    f.blocks = [entry,target] ∧ entry.body = [⟨[],.nop⟩] ∧
      target.body = [⟨[],.nop⟩,⟨[z],.load .load .i32 flags x 0⟩] ∧
      entry.term = .jump ⟨target.id,[]⟩ ∧ target.term = .ret [z] ∧
      x ∈ entry.params.map (·.1) ∧ flags.trapCode = none

/-- Source checks derive the class without requiring a compiled artifact. -/
theorem sourceOk_sound {f : Clif.Function} (checked : sourceOk f = true) : TwoBlockClass f := by
  simp only [sourceOk,Bool.and_eq_true,Bool.not_eq_true'] at checked
  obtain ⟨⟨⟨⟨⟨shapeOk,scope⟩,dominated⟩,abi⟩,ordinary⟩,registers⟩ := checked
  refine ⟨lowerScope_of scope,dominated_of dominated,abi,ordinary,?_,?_⟩
  · intro loc member
    have good := List.all_eq_true.mp registers loc member
    cases loc with
    | reg pin => exact ⟨pin,rfl⟩
    | stack off => cases good
  · unfold eligible at shapeOk
    split at shapeOk
    next entry target blocks =>
      split at shapeOk
      next z flags x dst ret entryBody targetBody jump terminal =>
        simp only [Bool.and_eq_true,beq_iff_eq] at shapeOk
        obtain ⟨⟨⟨destination,same⟩,parameter⟩,notrap⟩ := shapeOk
        subst dst
        subst ret
        exact ⟨entry,target,x,z,flags,blocks,entryBody,targetBody,jump,terminal,
          List.contains_iff_mem.mp parameter,Option.isNone_iff_eq_none.mp notrap⟩
      next => cases shapeOk
    next => cases shapeOk

/-- Artifact validation binds the source class to the actual returned Stock code. -/
theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ result,TwoBlockClass f ∧ Stock.lower f = .ok result ∧ result.code = vc ∧ effectsOnly vc = true := by
  simp only [check,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  cases run : Stock.lower f with
  | error error => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    obtain ⟨equal,effects⟩ := Bool.and_eq_true_iff.mp lowered
    exact ⟨result,sourceOk_sound source,rfl,of_decide_eq_true equal,effects⟩

/-- The CFG whitelist excludes TLS helpers from the actual code. -/
theorem effectsOnly_noTls {vc : VCode} (checked : effectsOnly vc = true) : vc.hasTls = false := by
  rw [VCode.hasTls,Array.any_eq_false']
  intro vb member
  apply Bool.eq_false_iff.mp
  apply Array.any_eq_false'.mpr
  intro i present
  have blocks := List.all_eq_true.mp checked vb (Array.mem_toList_iff.mpr member)
  have good := List.all_eq_true.mp blocks i (Array.mem_toList_iff.mpr present)
  cases i <;> simp_all [effectInstruction]

end Backend.Stock.MemoryCfg
