import FV.Backend.Proof.StockMemoryAccessHalt
import FV.E2E.RegLevelCorrect
import FV.E2E.RegLevelU

namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- The existing allocated-code realizer also reaches the first access boundary.
The proof changes only its abstract halt semantics; the actual machine stays unchanged. -/
theorem realizes_haltAccess {R : RL} {isem : Backend.Proof.Sem} {sb : Nat}
    {code : Clif.TrapCode} {property : BitVec 64 → Nat → Prop}
    (old : Realizes R.vc R.rf isem ckeep R.step (QA R) R.GoodX) :
    Realizes R.vc R.rf (haltAccess sb code property isem) ckeep R.step (QA R) R.GoodX := by
  intro s before after related stepped
  cases stepped with
  | move =>
    obtain ⟨n,final,step,held,good⟩ := old s _ _ related .move
    exact ⟨n,final,mstep_congr step (fun _ _ _ _ _ _ _ _ _ impossible => by cases impossible),held,good⟩
  | @op b k allocs items values world block inst operands outs outs' next ctl regs after found located
      valid sizes execution length kept clobbered advance =>
    have step : MStep R.vc (haltAccess sb code property isem) ckeep R.rf
        (.run ⟨b,.op k allocs :: items,values,world⟩) after :=
      MStep.op found located valid sizes execution length kept clobbered advance
    by_cases fault : HaltsAtAccess sb code property inst
        (((operands.zip allocs).toList.filter (·.1.isUse)).map (values ·.2)) world
    · simp only [haltAccess,if_pos fault,Option.some.injEq,Prod.mk.injEq] at execution
      obtain ⟨outsEq,nextEq,controlEq⟩ := execution
      cases controlEq
      cases advance with
      | halt => exact ⟨0,_,step,.inl ⟨trivial,trivial⟩,fun _ impossible => absurd impossible (Nat.not_lt_zero _)⟩
    · have normal : isem inst (((operands.zip allocs).toList.filter (·.1.isUse)).map (values ·.2)) world =
          some (outs,next,ctl) := by simpa only [haltAccess,if_neg fault] using execution
      obtain ⟨n,final,original,held,good⟩ := old s _ _ related
        (MStep.op found located valid sizes normal length kept clobbered advance)
      refine ⟨n,final,mstep_congr original ?_,held,good⟩
      intro b' k' allocs' items' values' world' block' inst' operands' same found' located' valid'
      cases same
      rw [found] at found'
      cases found'
      rw [located] at located'
      cases located'
      rw [valid] at valid'
      cases valid'
      simp only [haltAccess,if_neg fault]

end Backend.Stock.Proof.MemoryFaults
