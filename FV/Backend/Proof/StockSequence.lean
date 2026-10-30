import FV.Backend.Proof.IselContract
import FV.Backend.Proof.IselExtern

namespace Backend.Stock.Proof.Sequence
open Backend Backend.Proof

theorem append_fall_inv {V W : Type} (sem : ISem V W) {leading suffix : List MInst}
    {ρ final : Nat → V} {w endWorld : W}
    (run : seqRun sem (leading++suffix) ρ w = some (.fall final endWorld)) :
    ∃ middle world,seqRun sem leading ρ w = some (.fall middle world) ∧
      seqRun sem suffix middle world = some (.fall final endWorld) := by
  induction leading generalizing ρ w with
  | nil => exact ⟨ρ,w,rfl,run⟩
  | cons i ms ih =>
    simp only [List.cons_append,seqRun] at run
    split at run
    · cases run
    · rename_i ops operands
      split at run
      · cases run
      · rename_i outs nextWorld ctl step
        split at run
        · rename_i length
          split at run
          · cases rest : seqRun sem (ms++suffix) (vdefUpd ops outs ρ) nextWorld with
            | none => rw [rest] at run; cases run
            | some result =>
              rw [rest] at run
              cases result with
              | fall after afterWorld =>
                cases run
                obtain ⟨middle,world,left,right⟩ := ih rest
                refine ⟨middle,world,?_,right⟩
                simp only [seqRun,operands,step,length,ite_true,left,Option.map_some]
                rfl
              | stop k j used before beforeWorld values stoppedWorld control => cases run
          · cases run
        · cases run
/-- A nonempty real pseudo-instruction prefix and suffix inhabit inversion. -/
theorem append_fall_inv_witness (ρ : Nat → Nat) :
    ∃ middle world,
      seqRun (fun _ _ (_ : Unit) => some ([],(),Ctl.next)) [MInst.args []] ρ () = some (.fall middle world) ∧
      seqRun (fun _ _ (_ : Unit) => some ([],(),Ctl.next)) [MInst.args []] middle world = some (.fall ρ ()) := by
  exact append_fall_inv (fun _ _ (_ : Unit) => some ([],(),Ctl.next))
    (leading := [MInst.args []]) (suffix := [MInst.args []]) (by rfl)

end Backend.Stock.Proof.Sequence
