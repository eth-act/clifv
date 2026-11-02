import FV.Backend.Proof.IselCmpRun

namespace Backend.Stock.Proof.Sequence
open Backend Backend.Proof
set_option autoImplicit false

/-- A stopped sequence preserves every virtual register absent from its
instruction definitions. This includes the register file before the final
control instruction and does not require any particular instruction semantics. -/
theorem stop_frame {V W : Type} (sem : ISem V W) {code : List MInst}
    {ρ regs : Nat → V} {world prefixWorld endWorld : W} {index : Nat} {inst : MInst}
    {ops : Array Operand} {outs : List V} {control : Ctl}
    (run : seqRun sem code ρ world = some (.stop index inst ops regs prefixWorld outs endWorld control)) :
    ∀ key,(∀ m ∈ code,key ∉ vdefs m) → regs key = ρ key := by
  induction code generalizing ρ world index with
  | nil => cases run
  | cons first rest ih =>
    simp only [seqRun] at run
    split at run
    · cases run
    · rename_i firstOps operands
      split at run
      · cases run
      · rename_i values nextWorld nextControl step
        split at run
        · rename_i length
          split at run
          · cases tail : seqRun sem rest (vdefUpd firstOps values ρ) nextWorld with
            | none => rw [tail] at run; cases run
            | some result =>
              rw [tail] at run
              cases result with
              | fall final finalWorld => cases run
              | stop stopIndex stopped used before beforeWorld outputs stoppedWorld ctl =>
                cases run
                intro key untouched
                rw [ih tail key (fun m member => untouched m (List.mem_cons_of_mem _ member))]
                apply vdefUpd_not_mem
                simpa only [vdefs,operands] using untouched first (List.mem_cons_self ..)
          · cases run
            intro key _
            rfl
        · cases run

private def witnessSem : ISem Nat Unit := fun inst _ world =>
  match inst with
  | .jump _ => some ([],world,.goto 0)
  | _ => some ([],world,.next)

/-- A nonempty prefix followed by an actual jump inhabits stopped-sequence
framing, preserving every register. -/
theorem stop_frame_witness (ρ : Nat → Nat) :
    seqRun witnessSem [.args [],.jump 3] ρ () =
      some (.stop 1 (.jump 3) #[] ρ () [] () (.goto 0)) ∧
    ∀ key,ρ key = ρ key := by
  have run : seqRun witnessSem [.args [],.jump 3] ρ () =
      some (.stop 1 (.jump 3) #[] ρ () [] () (.goto 0)) := rfl
  refine ⟨run,fun key => stop_frame witnessSem run key ?_⟩
  intro inst member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  all_goals change key ∉ ([] : List Nat)
  all_goals simp

end Backend.Stock.Proof.Sequence
