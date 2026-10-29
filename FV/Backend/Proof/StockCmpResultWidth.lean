module

public import FV.Backend.Proof.IselCmpRoot

@[expose] public section

namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false

/-- An arbitrary preceding instruction sequence cannot change the fact that the final CSET writes a
complete zero-or-one register. This uses the actual abstract semantics, through
Refines, and does not assume anything about the preceding source instructions. -/
theorem stock_cmp_cset_suffix_normalized {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (before : List MInst) {d : Nat} {c : Cond}
    (valid : c ≠ .al ∧ c ≠ .nv) {ρ ρ' : Nat → CV} {w w' : Arm.ArmState}
    (run : seqRun isem (before ++ [.cset (.vreg d .int) c]) ρ w = some (.fall ρ' w')) :
    ∃ b : Bool, ρ' d = ofX (if b then 1#64 else 0#64) := by
  induction before generalizing ρ w with
  | nil =>
    obtain ⟨actual,world,executed,_,written⟩ := Runs.cset refines d valid ρ w
    have same := Option.some.inj (executed.symm.trans run)
    obtain ⟨rfl,rfl⟩ := SeqEnd.fall.inj same
    rw [written]
    simp only [upd,ite_true]
    exact ⟨!(Arm.ConditionHolds c.invert.bits w),by cases Arm.ConditionHolds c.invert.bits w <;> rfl⟩
  | cons i rest ih =>
    simp only [List.cons_append,seqRun] at run
    split at run
    · cases run
    · split at run
      · cases run
      · split at run
        · split at run
          · rename_i tail
            cases done : seqRun isem (rest ++ [.cset (.vreg d .int) c]) _ _ with
            | none => rw [done] at run; cases run
            | some result =>
              rw [done] at run
              cases result with
              | fall regs world =>
                cases run
                exact ih done
              | stop => cases run
          · cases run
        · cases run

/-- The low-byte comparison result and its actual final CSET together justify
zero-extension to every original scalar output width. The low-byte theorem
alone deliberately leaves upper bits unspecified. -/
theorem stock_cmp_cset_suffix_extend {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {before : List MInst} {d : Nat} {c : Cond}
    (valid : c ≠ .al ∧ c ≠ .nv) {ρ ρ' : Nat → CV} {w w' : Arm.ArmState}
    (run : seqRun isem (before ++ [.cset (.vreg d .int) c]) ρ w = some (.fall ρ' w'))
    {b : Bool} (value : VHolds ⟨.i8,Clif.Sem.bool8 b⟩ (ρ' d))
    {ty : Clif.Ty} (accepted : eTy ty = true) :
    VHolds ⟨ty,Clif.Sem.uextend ty.width (Clif.Sem.bool8 b)⟩ (ρ' d) := by
  obtain ⟨actual,normalized⟩ := stock_cmp_cset_suffix_normalized refines before valid run
  have same : actual = b := by
    rw [normalized] at value
    cases actual <;> cases b <;> first | rfl | (simp [VHolds,Clif.Sem.bool8,ofX,Clif.Ty.width] at value)
  subst actual
  rw [normalized]
  exact vholds_uextend_bool8 accepted b

end Backend.Stock.Proof.ScalarCmp
