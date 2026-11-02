import FV.Backend.Proof.IselCmpSdiv
import FV.Backend.Proof.StockDivFlags
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
/-- Actual overflow guard execution follows both outcomes, using new standard-
kernel flag arithmetic while preserving every machine register. -/
theorem stock_div_overflow_guard_run (hR : Refines F isem) (sz : OperandSize) (kc ky : Nat) (ρ : Nat → CV)
    (w : Arm.ArmState) :
    (opnd sz (ρ ky) = BitVec.allOnes sz.bits ∧ opnd sz (ρ kc) = BitVec.intMin sz.bits →
      TrapRun isem (ovfCheck sz kc ky) ρ w .intOvf) ∧
    (¬ (opnd sz (ρ ky) = BitVec.allOnes sz.bits ∧ opnd sz (ρ kc) = BitVec.intMin sz.bits) →
      Runs F isem (ovfCheck sz kc ky) ρ w (fun ρ' _ => ρ' = ρ)) := by
  have hs1 : SetsFlags (.aluRRImm12 .addS sz .xzr (.vreg ky .int) ⟨1, false⟩) ρ
      (Arm.AddWithCarry (opnd sz (ρ ky)) (BitVec.ofNat sz.bits 1) 0#1).2 :=
    ⟨_, rfl, rfl, fun w => by show ispec _ [ρ ky] w = _; simp [ispec, defOut, Imm12.value]⟩
  have h12 : Runs F isem [.aluRRImm12 .addS sz .xzr (.vreg ky .int) ⟨1, false⟩,
      .ccmpImm sz (.vreg kc .int) 1 ⟨false, false, false, false⟩ .eq] ρ w (fun ρ' w' => ρ' = ρ ∧
      Arm.ConditionHolds Cond.vs.bits w' =
        (opnd sz (ρ ky) == BitVec.allOnes sz.bits && opnd sz (ρ kc) == BitVec.intMin sz.bits)) := by
    refine Runs.append (ms1 := [_]) (Runs.flags hR hs1 w) fun ρ1 w1 ⟨h1, h2⟩ => ?_
    subst h1
    have hs2 : ispec (.ccmpImm sz (.vreg kc .int) 1 ⟨false, false, false, false⟩ .eq) [ρ1 kc] w1 =
        some ([], Arm.write_pstate (if Arm.ConditionHolds Cond.eq.bits w1 then
          cmpFlags (opnd sz (ρ1 kc)) (BitVec.ofNat sz.bits 1) else
          Arm.make_pstate (BitVec.ofBool false) (BitVec.ofBool false) (BitVec.ofBool false)
            (BitVec.ofBool false)) w1, .next) := by
      simp [ispec, cmpFlags]
    refine Runs.one hR rfl hs2 rfl (SameWorldNF.write_pstate F _ w1) fun w'' hw => ⟨vdefUpd_nil _ _, ?_⟩
    rw [SameWorld.conditionHolds hw, conditionHolds_write_pstate, h2, stock_div_condOn_adds1]
    split
    · rename_i hc; rw [hc, Bool.true_and, stock_div_condOn_sub1_vs (show sz.bits = 32 ∨ sz.bits = 64 by cases sz <;> simp [OperandSize.bits])]
    · rename_i hc; simp only [Bool.not_eq_true] at hc; rw [hc, Bool.false_and, condOn_nzcv0_vs]
  have hlast : ovfCheck sz kc ky = [.aluRRImm12 .addS sz .xzr (.vreg ky .int) ⟨1, false⟩,
      .ccmpImm sz (.vreg kc .int) 1 ⟨false, false, false, false⟩ .eq] ++ [.trapIf (.cond .vs) .intOvf] := rfl
  constructor
  · intro ⟨ha, hb⟩
    rw [hlast]
    refine TrapRun.prefix h12 fun ρ1 w1 ⟨_, hv⟩ => ?_
    have hs : ispec (.trapIf (.cond .vs) .intOvf) [] w1 = some ([], w1, .halt) := by
      show some ([], w1, if Arm.ConditionHolds Cond.vs.bits w1 then Ctl.halt else Ctl.next) = _
      rw [hv, ha, hb]; simp
    obtain ⟨w'', hr⟩ := seqRun_one_halt (F := F) hR (i := .trapIf (.cond .vs) .intOvf) rfl (ρ := ρ1) hs rfl
    exact ⟨_, _, _, _, _, _, _, hr, rfl⟩
  · intro hn
    rw [hlast]
    refine Runs.append h12 fun ρ1 w1 ⟨h1, hv⟩ => ?_
    subst h1
    refine Runs.one hR (i := .trapIf (.cond .vs) .intOvf) rfl (outs := []) (w' := w1) ?_ rfl
      (SameWorldNF.refl F w1) fun _ _ => vdefUpd_nil _ _
    show some ([], w1, if Arm.ConditionHolds Cond.vs.bits w1 then Ctl.halt else Ctl.next) = _
    have : Arm.ConditionHolds Cond.vs.bits w1 = false := by
      rw [hv]; simpa [Bool.and_eq_true, beq_iff_eq] using hn
    rw [this]; rfl

/-- Actual division operands drive both zero-guard outcomes; no nonzero-only
input condition is imposed on the family contract. -/
theorem stock_div_zero_guard_run {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {n : Nat} (width : n ≤ 64) {signed : Bool}
    {b : BitVec n} {ρ : Nat → CV} {key : Nat}
    (operand : DivOpnd signed b (ρ key)) (w : Arm.ArmState) :
    (b = 0#n → TrapRun isem [.trapIf (.zero (.vreg key .int) (szOf n)) .intDivz] ρ w .intDivz) ∧
    (b ≠ 0#n → Runs F isem [.trapIf (.zero (.vreg key .int) (szOf n)) .intDivz] ρ w (fun ρ' _ => ρ' = ρ)) := by
  have tested := operand.zero_iff width w (.vreg key .int)
  constructor
  · intro zero
    apply trapRun_trapIf_zero refines
    rw [tested,zero]; rfl
  · intro nonzero
    apply runs_trapIf_zero_fall refines
    rw [tested]
    exact beq_eq_false_iff_ne.mpr nonzero
end Backend.Stock.Proof.ScalarDiv
