import FV.E2E.LinkArmStepX30
import FV.E2E.RegLevelMemTrap

/-!
# The compiled-code check that body lines name no `x30` (SEM1, `docs/plans/uninit.md` §5.9, step 3m)

The lock-step of prophecy determinism (`StEqOutX`, equal but for `x30`) steps an unhooked line
with `stEqOutX_armStepX`, which needs `DecX30Free` at the line: the decoded instruction names no
`x30` (`ArmInst.gprs`). Cranelift never allocates `x30`; the lines that name it are the calls
(`bl`, `blr`, `blrTlsDesc`: hooked), `ret`, and the frame-record pair
`stp fp, lr, [sp, #-16]!` / `ldp fp, lr, [sp], #16` (`LinkArmStepFrameRec`). So:

* `Insn.x30Exempt`: those lines;
* `Insn.x30Ok env i`: exempt, or the instruction `toArmInst env i` names no `x30`;
* `FnAsm.x30Free fa lm`: every instruction line of `fa` is `x30Ok` at its own encoder
  environment (decidable, run by `lean-backend-encode-test x30`);
* **`decX30Free_of_check`**: on the function's own machine, at a non-exempt instruction line of a
  function that passes the check, `DecX30Free` holds.
-/

namespace E2E

open Backend Backend.Proof

/-- The lines that may name `x30`: the calls, `ret` and the frame-record pair. -/
def _root_.Backend.Insn.x30Exempt : Insn → Bool
  | .bl _ | .blr _ | .blrTlsDesc _ _ | .ret => true
  | i => i == .stp .fp .lr (.spPreIndexed (-16)) || i == .ldp .fp .lr (.spPostIndexed 16)

/-- One line's check: exempt, or its instruction names no `x30`. -/
def _root_.Backend.Insn.x30Ok (env : Env) (i : Insn) : Bool :=
  i.x30Exempt ||
    match i.toArmInst env with
    | .ok a => a.gprs.all (· != 30#5)
    | .error _ => true

/-- **The check on compiled code**: every instruction line `j` of `fa` is `x30Ok` at its encoder
environment (`RL.envOf`). -/
def _root_.Backend.FnAsm.x30Free (fa : FnAsm) (lm : Std.HashMap Lbl Nat) : Bool :=
  (List.range fa.lines.toList.length).all fun j =>
    match fa.lines.toList[j]? with
    | some (.ins x _) => x.x30Ok ⟨lineOffset fa.lines.toList j, (lm[·]?)⟩
    | _ => true

theorem x30Free_line {fa : FnAsm} {lm : Std.HashMap Lbl Nat} (h : fa.x30Free lm = true)
    {j : Nat} {x : Insn} {t : Option Clif.TrapCode} (hj : fa.lines.toList[j]? = some (.ins x t)) :
    x.x30Ok ⟨lineOffset fa.lines.toList j, (lm[·]?)⟩ = true := by
  have hlt : j < fa.lines.toList.length := by
    rcases Nat.lt_or_ge j fa.lines.toList.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hj; cases hj
  have := List.all_eq_true.mp h j (List.mem_range.mpr hlt)
  simpa only [hj] using this

/-- **Soundness of the check.** On the function's own machine, at an instruction line `j` that is
not exempt, the decoded instruction names no `x30`. -/
theorem decX30Free_of_check {R : RL} (hR : R.Wf) (hc : R.fa.x30Free R.lm = true)
    {s : Arm.ArmState} {j : Nat} {x : Insn} {t : Option Clif.TrapCode}
    (hj : R.L[j]? = some (.ins x t)) (hx : x.x30Exempt = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j) : DecX30Free s := by
  obtain ⟨a, ha, hd⟩ := decodeAt_line hR hj hprog hpc
  have hok := x30Free_line hc hj
  simp only [Insn.x30Ok, hx, Bool.false_or, ha] at hok
  intro w ai hf hdec
  simp only [Concurrency.ArmFoot.decodeAt, show Arm.read_pc s = Arm.r .PC s from rfl] at hd hf
  rw [hf] at hd
  change Arm.decode_raw_inst w = some a at hd
  rw [hdec, Option.some.injEq] at hd
  subst hd
  intro y hy hy30
  have := List.all_eq_true.mp hok y hy
  simp [hy30] at this

/-- The machine at an instruction line of a laid-out function (`decodeAt_line` without `RL`). -/
theorem decodeAt_ofLine {fa : FnAsm} {fb : FnBin} {lm : Std.HashMap Lbl Nat} {base : BitVec 64}
    (hl : fa.layout = .ok fb) (hm : labelOffsets fa.lines = .ok lm)
    (hfit : 4 * fb.words.size ≤ 2 ^ 64) {s : Arm.ArmState} (hprog : s.program = fb.program base)
    {j : Nat} {x : Insn} {t : Option Clif.TrapCode} (hj : fa.lines.toList[j]? = some (.ins x t))
    (hpc : Arm.r .PC s = base + BitVec.ofNat 64 (lineOffset fa.lines.toList j)) :
    ∃ a, x.toArmInst ⟨lineOffset fa.lines.toList j, (lm[·]?)⟩ = .ok a ∧
      Concurrency.ArmFoot.decodeAt s = some a := by
  obtain ⟨h4, w, hw, hk⟩ := FnAsm.layout_word hl hm hj rfl
  have hfetch : Arm.fetch_inst (Arm.r .PC s) s = some w := by
    rw [Arm.fetch_inst_from_program, hprog, hpc]
    have := FnBin.program_find (base := base)
      (by have := (FnAsm.layout_size hl).1; omega) hk
    rwa [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h4)] at this
  obtain ⟨a, ha, hd⟩ := Insn.decode_encode hw
  refine ⟨a, ha, ?_⟩
  simp only [Concurrency.ArmFoot.decodeAt, hfetch, hd]

/-- **Soundness of the check** (`decX30Free_of_check` without `RL`). -/
theorem decX30Free_of_line {fa : FnAsm} {fb : FnBin} {lm : Std.HashMap Lbl Nat}
    {base : BitVec 64} (hl : fa.layout = .ok fb) (hm : labelOffsets fa.lines = .ok lm)
    (hfit : 4 * fb.words.size ≤ 2 ^ 64) (hc : fa.x30Free lm = true) {s : Arm.ArmState}
    (hprog : s.program = fb.program base) {j : Nat} {x : Insn} {t : Option Clif.TrapCode}
    (hj : fa.lines.toList[j]? = some (.ins x t)) (hx : x.x30Exempt = false)
    (hpc : Arm.r .PC s = base + BitVec.ofNat 64 (lineOffset fa.lines.toList j)) : DecX30Free s := by
  obtain ⟨a, ha, hd⟩ := decodeAt_ofLine hl hm hfit hprog hj hpc
  have hok := x30Free_line hc hj
  simp only [Insn.x30Ok, hx, Bool.false_or, ha] at hok
  intro w ai hf hdec
  simp only [Concurrency.ArmFoot.decodeAt, show Arm.read_pc s = Arm.r .PC s from rfl] at hd hf
  rw [hf] at hd
  change Arm.decode_raw_inst w = some a at hd
  rw [hdec, Option.some.injEq] at hd
  subst hd
  intro y hy hy30
  have := List.all_eq_true.mp hok y hy
  simp [hy30] at this

end E2E
