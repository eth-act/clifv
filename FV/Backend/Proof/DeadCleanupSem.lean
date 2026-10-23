import FV.Backend.Proof.DeadCleanupLive
import FV.Backend.Proof.RegallocCSemWorld

namespace Backend.DeadCleanup
open Backend.Proof

set_option maxHeartbeats 4000000 in
/-- The value-level specification confirms that a whitelisted instruction
changes neither the world nor control. This alone is not a whole-pass theorem:
the concrete semantics also has canonical-register bookkeeping. -/
theorem mspec_pure {sb : Nat} {i : MInst} {us outs : List CV}
    {w w' : Arm.ArmState} {ctl : Ctl} (hp : pureForm i = true)
    (h : mspec sb i us w = some (outs, w', ctl)) : w' = w ∧ ctl = .next := by
  unfold mspec at h
  split at h <;> try { simp_all [pureForm, pureAlu] }
  unfold ispec at h
  split at h <;> simp_all [pureForm, pureAlu, Option.map_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq]
  all_goals grind only

/-- A compare's specification: it continues, its world is the input world with the flags
written, and its result is the same from every world (it reads no flags). -/
theorem mspec_cmp {sb : Nat} {i : MInst} {us outs : List CV} {w w' : Arm.ArmState}
    {ctl : Ctl} (hc : cmpForm i = true) (h : mspec sb i us w = some (outs, w', ctl)) :
    ctl = .next ∧ ∃ p, w' = Arm.write_pstate p w ∧
      ∀ w0, mspec sb i us w0 = some (outs, Arm.write_pstate p w0, ctl) := by
  cases i
  all_goals simp at hc
  case aluRRR op sz rd rn rm =>
    cases op <;> cases rd <;> cases rn <;> simp at hc
    rcases us with _ | ⟨a, _ | ⟨b, _ | ⟨c, us⟩⟩⟩ <;> cases rm <;>
      simp [mspec, ispec] at h ⊢
    all_goals (obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, _, rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩)
  case aluRRImm12 op sz rd rn imm =>
    cases op <;> cases rd <;> cases rn <;> simp at hc
    all_goals rcases us with _ | ⟨a, _ | ⟨b, us⟩⟩ <;>
      simp [mspec, ispec] at h ⊢
    all_goals (obtain ⟨hb, rfl, rfl, rfl⟩ := h; exact ⟨rfl, _, rfl, fun _ => by simp [hb]⟩)
  case aluRRRExtend op sz rd rn rm e =>
    cases op <;> cases rd <;> cases rn <;> cases rm <;> simp at hc
    rcases us with _ | ⟨a, _ | ⟨b, _ | ⟨c, us⟩⟩⟩ <;>
      simp [mspec, ispec] at h ⊢
    all_goals (obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, _, rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩)
  case aluRRImmLogic op sz rd rn imm =>
    cases op <;> cases rd <;> cases rn <;> simp at hc
    rcases us with _ | ⟨a, _ | ⟨b, us⟩⟩ <;>
      simp [mspec, ispec] at h ⊢
    all_goals (obtain ⟨hb, rfl, rfl, rfl⟩ := h; exact ⟨rfl, _, rfl, fun _ => by simp [hb]⟩)

theorem write_pstate_twice (p q : Arm.PState) (w : Arm.ArmState) :
    Arm.write_pstate q (Arm.write_pstate p w) = Arm.write_pstate q w := by
  simp only [Arm.write_pstate]
  simp [Arm.w_of_w_shadow, Arm.w_of_w_commute]

/-- Under the specification, the next compare overwrites a compare's flags. -/
theorem mspec_cmpOverwrite (sb : Nat) : CmpOverwrite (mspec sb) := by
  intro i us w outs w' ctl hc h
  obtain ⟨hctl, p, rfl, -⟩ := mspec_cmp hc h
  refine ⟨hctl, fun k us' r hk hr => ?_⟩
  obtain ⟨o, w2, c⟩ := r
  obtain ⟨-, q, hw2, hall⟩ := mspec_cmp hk hr
  rw [hall w, hw2, write_pstate_twice]

example (w : Arm.ArmState) : ∃ outs,
    mspec 0 deadMvn [0#128] w = some (outs, w, .next) := by
  exact ⟨[ofX (~~~(0#64))], rfl⟩

end Backend.DeadCleanup
