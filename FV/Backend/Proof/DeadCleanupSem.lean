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
  all_goals simp [cmpForm] at hc
  case aluRRR op sz rd rn rm =>
    cases op <;> cases rd <;> cases rn <;> simp [cmpForm] at hc
    rcases us with _ | ⟨a, _ | ⟨b, _ | ⟨c, us⟩⟩⟩ <;> cases rm <;>
      simp [mspec, ispec] at h ⊢
    all_goals (obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, _, rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩)
  case aluRRImm12 op sz rd rn imm =>
    cases op <;> cases rd <;> cases rn <;> simp [cmpForm] at hc
    all_goals rcases us with _ | ⟨a, _ | ⟨b, us⟩⟩ <;>
      simp [mspec, ispec] at h ⊢
    all_goals (obtain ⟨hb, rfl, rfl, rfl⟩ := h; exact ⟨rfl, _, rfl, fun _ => by simp [hb]⟩)
  case aluRRRExtend op sz rd rn rm e =>
    cases op <;> cases rd <;> cases rn <;> cases rm <;> simp [cmpForm] at hc
    rcases us with _ | ⟨a, _ | ⟨b, _ | ⟨c, us⟩⟩⟩ <;>
      simp [mspec, ispec] at h ⊢
    all_goals (obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, _, rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩)
  case aluRRImmLogic op sz rd rn imm =>
    cases op <;> cases rd <;> cases rn <;> simp [cmpForm] at hc
    rcases us with _ | ⟨a, _ | ⟨b, us⟩⟩ <;>
      simp [mspec, ispec] at h ⊢
    all_goals (obtain ⟨hb, rfl, rfl, rfl⟩ := h; exact ⟨rfl, _, rfl, fun _ => by simp [hb]⟩)

theorem write_pstate_twice (p q : Arm.PState) (w : Arm.ArmState) :
    Arm.write_pstate q (Arm.write_pstate p w) = Arm.write_pstate q w := by
  simp only [Arm.write_pstate]
  simp [Arm.w_of_w_shadow, Arm.w_of_w_commute]

private theorem spOf_write_pstate (p : Arm.PState) (w : Arm.ArmState) :
    spOf (Arm.write_pstate p w) = spOf w := by
  simp only [spOf, Arm.write_pstate]
  rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp),
    Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]

set_option maxHeartbeats 4000000 in
/-- A flag-free producer's specification neither reads nor changes the flags. -/
theorem mspec_flagFree_pstate {sb : Nat} {i : MInst} {us : List CV} (hf : flagFree i = true)
    (p : Arm.PState) (w : Arm.ArmState) :
    mspec sb i us (Arm.write_pstate p w) =
      (mspec sb i us w).map (fun r => (r.1, Arm.write_pstate p r.2.1, r.2.2)) := by
  unfold mspec
  split <;> try { simp_all [flagFree, pureNoFlags, pureAlu, spOf_write_pstate] }
  unfold ispec
  split <;> simp_all [flagFree, pureNoFlags, pureAlu, Option.map_map, Function.comp_def]
  all_goals (try split) <;> (try rfl) <;> simp_all [Option.map_map, Function.comp_def]

/-- A flag-free producer steps alike from a world whose flags a compare wrote. -/
theorem mspec_flagFree {sb : Nat} {i : MInst} {us outs : List CV} {p : Arm.PState}
    {w w1 : Arm.ArmState} {ctl : Ctl} (hf : flagFree i = true)
    (h : mspec sb i us (Arm.write_pstate p w) = some (outs, w1, ctl)) :
    mspec sb i us w = some (outs, w, ctl) := by
  rw [mspec_flagFree_pstate hf] at h
  obtain ⟨⟨o, w2, c⟩, hr, he⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨rfl, -⟩ := mspec_pure (pureForm_of_flagFree hf) hr
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, -, rfl⟩ := he
  exact hr

/-- Under the specification, the next compare overwrites a compare's flags, and flag-free
producers ignore them. -/
theorem mspec_cmpOverwrite (sb : Nat) : CmpOverwrite (mspec sb) := by
  intro i us w outs w' ctl hc h
  obtain ⟨hctl, p, rfl, -⟩ := mspec_cmp hc h
  refine ⟨hctl, fun k us' r hk hr => ?_, fun j us' o c hj hr => mspec_flagFree hj hr⟩
  obtain ⟨o, w2, c⟩ := r
  obtain ⟨-, q, hw2, hall⟩ := mspec_cmp hk hr
  rw [hall w, hw2, write_pstate_twice]

example (w : Arm.ArmState) : ∃ outs,
    mspec 0 deadMvn [0#128] w = some (outs, w, .next) := by
  exact ⟨[ofX (~~~(0#64))], rfl⟩

end Backend.DeadCleanup
