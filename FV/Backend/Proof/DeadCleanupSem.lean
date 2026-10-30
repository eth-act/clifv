import FV.Backend.Proof.DeadCleanupLive
import FV.Backend.Proof.RegallocCSem

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
  split <;> try { simp_all [flagFree, pureForm, pureAlu, spOf_write_pstate] }
  unfold ispec
  split <;> simp_all [flagFree, pureForm, pureAlu, Option.map_map, Function.comp_def]
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

/-- A `jump` steps alike from every world: it keeps the world and branches. -/
def JumpPlain {V W : Type} (sem : ISem V W) : Prop :=
  ∀ l us w outs w' ctl, sem (.jump l) us w = some (outs, w', ctl) →
    w' = w ∧ (∃ j, ctl = .goto j) ∧ ∀ w0, sem (.jump l) us w0 = some (outs, w0, ctl)

theorem mspec_jumpPlain (sb : Nat) : JumpPlain (mspec sb) := by
  intro l us w outs w' ctl h
  cases us with
  | nil =>
    simp [mspec, ispec] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, ⟨0, rfl⟩, fun _ => by simp [mspec, ispec]⟩
  | cons u us => simp [mspec, ispec] at h

/-- Under the specification, the next compare overwrites a compare's flags, and flag-free
producers and `jump`s ignore them. -/
theorem mspec_cmpOverwrite (sb : Nat) : CmpOverwrite (mspec sb) := by
  refine ⟨fun i us w outs w' ctl hc h => ?_, fun l us w outs w' ctl h => ?_⟩
  · obtain ⟨hctl, p, rfl, -⟩ := mspec_cmp hc h
    refine ⟨hctl, fun k us' r hk hr => ?_, fun j us' o c hj hr => ?_⟩
    · obtain ⟨o, w2, c⟩ := r
      obtain ⟨-, q, hw2, hall⟩ := mspec_cmp hk hr
      rw [hall w, hw2, write_pstate_twice]
    · rcases Bool.or_eq_true_iff.mp hj with hj | hj
      · exact mspec_flagFree hj hr
      · obtain ⟨l, rfl⟩ : ∃ l, j = .jump l := by cases j <;> simp at hj; exact ⟨_, rfl⟩
        exact ((mspec_jumpPlain sb) _ _ _ _ _ _ hr).2.2 w
  · obtain ⟨hw, hj, -⟩ := mspec_jumpPlain sb _ _ _ _ _ _ h
    exact ⟨hw, hj⟩

/-- The forms the cleanup's value semantics runs by their specification `mspec`: the pure
producers (unchanged world) and, since the cleanup drops compares whose flags are dead (#552),
the compares (flags only). -/
def specForm (i : MInst) : Bool := pureForm i || cmpForm i

theorem specForm_of_pure {i : MInst} (h : pureForm i = true) : specForm i = true := by
  simp [specForm, h]

theorem specForm_of_cmp {i : MInst} (h : cmpForm i = true) : specForm i = true := by
  simp [specForm, h]

theorem specForm_cases {i : MInst} (h : specForm i = true) :
    pureForm i = true ∨ cmpForm i = true := by
  simpa [specForm] using h

theorem pureForm_of_not_spec {i : MInst} (h : specForm i = false) : pureForm i = false := by
  simp only [specForm, Bool.or_eq_false_iff] at h
  exact h.1

theorem cmpForm_of_not_spec {i : MInst} (h : specForm i = false) : cmpForm i = false := by
  simp only [specForm, Bool.or_eq_false_iff] at h
  exact h.2

/-- A specification form's step continues. -/
theorem mspec_spec_next {sb : Nat} {i : MInst} {us outs : List CV} {w w' : Arm.ArmState}
    {ctl : Ctl} (hs : specForm i = true) (h : mspec sb i us w = some (outs, w', ctl)) :
    ctl = .next := by
  rcases specForm_cases hs with hp | hc
  · exact (mspec_pure hp h).2
  · exact (mspec_cmp hc h).1

/-- A semantics that runs the specification forms by `mspec`, and `jump`s alike from every
world, lets the next compare overwrite a compare's flags: the premise of the cleanup's compare
removal. -/
theorem cmpOverwrite_of_mspec {sem : Sem} {sb : Nat}
    (h : ∀ i, specForm i = true → sem i = mspec sb i) (hjp : JumpPlain sem) :
    CmpOverwrite sem := by
  refine ⟨fun i us w outs w' ctl hc hs => ?_, fun l us w outs w' ctl hs => ?_⟩
  · rw [h i (specForm_of_cmp hc)] at hs
    obtain ⟨hctl, hov⟩ := (mspec_cmpOverwrite sb).1 i us w outs w' ctl hc hs
    refine ⟨hctl, fun K us' r hK hr => ?_, fun j us' o c hj hr => ?_⟩
    · rw [h K (specForm_of_cmp hK)] at hr ⊢
      exact hov.1 K us' r hK hr
    · rcases Bool.or_eq_true_iff.mp hj with hf | hjm
      · have hjs := specForm_of_pure (pureForm_of_flagFree hf)
        rw [h j hjs] at hr ⊢
        exact hov.2 j us' o c hj hr
      · obtain ⟨l, rfl⟩ : ∃ l, j = .jump l := by cases j <;> simp at hjm; exact ⟨_, rfl⟩
        exact (hjp _ _ _ _ _ _ hr).2.2 w
  · obtain ⟨hw, hj, -⟩ := hjp _ _ _ _ _ _ hs
    exact ⟨hw, hj⟩

/-- Compares are not branches (a specification form has no targets). -/
theorem specForm_targets {i : MInst} (h : specForm i = true) : i.targets = [] := by
  rcases specForm_cases h with hp | hc
  · exact pureForm_targets hp
  · unfold cmpForm at hc
    split at hc <;> first | rfl | cases hc

example (w : Arm.ArmState) : ∃ outs,
    mspec 0 deadMvn [0#128] w = some (outs, w, .next) := by
  exact ⟨[ofX (~~~(0#64))], rfl⟩

end Backend.DeadCleanup
