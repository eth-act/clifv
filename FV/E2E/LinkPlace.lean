import FV.E2E.LinkClifN

/-! # The slot-placement oracle on whole-program runs (agent/link-widen, stage 2)

With the slot-placement oracle (`Clif.Mem.place`), entering a function pushes its activation's
stack pointer and places its slots (`Clif.enterSlots`), returning pops it and frees them. A
returning whole-program run gives back the oracle (`runLoop_place`) when the externs keep it,
and creates no allocation (`runLoop_allocs`) when the externs create none (their allocations
are among their arguments'). -/

namespace Clif
open Opt

/-! ## Entering a function -/

theorem bumpSlots_facts : ∀ (slots : List (SlotId × StackSlot)) (acc : List (SlotId × Nat) × Mem),
    (slots.foldl (fun (acc : List (SlotId × Nat) × Mem) (s : SlotId × StackSlot) =>
      let (base, m) := acc.2.alloc s.2.size (s.2.align.getD 1)
      (acc.1 ++ [(s.1, base)], m)) acc).2.place = acc.2.place ∧
    (∃ l, (slots.foldl (fun (acc : List (SlotId × Nat) × Mem) (s : SlotId × StackSlot) =>
      let (base, m) := acc.2.alloc s.2.size (s.2.align.getD 1)
      (acc.1 ++ [(s.1, base)], m)) acc).1 = acc.1 ++ l) ∧
    ∀ x ∈ (slots.foldl (fun (acc : List (SlotId × Nat) × Mem) (s : SlotId × StackSlot) =>
      let (base, m) := acc.2.alloc s.2.size (s.2.align.getD 1)
      (acc.1 ++ [(s.1, base)], m)) acc).2.allocs, x ∈ acc.2.allocs ∨
      x.base ∈ (slots.foldl (fun (acc : List (SlotId × Nat) × Mem) (s : SlotId × StackSlot) =>
        let (base, m) := acc.2.alloc s.2.size (s.2.align.getD 1)
        (acc.1 ++ [(s.1, base)], m)) acc).1.map (·.2)
  | [], acc => ⟨rfl, ⟨[], by simp⟩, fun x hx => .inl hx⟩
  | s :: ss, acc => by
    simp only [List.foldl_cons]
    obtain ⟨h1, ⟨l, h2⟩, h3⟩ := bumpSlots_facts ss
      (acc.1 ++ [(s.1, (acc.2.alloc s.2.size (s.2.align.getD 1)).1)],
        (acc.2.alloc s.2.size (s.2.align.getD 1)).2)
    refine ⟨h1, ⟨(s.1, (acc.2.alloc s.2.size (s.2.align.getD 1)).1) :: l, by rw [h2]; simp⟩,
      fun x hx => ?_⟩
    rcases h3 x hx with hx' | hx'
    · simp only [Mem.alloc, List.mem_cons] at hx'
      rcases hx' with rfl | hx'
      · exact .inr (by rw [h2]; simp [Mem.alloc])
      · exact .inl hx'
    · exact .inr hx'

theorem placeSlots_facts (sp : BitVec 64) (off : SlotId → Nat) :
    ∀ (slots : List (SlotId × StackSlot)) (acc : List (SlotId × Nat) × Mem),
    (slots.foldl (fun (acc : List (SlotId × Nat) × Mem) (s : SlotId × StackSlot) =>
      (acc.1 ++ [(s.1, sp.toNat + off s.1)], acc.2.allocAt (sp.toNat + off s.1) s.2.size))
      acc).2.place = acc.2.place ∧
    (∃ l, (slots.foldl (fun (acc : List (SlotId × Nat) × Mem) (s : SlotId × StackSlot) =>
      (acc.1 ++ [(s.1, sp.toNat + off s.1)], acc.2.allocAt (sp.toNat + off s.1) s.2.size))
      acc).1 = acc.1 ++ l) ∧
    ∀ x ∈ (slots.foldl (fun (acc : List (SlotId × Nat) × Mem) (s : SlotId × StackSlot) =>
      (acc.1 ++ [(s.1, sp.toNat + off s.1)], acc.2.allocAt (sp.toNat + off s.1) s.2.size))
      acc).2.allocs, x ∈ acc.2.allocs ∨
      x.base ∈ (slots.foldl (fun (acc : List (SlotId × Nat) × Mem) (s : SlotId × StackSlot) =>
        (acc.1 ++ [(s.1, sp.toNat + off s.1)], acc.2.allocAt (sp.toNat + off s.1) s.2.size))
        acc).1.map (·.2)
  | [], acc => ⟨rfl, ⟨[], by simp⟩, fun x hx => .inl hx⟩
  | s :: ss, acc => by
    simp only [List.foldl_cons]
    obtain ⟨h1, ⟨l, h2⟩, h3⟩ := placeSlots_facts sp off ss
      (acc.1 ++ [(s.1, sp.toNat + off s.1)], acc.2.allocAt (sp.toNat + off s.1) s.2.size)
    refine ⟨h1, ⟨(s.1, sp.toNat + off s.1) :: l, by rw [h2]; simp⟩, fun x hx => ?_⟩
    rcases h3 x hx with hx' | hx'
    · simp only [Mem.allocAt, List.mem_cons] at hx'
      rcases hx' with rfl | hx'
      · exact .inr (by rw [h2]; simp)
      · exact .inl hx'
    · exact .inr hx'

/-- Entering a function pushes a stack pointer on the slot-placement oracle. -/
theorem enterSlots_place (f : Function) (mem : Mem) :
    (mem.place = none → (enterSlots f mem).2.place = none) ∧
    ∀ pl, mem.place = some pl → ∃ sp, (enterSlots f mem).2.place = some { pl with sps := sp :: pl.sps } := by
  refine ⟨fun h => ?_, fun pl h => ?_⟩
  · simp only [enterSlots, h]
    exact (bumpSlots_facts f.slots ([], mem)).1.trans h
  · cases hf : pl.frame f.name with
    | none =>
      simp only [enterSlots, h, hf]
      exact ⟨_, (bumpSlots_facts f.slots _).1⟩
    | some p =>
      obtain ⟨d, off⟩ := p
      simp only [enterSlots, h, hf]
      exact ⟨_, (placeSlots_facts _ _ f.slots _).1⟩

/-- The allocations after entering a function: the former ones and its slots. -/
theorem enterSlots_allocs (f : Function) (mem : Mem) :
    ∀ x ∈ (enterSlots f mem).2.allocs, x ∈ mem.allocs ∨ x.base ∈ (enterSlots f mem).1.map (·.2) := by
  cases h : mem.place with
  | none =>
    simp only [enterSlots, h]
    exact (bumpSlots_facts f.slots ([], mem)).2.2
  | some pl =>
    cases hf : pl.frame f.name with
    | none =>
      simp only [enterSlots, h, hf]
      exact (bumpSlots_facts f.slots _).2.2
    | some p =>
      obtain ⟨d, off⟩ := p
      simp only [enterSlots, h, hf]
      exact (placeSlots_facts _ _ f.slots _).2.2

/-- One step of `placeSlots`. -/
def placeStep (sp : BitVec 64) (off : SlotId → Nat) (acc : List (SlotId × Nat) × Mem)
    (s : SlotId × StackSlot) : List (SlotId × Nat) × Mem :=
  (acc.1 ++ [(s.1, sp.toNat + off s.1)], acc.2.allocAt (sp.toNat + off s.1) s.2.size)

/-- **The placed slots**: each slot at `sp + off`, allocated uninitialised. -/
theorem placeSlots_spec (sp : BitVec 64) (off : SlotId → Nat) :
    ∀ (slots : List (SlotId × StackSlot)) (acc : List (SlotId × Nat) × Mem),
    (slots.foldl (placeStep sp off) acc).1 = acc.1 ++ slots.map (fun p => (p.1, sp.toNat + off p.1)) ∧
    (slots.foldl (placeStep sp off) acc).2.symbols = acc.2.symbols ∧
    (∀ x ∈ (slots.foldl (placeStep sp off) acc).2.allocs, x ∈ acc.2.allocs ∨
      ∃ p ∈ slots, x = ⟨sp.toNat + off p.1, p.2.size, false⟩) ∧
    ∀ a b, (slots.foldl (placeStep sp off) acc).2.bytes a = some b → acc.2.bytes a = some b ∧
      ∀ p ∈ slots, ¬ (sp.toNat + off p.1 ≤ a ∧ a < sp.toNat + off p.1 + p.2.size)
  | [], acc => ⟨by simp, rfl, fun x hx => .inl hx, fun a b h => ⟨h, fun p hp => by simp at hp⟩⟩
  | q :: qs, acc => by
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4⟩ := placeSlots_spec sp off qs (placeStep sp off acc q)
    refine ⟨by rw [h1]; simp [placeStep], h2.trans rfl, fun x hx => ?_, fun a b hb => ?_⟩
    · rcases h3 x hx with hx' | ⟨p, hp, rfl⟩
      · simp only [placeStep, Mem.allocAt, List.mem_cons] at hx'
        rcases hx' with rfl | hx'
        · exact .inr ⟨q, List.mem_cons_self .., rfl⟩
        · exact .inl hx'
      · exact .inr ⟨p, List.mem_cons_of_mem _ hp, rfl⟩
    · obtain ⟨hb1, hb2⟩ := h4 a b hb
      simp only [placeStep, Mem.allocAt] at hb1
      split at hb1
      · cases hb1
      · rename_i hn
        refine ⟨hb1, fun p hp => ?_⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hn
        · exact hb2 p hp

/-! ## Local steps -/

theorem store_place {w : Nat} {m : Mem} {fl a n} {x : BitVec w} {m'}
    (h : m.store fl a n x = .ok m') : m'.place = m.place ∧ m'.allocs = m.allocs := by
  simp only [Mem.store, Res.bind_eq_ok, Res.pure_eq_ok] at h
  obtain ⟨_, _, _, _, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem evalInst_place {fr mem i vals mem'} (h : evalInst fr mem i = .ok (vals, mem')) :
    mem'.place = mem.place ∧ mem'.allocs = mem.allocs := by
  cases i <;> simp only [evalInst, Res.bind_eq_ok, Res.pure_eq_ok, Prod.mk.injEq] at h
  all_goals (repeat' (first | obtain ⟨_, _, h⟩ := h | split at h)) <;>
    (try simp only [Res.pure_eq_ok, Prod.mk.injEq, Res.bind_eq_ok] at h) <;>
    (repeat' (first | obtain ⟨_, _, h⟩ := h | split at h))
  all_goals first | exact ⟨rfl, rfl⟩ | exact store_place ‹_›

theorem lstep_next_place {fr m fr' m'} (h : lstep fr m = .next fr' m') :
    m'.place = m.place ∧ m'.allocs = m.allocs := by
  obtain ⟨func, regs, slots, body, term⟩ := fr
  cases body with
  | nil =>
    simp only [lstep] at h
    cases term <;> simp only [LRes.ofRes] at h <;> (repeat' split at h) <;> (try contradiction) <;>
      (cases h; exact ⟨rfl, rfl⟩)
  | cons st rest =>
    simp only [lstep] at h
    split at h
    · simp only [LRes.ofRes] at h; split at h <;> contradiction
    · simp only [LRes.ofRes] at h
      split at h <;> try contradiction
      split at h <;> try contradiction
      cases h
      exact evalInst_place ‹_›

/-! ## Whole-program steps -/

theorem callCont_cases {env : Env} {p : Program} {t : State} {rest : List Stmt}
    {rs : List ValueId} {ext : ExtFunc} {vals : List Val} {s1 : State}
    (h : Opt.callCont env p t rest rs ext vals = .next s1) :
    (s1.callers = ({ t.frame with body := rest }, rs) :: t.callers ∧
      ∃ g, enterFunc g vals t.mem = .ok (s1.frame, s1.mem)) ∨
    (s1.callers = t.callers ∧ (∃ regs, s1.frame = { t.frame with regs, body := rest }) ∧
      ∃ n g rv, env.extern n = some g ∧ g vals t.mem = .returned rv s1.mem) := by
  unfold Opt.callCont at h
  split at h
  · rename_i g hg
    split at h
    · obtain ⟨⟨fr', mem'⟩, he, h⟩ := Opt.StepResult.ofRes_eq_next h
      cases h
      exact .inl ⟨rfl, g, he⟩
    · cases h
  · split at h
    · rename_i gsem hgs
      split at h
      · rename_i rvals mem' hr
        split at h
        · unfold continueWith at h
          split at h
          · rename_i regs _
            cases h
            exact .inr ⟨rfl, ⟨regs, rfl⟩, ext.name, gsem, rvals, hgs, hr⟩
          · cases h
        · cases h
      all_goals cases h
    · cases h

/-- **The shapes of a whole-program step**: a step of the running frame (the allocations and
the oracle kept, or an extern's memory), entering a function, or returning to the caller. -/
def StepShape (env : Env) (s s1 : State) : Prop :=
    (s1.callers = s.callers ∧ s1.frame.slots = s.frame.slots ∧
      ((s1.mem.place = s.mem.place ∧ s1.mem.allocs = s.mem.allocs) ∨
        ∃ n g vals rv, env.extern n = some g ∧ g vals s.mem = .returned rv s1.mem)) ∨
    (∃ c, s1.callers = c :: s.callers ∧ c.1.slots = s.frame.slots ∧
      ∃ g vals, enterFunc g vals s.mem = .ok (s1.frame, s1.mem)) ∨
    (∃ c, s.callers = c :: s1.callers ∧ s1.frame.slots = c.1.slots ∧
      s1.mem = (s.mem.free (s.frame.slots.map (·.2))).leave)

theorem step_next_cases {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env} {s s1 : State}
    (hI : LInv P s) (h : step env P s = .next s1) : StepShape env s s1 := by
  have hcall : ∀ (t : State) rest rs ext vals, t.callers = s.callers →
      t.frame.slots = s.frame.slots → t.mem = s.mem →
      Opt.callCont env P t rest rs ext vals = .next s1 → StepShape env s s1 := by
    intro t rest rs ext vals htc hts htm hc
    rcases callCont_cases hc with ⟨hc1, g, he⟩ | ⟨hc1, ⟨regs, hf1⟩, n, g, rv, hg, hr⟩
    · exact .inr (.inl ⟨_, by rw [hc1, htc], hts, g, vals, htm ▸ he⟩)
    · exact .inl ⟨hc1.trans htc, by rw [hf1]; exact hts, .inr ⟨n, g, vals, rv, hg, htm ▸ hr⟩⟩
  have hind : ∀ (t : State) rest rs sig d a v, t.callers = s.callers →
      t.frame.slots = s.frame.slots → t.mem = s.mem →
      indCont env P t rest rs sig d a v = .next s1 → StepShape env s s1 := by
    intro t rest rs sig d a v htc hts htm hc
    rcases indCont_next hc with ⟨hc1, g, mem', -, he, hm, -⟩ | ⟨hc1, ⟨regs, hf1⟩, n, g, rv, hg, hr⟩
    · subst hm
      exact .inr (.inl ⟨_, by rw [hc1, htc], hts, g, v, htm ▸ he⟩)
    · exact .inl ⟨hc1.trans htc, by rw [hf1]; exact hts, .inr ⟨n, g, v, rv, hg, htm ▸ hr⟩⟩
  rcases step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · rw [step_try env P s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
    obtain ⟨⟨ext, vals⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
    exact hcall (tryState s bc) [] _ ext vals rfl rfl rfl h
  · rw [step_tryInd env P s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
    obtain ⟨⟨d, a, v⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
    exact hind (tryState s bc) [] _ _ d a v rfl rfl rfl h
  · rw [step_ind env P s hb hi] at h
    obtain ⟨⟨d, a, v⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
    exact hind s rest st.results sig d a v rfl rfl rfl h
  · rw [Opt.step_eq_lift env P s hci] at h
    cases hl : Opt.lstep s.frame s.mem with
    | next fr1 m1 =>
      rw [hl] at h; cases h
      exact .inl ⟨rfl, (Opt.lstep_next_frame hl).2.1, .inl (lstep_next_place hl)⟩
    | call ext vals rs rest =>
      rw [hl] at h
      exact hcall s rest rs ext vals rfl rfl rfl h
    | ret vals =>
      rw [hl] at h
      obtain ⟨c, rs, cs, regs, hc, hc1, hf1⟩ := returnValues_next h
      exact .inr (.inr ⟨(c, rs), by rw [hc, hc1], by rw [hf1], returnValues_mem.1 s1 h⟩)
    | tail ext vals => exact absurd hl (lstep_ne_tail hP hI.1)
    | trap c => rw [hl] at h; cases h
    | stuck m => rw [hl] at h; cases h

/-- A whole-program step that finishes returns from the bottom frame, freeing its slots. -/
theorem step_done_mem {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env} {s : State}
    {v : List Val} {m : Mem} (hI : LInv P s) (h : step env P s = .done v m) :
    s.callers = [] ∧ m = (s.mem.free (s.frame.slots.map (·.2))).leave := by
  refine ⟨(step_done_linv hP hI h).1, ?_⟩
  rcases step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · rw [step_try env P s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := ofRes_eq_done h
    obtain ⟨⟨ext, vals⟩, -, h⟩ := ofRes_eq_done h
    exact absurd h callCont_ne_done
  · rw [step_tryInd env P s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := ofRes_eq_done h
    obtain ⟨⟨d, a, w⟩, -, h⟩ := ofRes_eq_done h
    exact absurd h indCont_ne_done
  · rw [step_ind env P s hb hi] at h
    obtain ⟨⟨d, a, w⟩, -, h⟩ := ofRes_eq_done h
    exact absurd h indCont_ne_done
  · rw [Opt.step_eq_lift env P s hci] at h
    cases hl : Opt.lstep s.frame s.mem with
    | ret vals => rw [hl] at h; exact returnValues_mem.2 v m h
    | call ext vals rs rest => rw [hl] at h; exact absurd h callCont_ne_done
    | tail ext vals => exact absurd hl (lstep_ne_tail hP hI.1)
    | next fr1 m1 => rw [hl] at h; cases h
    | trap c => rw [hl] at h; cases h
    | stuck m => rw [hl] at h; cases h

/-! ## The oracle on returning runs -/

/-- The externs keep the slot-placement oracle. -/
def EnvKeepsPlace (env : Env) : Prop :=
  ∀ n g, env.extern n = some g → ∀ vals m rvals m', g vals m = .returned rvals m' →
    m'.place = m.place

/-- The oracle of a state of a run from an activation entered with stack pointers `sps`: one
stack pointer per frame on top of them. -/
def PlaceInv (sps : List (BitVec 64)) (fr : String → Option (Nat × (SlotId → Nat))) (s : State) :
    Prop :=
  ∃ l, s.mem.place = some ⟨l ++ sps, fr⟩ ∧ l.length = s.callers.length + 1

theorem placeInv_step {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    (hk : EnvKeepsPlace env) {sps : List (BitVec 64)} {fr : String → Option (Nat × (SlotId → Nat))}
    {s : State} (hI : LInv P s) (hp : PlaceInv sps fr s) :
    (∀ s1, step env P s = .next s1 → PlaceInv sps fr s1) ∧
    (∀ v m, step env P s = .done v m → m.place = some ⟨sps, fr⟩) := by
  obtain ⟨l, hl, hlen⟩ := hp
  refine ⟨fun s1 h => ?_, fun v m h => ?_⟩
  · rcases step_next_cases hP hI h with ⟨hc, -, ⟨hpl, -⟩ | ⟨n, g, vals, rv, hg, hr⟩⟩ |
      ⟨c, hc, -, g, vals, he⟩ | ⟨c, hc, -, hm⟩
    · exact ⟨l, by rw [hpl, hl], by rw [hc, hlen]⟩
    · exact ⟨l, by rw [hk n g hg vals s.mem rv s1.mem hr, hl], by rw [hc, hlen]⟩
    · obtain ⟨_, _, _, _, _, _, hal, -⟩ := Opt.enterFunc_ok he
      obtain ⟨sp, hsp⟩ := (enterSlots_place g s.mem).2 _ hl
      rw [hal] at hsp
      exact ⟨sp :: l, hsp, by rw [hc]; simp [hlen]⟩
    · rw [hc] at hlen
      cases l with
      | nil => simp at hlen
      | cons y l' =>
        refine ⟨l', ?_, by simpa using hlen⟩
        rw [hm]
        simp only [Mem.leave, Mem.free, hl]
        rfl
  · obtain ⟨hc, hm⟩ := step_done_mem hP hI h
    rw [hc] at hlen
    cases l with
    | nil => simp at hlen
    | cons y l' =>
      cases l' with
      | cons => simp at hlen
      | nil =>
        rw [hm]
        simp only [Mem.leave, Mem.free, hl]
        rfl

/-- **A returning run gives back the oracle**: a whole-program run from a state with one stack
pointer per frame on top of `sps` returns a memory whose oracle has `sps` (when the externs keep
the oracle). -/
theorem runLoop_place {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    (hk : EnvKeepsPlace env) {sps : List (BitVec 64)} {fr : String → Option (Nat × (SlotId → Nat))} :
    ∀ (N : Nat) (s : State) (vals : List Val) (mem : Mem), LInv P s → PlaceInv sps fr s →
      runLoop env P N s = .returned vals mem → mem.place = some ⟨sps, fr⟩
  | 0, _, _, _, _, _, h => by simp at h
  | N + 1, s, vals, mem, hI, hp, h => by
    rw [runLoop_succ'] at h
    have hs := placeInv_step hP hk hI hp
    cases hst : step env P s with
    | next s1 =>
      rw [hst] at h
      exact runLoop_place hP hk N s1 vals mem (step_next_linv hP hI hst).1 (hs.1 s1 hst) h
    | done v m =>
      rw [hst] at h
      simp only [afterStep, Outcome.returned.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hs.2 v m hst
    | trapped c => rw [hst] at h; cases h
    | stuck m => rw [hst] at h; cases h

theorem placeNone_step {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    (hk : EnvKeepsPlace env) {s : State} (hI : LInv P s) (hp : s.mem.place = none) :
    (∀ s1, step env P s = .next s1 → s1.mem.place = none) ∧
    (∀ v m, step env P s = .done v m → m.place = none) := by
  refine ⟨fun s1 h => ?_, fun v m h => ?_⟩
  · rcases step_next_cases hP hI h with ⟨-, -, ⟨hpl, -⟩ | ⟨n, g, vals, rv, hg, hr⟩⟩ |
      ⟨c, -, -, g, vals, he⟩ | ⟨c, -, -, hm⟩
    · rw [hpl, hp]
    · rw [hk n g hg vals s.mem rv s1.mem hr, hp]
    · obtain ⟨_, _, _, _, _, _, hal, -⟩ := Opt.enterFunc_ok he
      have := (enterSlots_place g s.mem).1 hp
      rwa [hal] at this
    · rw [hm]; simp only [Mem.leave, Mem.free, hp]
  · obtain ⟨-, hm⟩ := step_done_mem hP hI h
    rw [hm]; simp only [Mem.leave, Mem.free, hp]

theorem runLoop_placeNone {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    (hk : EnvKeepsPlace env) :
    ∀ (N : Nat) (s : State) (vals : List Val) (mem : Mem), LInv P s → s.mem.place = none →
      runLoop env P N s = .returned vals mem → mem.place = none
  | 0, _, _, _, _, _, h => by simp at h
  | N + 1, s, vals, mem, hI, hp, h => by
    rw [runLoop_succ'] at h
    have hs := placeNone_step hP hk hI hp
    cases hst : step env P s with
    | next s1 =>
      rw [hst] at h
      exact runLoop_placeNone hP hk N s1 vals mem (step_next_linv hP hI hst).1 (hs.1 s1 hst) h
    | done v m =>
      rw [hst] at h
      simp only [afterStep, Outcome.returned.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hs.2 v m hst
    | trapped c => rw [hst] at h; cases h
    | stuck m => rw [hst] at h; cases h

/-- The entry state of an activation pushes one stack pointer on the oracle. -/
theorem initState_place {P : Program} {n : String} {vals : List Val} {cm : Mem} {cs : State}
    (hi : initState P n vals cm = .ok cs) {pl : Place} (hp : cm.place = some pl) :
    PlaceInv pl.sps pl.frame cs := by
  simp only [initState, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.pure_eq_ok] at hi
  obtain ⟨g, -, ⟨fr, mem'⟩, he, rfl⟩ := hi
  obtain ⟨_, _, _, _, _, _, hal, -⟩ := Opt.enterFunc_ok he
  obtain ⟨sp, hsp⟩ := (enterSlots_place g cm).2 _ hp
  rw [hal] at hsp
  exact ⟨[sp], hsp, rfl⟩

/-- **The linked environment keeps the oracle** (the program's functions' runs give it back)
when the base externs do. -/
theorem linkEnvN_keepsPlace {P : Program} {base : Env} {M : Nat} (hP : ∀ g ∈ P.funcs, LinkFree g)
    (hk : EnvKeepsPlace base) : EnvKeepsPlace (linkEnvN P base M) := by
  intro n gsem hg vals m rvals m' hr
  cases hpf : P.func? n with
  | none => rw [linkEnvN_none hpf] at hg; exact hk n gsem hg vals m rvals m' hr
  | some g =>
    rw [linkEnvN_some hpf] at hg
    cases hg
    simp only at hr
    cases hi : initState P n vals m with
    | ok s =>
      rw [hi] at hr
      simp only at hr
      have hI : LInv P s := by
        simp only [initState, hpf, Res.ofOption_some, Res.ok_bind] at hi
        cases he : enterFunc g vals m with
        | ok r =>
          rw [he] at hi
          obtain ⟨fr, mem'⟩ := r
          simp only [Res.ok_bind, Res.pure_eq, Res.ok.injEq] at hi
          subst hi
          exact ⟨LFrame.enterFunc (Program.func?_some hpf).1 he, fun _ h => nomatch h⟩
        | trap => rw [he] at hi; cases hi
        | stuck => rw [he] at hi; cases hi
      cases hmp : m.place with
      | none =>
        have h0 : s.mem.place = none := by
          simp only [initState, hpf, Res.ofOption_some, Res.ok_bind] at hi
          cases he : enterFunc g vals m with
          | ok r =>
            rw [he] at hi
            obtain ⟨fr, mem'⟩ := r
            simp only [Res.ok_bind, Res.pure_eq, Res.ok.injEq] at hi
            subst hi
            obtain ⟨_, _, _, _, _, _, hal, -⟩ := Opt.enterFunc_ok he
            have := (enterSlots_place g m).1 hmp
            rwa [hal] at this
          | trap => rw [he] at hi; cases hi
          | stuck => rw [he] at hi; cases hi
        exact runLoop_placeNone hP hk M s rvals m' hI h0 hr
      | some pl =>
        exact runLoop_place hP hk M s rvals m' hI (initState_place hi hmp) hr
    | trap c => rw [hi] at hr; cases hr
    | stuck msg => rw [hi] at hr; cases hr

/-! ## The allocations on returning runs -/

/-- The externs create no allocation: their allocations are among their arguments'. -/
def EnvKeepsAllocs (env : Env) : Prop :=
  ∀ n g, env.extern n = some g → ∀ vals m rvals m', g vals m = .returned rvals m' →
    ∀ x ∈ m'.allocs, x ∈ m.allocs

/-- The slot bases of the frames of a state. -/
def slotBases (s : State) : List Nat :=
  (s.frame :: s.callers.map (·.1)).flatMap fun fr => fr.slots.map (·.2)

/-- The allocations of a state of a run from memory `cm`: within `cm`'s valid bytes, or slots
of its frames. -/
def AllocInv (cm : Mem) (s : State) : Prop :=
  ∀ x ∈ s.mem.allocs, (∀ a k, x.contains a k = true → cm.valid a k = true) ∨ x.base ∈ slotBases s

theorem allocInv_step {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    (hk : EnvKeepsAllocs env) {cm : Mem} {s : State} (hI : LInv P s) (hp : AllocInv cm s) :
    (∀ s1, step env P s = .next s1 → AllocInv cm s1) ∧
    (∀ v m, step env P s = .done v m → ∀ a k, m.valid a k = true → cm.valid a k = true) := by
  refine ⟨fun s1 h => ?_, fun v m h => ?_⟩
  · rcases step_next_cases hP hI h with ⟨hc, hsl, ⟨-, hal⟩ | ⟨n, g, vals, rv, hg, hr⟩⟩ |
      ⟨c, hc, hcs, g, vals, he⟩ | ⟨c, hc, hsl, hm⟩
    · intro x hx
      rw [hal] at hx
      rcases hp x hx with h1 | h1
      · exact .inl h1
      · exact .inr (by simpa [slotBases, hc, hsl] using h1)
    · intro x hx
      rcases hp x (hk n g hg vals s.mem rv s1.mem hr x hx) with h1 | h1
      · exact .inl h1
      · exact .inr (by simpa [slotBases, hc, hsl] using h1)
    · obtain ⟨_, _, _, _, _, _, hal, -⟩ := Opt.enterFunc_ok he
      intro x hx
      have := enterSlots_allocs g s.mem x
      rw [hal] at this
      rcases this hx with h1 | h1
      · rcases hp x h1 with h2 | h2
        · exact .inl h2
        · refine .inr ?_
          simp only [slotBases, hc, List.map_cons, List.flatMap_cons, List.mem_append] at h2 ⊢
          rw [hcs]
          rcases h2 with h2 | h2
          · exact .inr (.inl h2)
          · exact .inr (.inr h2)
      · exact .inr (by simp only [slotBases, List.flatMap_cons, List.mem_append]; exact .inl h1)
    · intro x hx
      rw [hm, Mem.leave_allocs] at hx
      simp only [Mem.free, List.mem_filter, Bool.not_eq_true'] at hx
      obtain ⟨hx, hnb⟩ := hx
      rcases hp x hx with h1 | h1
      · exact .inl h1
      · refine .inr ?_
        simp only [slotBases, hc, List.map_cons, List.flatMap_cons, List.mem_append] at h1 ⊢
        rw [hsl]
        rcases h1 with h1 | h1 | h1
        · exact absurd h1 (by simpa using hnb)
        · exact .inl h1
        · exact .inr h1
  · obtain ⟨hc, hm⟩ := step_done_mem hP hI h
    intro a k hv
    rw [hm, Mem.leave_valid] at hv
    simp only [Mem.valid, Mem.free, List.any_eq_true, List.mem_filter, Bool.not_eq_true'] at hv
    obtain ⟨x, ⟨hx, hnb⟩, hc'⟩ := hv
    rcases hp x hx with h1 | h1
    · exact h1 a k hc'
    · simp only [slotBases, hc, List.map_nil, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] at h1
      exact absurd h1 (by simpa using hnb)

/-- **A returning run creates no allocation**: from a state whose allocations are within `cm`'s
valid bytes or slots of its frames, a returning whole-program run gives a memory valid only
where `cm` is (when the externs create no allocation). -/
theorem runLoop_allocs {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    (hk : EnvKeepsAllocs env) {cm : Mem} :
    ∀ (N : Nat) (s : State) (vals : List Val) (mem : Mem), LInv P s → AllocInv cm s →
      runLoop env P N s = .returned vals mem → ∀ a k, mem.valid a k = true → cm.valid a k = true
  | 0, _, _, _, _, _, h => by simp at h
  | N + 1, s, vals, mem, hI, hp, h => by
    rw [runLoop_succ'] at h
    have hs := allocInv_step hP hk hI hp
    cases hst : step env P s with
    | next s1 =>
      rw [hst] at h
      exact runLoop_allocs hP hk N s1 vals mem (step_next_linv hP hI hst).1 (hs.1 s1 hst) h
    | done v m =>
      rw [hst] at h
      simp only [afterStep, Outcome.returned.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hs.2 v m hst
    | trapped c => rw [hst] at h; cases h
    | stuck m => rw [hst] at h; cases h

/-- The entry state of an activation: its allocations are the memory's and its slots. -/
theorem initState_allocInv {P : Program} {n : String} {vals : List Val} {cm : Mem} {cs : State}
    (hi : initState P n vals cm = .ok cs) : AllocInv cm cs := by
  simp only [initState, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.pure_eq_ok] at hi
  obtain ⟨g, -, ⟨fr, mem'⟩, he, rfl⟩ := hi
  obtain ⟨_, _, _, _, _, _, hal, -⟩ := Opt.enterFunc_ok he
  intro x hx
  have := enterSlots_allocs g cm x
  rw [hal] at this
  rcases this hx with h1 | h1
  · exact .inl fun a k hc => List.any_eq_true.mpr ⟨x, h1, hc⟩
  · exact .inr (by simp only [slotBases, List.flatMap_cons, List.mem_append]; exact .inl h1)

end Clif
