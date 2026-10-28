import FV.E2E.SrcBounded
import FV.E2E.LinkPlaceB

/-! # Bounded memories of placed runs under the slot-byte oracle (SEM1)

`bounded_placed` (`SrcBounded.lean`) with the slot-byte oracle on: the start memory's oracle has
`init = some ini`, the externs advance its counter (`EnvAdv`) instead of keeping the oracle, and
each placed activation with slots fills its slots with the oracle's bytes (`initSlots`), which
changes no allocation. The conclusion is the same. -/

namespace E2E.SrcBounded

open Clif Opt.Legal

/-- The invariant of `bounded_placedB`: `PlacedInv` with the slot-byte counter advanced. -/
def PlacedInvB (P : Program) (β : Nat → Function → Nat) (Q : Function → Prop)
    (fr : String → Option (Nat × (SlotId → Nat))) (sps : List (BitVec 64)) (ini : SlotInit)
    (t : State) : Prop :=
  LInv P t ∧ MemBounded t.mem ∧ Q t.frame.func ∧ (∀ c ∈ t.callers, Q c.1.func) ∧
    ∃ l e, t.mem.place = some ⟨l ++ sps, fr, some (ini.adv e)⟩ ∧ SpOk β l (funcs t)

/-- `initPlace` under the slot-byte oracle: the counter advanced by `0` or `1`. -/
theorem initPlace_adv (slots : List (SlotId × StackSlot)) (pl : Place) (ini : SlotInit)
    (hi : pl.init = some ini) :
    ∃ e, initPlace slots (some ini) (some pl) = some { pl with init := some (ini.adv e) } := by
  by_cases hs : slots.isEmpty
  · refine ⟨0, ?_⟩
    simp only [initPlace, hs, ↓reduceIte]
    obtain ⟨sps, frm, i⟩ := pl
    cases hi
    rfl
  · refine ⟨1, ?_⟩
    simp only [initPlace, hs, Option.map_some, Place.advance]
    rfl

/-- **Bounded memories, placed slots, slot-byte oracle**: `bounded_placed` from a memory whose
oracle has the slot-byte oracle `ini`, under externs advancing its counter (`EnvAdv`). -/
theorem bounded_placedB {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    (hkp : EnvAdv env) (hk : EnvKeepsBounded env)
    (β : Nat → Function → Nat) (Q : Function → Prop)
    (fr : String → Option (Nat × (SlotId → Nat))) {s : State} (hI : LInv P s)
    (hM : MemBounded s.mem) (hcs : s.callers = []) {c : BitVec 64} {sps : List (BitVec 64)}
    {ini : SlotInit}
    (hpl : s.mem.place = some ⟨c :: sps, fr, some ini⟩) (hc : β 0 s.frame.func ≤ c.toNat)
    (hQ : Q s.frame.func)
    (hent : ∀ t t1, SReach env P s t → LInv P t → Q t.frame.func → step env P t = .next t1 →
      t1.callers.length = t.callers.length + 1 → EnterVia P t.frame.func t1.frame.func t.mem →
      ∃ d off, fr t1.frame.func.name = some (d, off) ∧
        (∀ p ∈ t1.frame.func.slots, off p.1 + p.2.size ≤ d) ∧
        d + β (t.callers.length + 1) t1.frame.func ≤ β t.callers.length t.frame.func ∧
        Q t1.frame.func) :
    ∀ s', SReach env P s s' → MemBounded s'.mem := by
  have key : ∀ t t', SReach env P t t' → SReach env P s t → PlacedInvB P β Q fr sps ini t →
      PlacedInvB P β Q fr sps ini t' := by
    intro t t' h
    induction h with
    | refl => exact fun _ hi => hi
    | @step t0 t1 _ hs _ ih =>
      intro hr ⟨hIt, hm, hq, hqc, l, e, hpl0, hsp⟩
      have hr1 : SReach env P s t1 := hr.trans (.step hs (.refl _))
      have hI1 := (step_next_linv hP hIt hs).1
      refine ih hr1 ?_
      rcases step_next_rich hP hIt hs with ⟨hc1, hf1, hloc⟩ | ⟨cc, hc1, hcf, h, vals, hvia, he⟩ |
        ⟨cc, hc0, hf1, hm1⟩
      · -- a step of the running frame
        have hfs : funcs t1 = funcs t0 := by simp only [funcs, hc1, hf1]
        refine ⟨hI1, ?_, hf1 ▸ hq, hc1 ▸ hqc, ?_⟩
        · rcases hloc with ⟨-, hal⟩ | ⟨n, g, vals, rv, hg, hret⟩
          · exact bounded_of_allocs hal hm
          · exact hk n g hg vals _ rv _ hret hm
        · rcases hloc with ⟨hp, -⟩ | ⟨n, g, vals, rv, hg, hret⟩
          · exact ⟨l, e, by rw [hp]; exact hpl0, hfs ▸ hsp⟩
          · obtain ⟨e', he'⟩ := hkp n g hg vals _ rv _ hret
            refine ⟨l, e + e', ?_, hfs ▸ hsp⟩
            rw [he' _ _ hpl0 rfl, SlotInit.adv_adv]
      · -- entering `h`
        obtain ⟨_, _, _, _, _, _, hal, hfr⟩ := Opt.enterFunc_ok he
        have hh : t1.frame.func = h := by rw [hfr]
        have hlen : t1.callers.length = t0.callers.length + 1 := by rw [hc1]; rfl
        obtain ⟨d, off, hfd, hfit, hle, hqh⟩ :=
          hent t0 t1 hr hIt hq hs hlen (by rw [hh]; exact hvia)
        rw [hh] at hfd hfit hle hqh
        -- the running activation's stack pointer
        obtain ⟨sp, l', rfl⟩ : ∃ sp l', l = sp :: l' := by
          cases l with
          | nil => simp [funcs, SpOk] at hsp
          | cons sp l' => exact ⟨sp, l', rfl⟩
        have hsp0 : β t0.callers.length t0.frame.func ≤ sp.toNat := by
          simpa [funcs, SpOk] using hsp.1
        have hdle : d ≤ sp.toNat := by omega
        have hsub := toNat_sub_of_le hdle
        -- the slots placed below `sp`, then filled by the oracle
        have hes : enterSlots h t0.mem = initSlots h.slots (sp - BitVec.ofNat 64 d) off
            (some (ini.adv e)) (h.slots.foldl (placeStep (sp - BitVec.ofNat 64 d) off)
            ([], { t0.mem with place := some ⟨(sp - BitVec.ofNat 64 d) :: (sp :: l' ++ sps), fr,
              some (ini.adv e)⟩ })) := by
          simp only [enterSlots, hpl0, hfd, List.cons_append, List.headD]
          rfl
        rw [hes] at hal
        obtain ⟨-, -, h3, -⟩ := placeSlots_spec (sp - BitVec.ofNat 64 d) off h.slots
          ([], { t0.mem with place := some ⟨(sp - BitVec.ofNat 64 d) :: (sp :: l' ++ sps), fr,
            some (ini.adv e)⟩ })
        have h5 : (h.slots.foldl (placeStep (sp - BitVec.ofNat 64 d) off)
            ([], { t0.mem with place := some ⟨(sp - BitVec.ofNat 64 d) :: (sp :: l' ++ sps), fr,
              some (ini.adv e)⟩ })).2.place =
            some ⟨(sp - BitVec.ofNat 64 d) :: (sp :: l' ++ sps), fr, some (ini.adv e)⟩ :=
          (placeSlots_facts (sp - BitVec.ofNat 64 d) off h.slots
            ([], { t0.mem with place := some ⟨(sp - BitVec.ofNat 64 d) :: (sp :: l' ++ sps), fr,
              some (ini.adv e)⟩ })).1
        have hal2 := congrArg (fun r : List (SlotId × Nat) × Mem => r.2.allocs) hal
        have hpl2 := congrArg (fun r : List (SlotId × Nat) × Mem => r.2.place) hal
        simp only at hal2 hpl2
        rw [initSlots_allocs] at hal2
        rw [initSlots_place, h5] at hpl2
        obtain ⟨e', he'⟩ := initPlace_adv h.slots
          ⟨(sp - BitVec.ofNat 64 d) :: (sp :: l' ++ sps), fr, some (ini.adv e)⟩ (ini.adv e) rfl
        rw [he'] at hpl2
        refine ⟨hI1, fun a n hv => ?_, hh ▸ hqh, ?_, (sp - BitVec.ofNat 64 d) :: sp :: l', e + e',
          ?_, ?_⟩
        · simp only [Mem.valid, List.any_eq_true] at hv
          obtain ⟨x, hx, hcx⟩ := hv
          rw [← hal2] at hx
          rcases h3 x hx with hx' | ⟨p, hp, rfl⟩
          · exact hm a n (by simp only [Mem.valid, List.any_eq_true]; exact ⟨x, hx', hcx⟩)
          · simp only [Alloc.contains, Bool.and_eq_true, decide_eq_true_eq] at hcx
            have := hfit p hp
            have := sp.isLt
            omega
        · rw [hc1]
          intro c' hc'
          rcases List.mem_cons.1 hc' with rfl | hc'
          · rw [hcf]; exact hq
          · exact hqc c' hc'
        · rw [← hpl2, SlotInit.adv_adv]; rfl
        · refine ⟨?_, ?_⟩
          · simp only [hh, hc1, List.length_map, List.length_cons]
            rw [hsub]; omega
          · simpa [funcs, hc1, hcf] using hsp
      · -- returning to the caller
        obtain ⟨sp, l', rfl⟩ : ∃ sp l', l = sp :: l' := by
          cases l with
          | nil => simp [funcs, SpOk] at hsp
          | cons sp l' => exact ⟨sp, l', rfl⟩
        refine ⟨hI1, by rw [hm1]; exact bounded_ret hm, ?_, ?_, l', e, ?_, ?_⟩
        · rw [hf1]; exact hqc cc (by rw [hc0]; exact List.mem_cons_self ..)
        · intro c' hc'; exact hqc c' (by rw [hc0]; exact List.mem_cons_of_mem _ hc')
        · rw [hm1]
          simp only [Mem.leave, Mem.free, hpl0, List.cons_append, List.tail_cons]
        · have := hsp.2
          simpa [funcs, hc0, hf1] using this
  intro s' hr
  have h0 : PlacedInvB P β Q fr sps ini s := by
    refine ⟨hI, hM, hQ, ?_, [c], 0, ?_, ?_⟩
    · rw [hcs]; intro _ h; cases h
    · rw [hpl]; rfl
    · simp only [funcs, hcs, List.map_nil, SpOk, List.length_nil]
      exact ⟨hc, trivial⟩
  exact (key s s' hr (.refl _) h0).2.1

end E2E.SrcBounded
