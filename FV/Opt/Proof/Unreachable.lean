import FV.Opt.Proof.SemFacts

/-!
# `removeUnreachable` refines (`Opt.removeUnreachable_sim`)

`removeUnreachable` validates its result (`Opt.unreachableOk`): same header, the entry block and
a subset of the blocks, each branch target of a kept block resolving to the same block. A frame
of `f` and the same frame running `g` then step identically (`Opt.lstep_withFunc`).
-/

namespace Opt

open Clif

/-- Replace the function of a local step's frames. -/
def LRes.withFunc (g : Function) : LRes → LRes
  | .next fr m => .next { fr with func := g } m
  | r => r

def resMap {α β : Type} (h : α → β) : Res α → Res β
  | .ok a => .ok (h a)
  | .trap c => .trap c
  | .stuck m => .stuck m

/-- A frame steps the same in any function with the same header and the same targets for its
terminator's successors. -/
theorem lstep_withFunc {fr : Frame} {g : Function} {m : Mem}
    (hext : g.externs = fr.func.externs) (hglob : g.globals = fr.func.globals)
    (hsig : g.sig = fr.func.sig)
    (hsucc : ∀ id ∈ termSuccs fr.term, g.block? id = fr.func.block? id) :
    lstep { fr with func := g } m = (lstep fr m).withFunc g := by
  obtain ⟨func, regs, slots, body, term⟩ := fr
  simp only at hext hglob hsig hsucc
  have hgm : ∀ xs, Frame.getMany ⟨g, regs, slots, body, term⟩ xs =
      Frame.getMany ⟨func, regs, slots, body, term⟩ xs := fun xs => getMany_congr (fun _ _ => rfl)
  have heb : ∀ bc, bc.block ∈ termSuccs term →
      enterBlock ⟨g, regs, slots, body, term⟩ bc =
        resMap (fun fr' => { fr' with func := g }) (enterBlock ⟨func, regs, slots, body, term⟩ bc) := by
    intro bc hbc
    simp only [enterBlock, hsucc _ hbc, hgm]
    cases func.block? bc.block with
    | none => rfl
    | some b =>
      simp only [Res.ofOption, Res.ok_bind]
      cases Frame.getMany ⟨func, regs, slots, body, term⟩ bc.args with
      | trap c => rfl
      | stuck m => rfl
      | ok args =>
        simp only [Res.ok_bind, checkTys, Res.check]
        split
        · simp only [Res.ok_bind]
          cases regs.setMany _ args <;> rfl
        · rfl
  have hwr : ∀ {α : Type} (r : Res α) (k : α → LRes),
      (LRes.ofRes r k).withFunc g = LRes.ofRes r (fun a => (k a).withFunc g) := by
    intro α r k; cases r <;> rfl
  cases body with
  | nil =>
    cases term with
    | jump d =>
      simp only [lstep, heb d (by simp [termSuccs]), hwr]
      cases enterBlock _ d <;> rfl
    | brif c t e =>
      simp only [lstep, Frame.get, hwr]
      cases regs c with
      | none => rfl
      | some cv =>
        simp only [Res.ofOption, LRes.ofRes]
        rw [heb _ (by split <;> simp [termSuccs])]
        cases enterBlock _ _ <;> rfl
    | brTable x d t =>
      simp only [lstep, Frame.get, hwr]
      cases regs x with
      | none => rfl
      | some xv =>
        simp only [Res.ofOption, LRes.ofRes]
        rw [heb _ (by
          simp only [termSuccs, List.mem_cons, List.mem_map]
          cases h : t[xv.toNat]? with
          | none => simp
          | some bc => exact .inr ⟨bc, List.mem_of_getElem? h, rfl⟩)]
        cases enterBlock _ _ <;> rfl
    | ret xs =>
      simp only [lstep, hgm, hwr]
      cases Frame.getMany _ xs <;> rfl
    | returnCall fn args =>
      have : tailArgs ⟨g, regs, slots, [], .returnCall fn args⟩ fn args =
          tailArgs ⟨func, regs, slots, [], .returnCall fn args⟩ fn args := by
        simp only [tailArgs, Function.extern?, hext, hsig, hgm]
      simp only [lstep, this, hwr]
      cases tailArgs _ fn args <;> rfl
    | trap c => rfl
  | cons st rest =>
    simp only [lstep]
    split
    · rename_i fn args _
      have : callArgs ⟨g, regs, slots, st :: rest, term⟩ fn args =
          callArgs ⟨func, regs, slots, st :: rest, term⟩ fn args := by
        simp only [callArgs, Function.extern?, hext, hgm]
      simp only [this, hwr]
      cases callArgs _ fn args <;> rfl
    · rw [evalInst_congr (fr := ⟨func, regs, slots, st :: rest, term⟩)
        (fr' := ⟨g, regs, slots, st :: rest, term⟩) hglob hext rfl (fun _ _ => rfl), hwr]
      cases evalInst _ m _ with
      | ok p => obtain ⟨vals, m'⟩ := p; simp only [LRes.ofRes]; split <;> rfl
      | trap c => rfl
      | stuck msg => rfl

theorem block?_mem {f : Function} {id : BlockId} {b : Block} (h : f.block? id = some b) :
    b ∈ f.blocks := List.mem_of_find?_eq_some h

/-- The facts of `unreachableOk`. -/
theorem unreachableOk_spec {f g : Function} (h : unreachableOk f g = true) :
    g.name = f.name ∧ g.sig = f.sig ∧ g.slots = f.slots ∧ g.globals = f.globals ∧
      g.externs = f.externs ∧ g.blocks.head? = f.blocks.head? ∧
      ∀ b ∈ g.blocks, ∀ id ∈ termSuccs b.term, (g.block? id).isSome ∧ g.block? id = f.block? id := by
  simp only [unreachableOk, sameHeader, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, fun b hb id hid => by simpa using (h7 b hb).2 id hid⟩

/-- **`removeUnreachable` refines.** -/
theorem removeUnreachable_sim (f : Function) : FunSim f (removeUnreachable f) := by
  unfold removeUnreachable
  by_cases hok : unreachableOk f (removeUnreachableRaw f) = true
  case neg => simp only [hok]; exact FunSim.refl f
  simp only [hok, ite_true]
  generalize removeUnreachableRaw f = g at hok ⊢
  obtain ⟨hn, hs, hsl, hgl, hex, hhd, hbl⟩ := unreachableOk_spec hok
  let R : Frame → Frame → Prop := fun fr fr' =>
    fr.func = f ∧ fr' = { fr with func := g } ∧ ∃ b ∈ g.blocks, fr.term = b.term
  have hstep : ∀ fr m, R fr { fr with func := g } →
      lstep { fr with func := g } m = (lstep fr m).withFunc g := by
    rintro fr m ⟨hf, -, b, hb, ht⟩
    refine lstep_withFunc (by rw [hf, hex]) (by rw [hf, hgl]) (by rw [hf, hs]) fun id hid => ?_
    rw [hf]; exact (hbl b hb id (ht ▸ hid)).2
  refine ⟨hn, hs, hsl, fun syms => ⟨R, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩⟩
  · rintro fr _ ⟨hf, rfl, -⟩; exact ⟨rfl, by simp [hf, hs]⟩
  · rintro fr _ m fr1 m1 hr hm hl
    obtain ⟨hf, rfl, b, hb, ht⟩ := hr
    refine ⟨{ fr1 with func := g }, .single (by rw [hstep fr m ⟨hf, rfl, b, hb, ht⟩, hl]; rfl),
      (lstep_next_frame hl).1.trans hf, rfl, ?_⟩
    -- the new terminator is the old one, or that of a branch target (a kept block)
    obtain ⟨func, regs, slots, body, term⟩ := fr
    simp only at hf ht
    subst hf
    cases body with
    | cons st rest =>
      simp only [lstep] at hl
      split at hl
      · simp only [LRes.ofRes] at hl; split at hl <;> cases hl
      · simp only [LRes.ofRes] at hl
        split at hl <;> (try cases hl)
        split at hl <;> cases hl
        exact ⟨b, hb, ht⟩
    | nil =>
      have hent : ∀ bc fr2, bc.block ∈ termSuccs term →
          enterBlock ⟨func, regs, slots, [], term⟩ bc = .ok fr2 → ∃ b ∈ g.blocks, fr2.term = b.term := by
        intro bc fr2 hbc he
        obtain ⟨b2, _, _, hb2, _, _, _, rfl⟩ := enterBlock_ok he
        simp only at hb2
        obtain ⟨hsome, heq⟩ := hbl b hb bc.block (ht ▸ hbc)
        rw [← heq] at hb2
        exact ⟨b2, block?_mem hb2, rfl⟩
      simp only [lstep] at hl
      cases term with
      | jump d =>
        simp only [LRes.ofRes] at hl; split at hl <;> cases hl
        exact hent d _ (by simp [termSuccs]) ‹_›
      | brif c t e =>
        simp only [LRes.ofRes] at hl; split at hl <;> try cases hl
        split at hl <;> cases hl
        refine hent _ _ ?_ ‹_›
        split <;> simp [termSuccs]
      | brTable x d t =>
        simp only [LRes.ofRes] at hl; split at hl <;> try cases hl
        split at hl <;> cases hl
        refine hent _ _ ?_ ‹_›
        simp only [termSuccs, List.mem_cons, List.mem_map]
        rename_i xv _ _ _
        cases h : t[xv.toNat]? with
        | none => simp
        | some bc => exact .inr ⟨bc, List.mem_of_getElem? h, rfl⟩
      | ret xs => simp only [LRes.ofRes] at hl; split at hl <;> cases hl
      | returnCall fn args => simp only [LRes.ofRes] at hl; split at hl <;> cases hl
      | trap c => cases hl
  · rintro fr _ m ext vals rs rest hr hm hl
    obtain ⟨hf, rfl, b, hb, ht⟩ := hr
    refine ⟨{ fr with func := g }, rs, rest, .refl _ _,
      by rw [hstep fr m ⟨hf, rfl, b, hb, ht⟩, hl]; rfl, ?_⟩
    intro vs regs _ hset
    exact ⟨regs, hset, hf, rfl, b, hb, ht⟩
  · rintro fr _ m vals hr hm hl
    obtain ⟨hf, rfl, b, hb, ht⟩ := hr
    exact ⟨_, .refl _ _, by rw [hstep fr m ⟨hf, rfl, b, hb, ht⟩, hl]; rfl⟩
  · rintro fr _ m ext vals hr hm hl
    obtain ⟨hf, rfl, b, hb, ht⟩ := hr
    exact ⟨_, .refl _ _, by rw [hstep fr m ⟨hf, rfl, b, hb, ht⟩, hl]; rfl⟩
  · rintro fr _ m c hr hm hl
    obtain ⟨hf, rfl, b, hb, ht⟩ := hr
    exact ⟨_, m, .refl _ _, by rw [hstep fr m ⟨hf, rfl, b, hb, ht⟩, hl]; rfl⟩
  · intro b hb
    have hb' : g.entry? = some b := by simpa [Function.entry?, hhd] using hb
    refine ⟨b, hb', rfl, fun args regs slots _ _ _ => ⟨rfl, rfl, b, ?_, rfl⟩⟩
    exact List.mem_of_mem_head? hb'

end Opt
