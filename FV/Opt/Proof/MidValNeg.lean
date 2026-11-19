import FV.Opt.Proof.SemSimM

/-!
# When `g` does not simulate `f` (#1119, negative witnesses)

Two criteria, on the entry frames of `f` and `g` (same arguments, no stack slots) in one memory:
`f` traps at its first step while `g` can neither step nor trap (`not_funSimMU_trap`), or `f`
steps once and returns while `g` is `stuck` at once (`not_funSimMU_ret`). Then no memory-aware
simulation relates them, so `check_sound` forces the re-check to reject every certificate for
such a pair (`FVTest/Opt/MidValNegWitness.lean`).
-/

namespace Opt

open Clif

/-- From a frame that cannot step, `LStar` stays put. -/
theorem LStar.of_no_next {fr : Frame} {m : Mem} (h : ∀ fr1 m1, lstep fr m ≠ .next fr1 m1)
    {fr2 : Frame} {m2 : Mem} (hs : LStar fr m fr2 m2) : fr2 = fr ∧ m2 = m := by
  cases hs with
  | refl => exact ⟨rfl, rfl⟩
  | step h1 _ => exact absurd h1 (h _ _)

/-- The related entry frames of a `FunSimMU` (no stack slots). -/
theorem FunSimMU.entry_rel {f g : Function} (hs : FunSimMU f g) {b b' : Block}
    (hb : f.entry? = some b) (hb' : g.entry? = some b') {args : List Val} {regs : Regs} {m : Mem}
    (hty : args.map (·.ty) = b.params.map (·.2))
    (hr : Regs.empty.setMany (b.params.map (·.1)) args = some regs) (hsl : f.slots = []) :
    ∃ R, IsSimMU m.symbols R ∧ R ⟨f, regs, [], b.body, b.term⟩ ⟨g, regs, [], b'.body, b'.term⟩ m := by
  obtain ⟨R, hR, he⟩ := hs.sim m.symbols
  obtain ⟨b2, hb2, -, hrel⟩ := he b hb
  rw [hb'] at hb2
  cases hb2
  exact ⟨R, hR, hrel args regs [] m hty hr (by simp [hsl]) rfl⟩

/-- `f` traps at once, `g` neither steps nor traps: no simulation. -/
theorem not_funSimMU_trap {f g : Function} {b b' : Block} (hb : f.entry? = some b)
    (hb' : g.entry? = some b') {args : List Val} {regs : Regs} {m : Mem}
    (hty : args.map (·.ty) = b.params.map (·.2))
    (hr : Regs.empty.setMany (b.params.map (·.1)) args = some regs) (hsl : f.slots = [])
    {c : TrapCode} (hf : lstep ⟨f, regs, [], b.body, b.term⟩ m = .trap c)
    (hgn : ∀ fr1 m1, lstep ⟨g, regs, [], b'.body, b'.term⟩ m ≠ .next fr1 m1)
    (hgt : ∀ c', lstep ⟨g, regs, [], b'.body, b'.term⟩ m ≠ .trap c') :
    ¬ FunSimMU f g := by
  intro hs
  obtain ⟨R, hR, hrel⟩ := hs.entry_rel hb hb' hty hr hsl
  obtain ⟨fr2, m2, hst, ht⟩ := hR.toIsSimM.trap hrel rfl hf
  obtain ⟨rfl, rfl⟩ := LStar.of_no_next hgn hst
  exact hgt c ht

/-- `f` steps once and returns, `g` is `stuck` at once: no simulation. -/
theorem not_funSimMU_ret {f g : Function} {b b' : Block} (hb : f.entry? = some b)
    (hb' : g.entry? = some b') {args : List Val} {regs : Regs} {m : Mem}
    (hty : args.map (·.ty) = b.params.map (·.2))
    (hr : Regs.empty.setMany (b.params.map (·.1)) args = some regs) (hsl : f.slots = [])
    {fr1 : Frame} {vals : List Val} (hf1 : lstep ⟨f, regs, [], b.body, b.term⟩ m = .next fr1 m)
    (hf2 : lstep fr1 m = .ret vals)
    (hg : ∃ msg, lstep ⟨g, regs, [], b'.body, b'.term⟩ m = .stuck msg) :
    ¬ FunSimMU f g := by
  intro hs
  obtain ⟨R, hR, hrel⟩ := hs.entry_rel hb hb' hty hr hsl
  obtain ⟨msg, hgs⟩ := hg
  have hgn : ∀ fr1 m1, lstep ⟨g, regs, [], b'.body, b'.term⟩ m ≠ .next fr1 m1 := by
    intro _ _ h; rw [hgs] at h; cases h
  obtain ⟨g1, hs1, hr1⟩ := hR.toIsSimM.next hrel rfl hf1
  obtain ⟨rfl, -⟩ := LStar.of_no_next hgn hs1
  obtain ⟨fr2, hs2, hret⟩ := hR.toIsSimM.ret hr1 rfl hf2
  obtain ⟨rfl, -⟩ := LStar.of_no_next hgn hs2
  rw [hgs] at hret
  cases hret

end Opt
