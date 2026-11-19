import FV.Opt.Proof.SemSimM

/-!
# When `g` does not simulate `f` (#1119, negative witnesses)

Criteria on the entry frames of `f` and `g` (same arguments, no stack slots) in one memory. Then
no memory-aware simulation relates them, so `check_sound` forces the re-check to reject every
certificate for such a pair (`FVTest/Opt/MidValNegWitness.lean`):

* `not_funSimMU_trap`: `f` traps at its first step while `g` can neither step nor trap;
* `not_funSimMU_ret`: `f` steps once and returns while `g` is `stuck` at once;
* `not_funSimMU_ret_ne`: `f` runs by local steps (the memory may change) to a `return` of
  `vals`, `g` runs by local steps to a `return` of other values `vals'`;
* `not_funSimMU_call_ret`: both run by local steps to a `call`; after it returns `vs` in a
  memory `m'` of one's choice (with the same symbols), `f` runs to a `return` of `vals` and `g` to
  a `return` of other values. A simulation must relate the continuations at **every** memory the
  callee may leave (`ContM`).

Both multi-step criteria rest on `lstep` being a function: two runs from one frame that both stop
(no further local step) stop at the same frame and memory (`LStar.det`), so related frames
return the same values (`IsSimM.ret_eq`).
-/

namespace Opt

open Clif

/-- From a frame that cannot step, `LStar` stays put. -/
theorem LStar.of_no_next {fr : Frame} {m : Mem} (h : ∀ fr1 m1, lstep fr m ≠ .next fr1 m1)
    {fr2 : Frame} {m2 : Mem} (hs : LStar fr m fr2 m2) : fr2 = fr ∧ m2 = m := by
  cases hs with
  | refl => exact ⟨rfl, rfl⟩
  | step h1 _ => exact absurd h1 (h _ _)

/-- `lstep` is a function: two runs of local steps from one frame and memory that both stop (no
further `next` step) stop at the same frame and memory. -/
theorem LStar.det {fr : Frame} {m : Mem} {fr2 : Frame} {m2 : Mem} (h2 : LStar fr m fr2 m2)
    (hn2 : ∀ fr1 m1, lstep fr2 m2 ≠ .next fr1 m1) {fr3 : Frame} {m3 : Mem}
    (h3 : LStar fr m fr3 m3) (hn3 : ∀ fr1 m1, lstep fr3 m3 ≠ .next fr1 m1) :
    fr3 = fr2 ∧ m3 = m2 := by
  induction h2 with
  | refl => exact LStar.of_no_next hn2 h3
  | step h1 _ ih =>
    cases h3 with
    | refl => exact absurd h1 (hn3 _ _)
    | step h1' h3' =>
      rw [h1] at h1'
      obtain ⟨rfl, rfl⟩ := LRes.next.inj h1'
      exact ih hn2 h3'

/-- Related frames that both run by local steps to a `return` return the same values. -/
theorem IsSimM.ret_eq {syms : String → Option Nat} {R : Frame → Frame → Mem → Prop}
    (hR : IsSimM syms R) {fr fr' : Frame} {m : Mem} (h : R fr fr' m) (hm : m.symbols = syms)
    {fr1 : Frame} {m1 : Mem} {vals : List Val} (hf : LStar fr m fr1 m1)
    (hf1 : lstep fr1 m1 = .ret vals) {fr2 : Frame} {m2 : Mem} {vals' : List Val}
    (hg : LStar fr' m fr2 m2) (hg1 : lstep fr2 m2 = .ret vals') : vals' = vals := by
  obtain ⟨g1, hs1, hr1⟩ := hR.star h hm hf
  obtain ⟨g2, hs2, hr2⟩ := hR.ret hr1 ((LStar.frame hf).2.2.trans hm) hf1
  obtain ⟨rfl, rfl⟩ := LStar.det hg (fun _ _ h => by rw [hg1] at h; cases h) (hs1.trans hs2)
    (fun _ _ h => by rw [hr2] at h; cases h)
  rw [hr2] at hg1
  exact (LRes.ret.inj hg1).symm

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

/-- `f` and `g` run by local steps (the memory may change) to `return`s of different values: no
simulation. -/
theorem not_funSimMU_ret_ne {f g : Function} {b b' : Block} (hb : f.entry? = some b)
    (hb' : g.entry? = some b') {args : List Val} {regs : Regs} {m : Mem}
    (hty : args.map (·.ty) = b.params.map (·.2))
    (hr : Regs.empty.setMany (b.params.map (·.1)) args = some regs) (hsl : f.slots = [])
    {fr1 : Frame} {m1 : Mem} {vals : List Val} (hf : LStar ⟨f, regs, [], b.body, b.term⟩ m fr1 m1)
    (hf1 : lstep fr1 m1 = .ret vals) {fr2 : Frame} {m2 : Mem} {vals' : List Val}
    (hg : LStar ⟨g, regs, [], b'.body, b'.term⟩ m fr2 m2) (hg1 : lstep fr2 m2 = .ret vals')
    (hne : vals' ≠ vals) : ¬ FunSimMU f g := by
  intro hs
  obtain ⟨R, hR, hrel⟩ := hs.entry_rel hb hb' hty hr hsl
  exact hne (hR.toIsSimM.ret_eq hrel rfl hf hf1 hg hg1)

/-- `f` and `g` run by local steps to a `call`; when it returns the values `vs` in a memory `m'`
with the same symbols, `f` and `g` run by local steps to `return`s of different values: no
simulation. -/
theorem not_funSimMU_call_ret {f g : Function} {b b' : Block} (hb : f.entry? = some b)
    (hb' : g.entry? = some b') {args : List Val} {regs : Regs} {m : Mem}
    (hty : args.map (·.ty) = b.params.map (·.2))
    (hr : Regs.empty.setMany (b.params.map (·.1)) args = some regs) (hsl : f.slots = [])
    {fc : Frame} {mc : Mem} {ext : ExtFunc} {cvals : List Val} {rs : List ValueId}
    {rest : List Stmt} (hf : LStar ⟨f, regs, [], b.body, b.term⟩ m fc mc)
    (hfc : lstep fc mc = .call ext cvals rs rest)
    {gc : Frame} {mgc : Mem} {ext' : ExtFunc} {cvals' : List Val} {rs' : List ValueId}
    {rest' : List Stmt} (hg : LStar ⟨g, regs, [], b'.body, b'.term⟩ m gc mgc)
    (hgc : lstep gc mgc = .call ext' cvals' rs' rest')
    {vs : List Val} (hvs : vs.map (·.ty) = AbiParam.tys ext.sig.returns) {m' : Mem}
    (hm' : m'.symbols = m.symbols) {regsc regsc' : Regs} (hrc : fc.regs.setMany rs vs = some regsc)
    (hrc' : gc.regs.setMany rs' vs = some regsc')
    {fr1 : Frame} {m1 : Mem} {vals : List Val}
    (hf' : LStar { fc with regs := regsc, body := rest } m' fr1 m1)
    (hf1 : lstep fr1 m1 = .ret vals) {fr2 : Frame} {m2 : Mem} {vals' : List Val}
    (hg' : LStar { gc with regs := regsc', body := rest' } m' fr2 m2)
    (hg1 : lstep fr2 m2 = .ret vals') (hne : vals' ≠ vals) : ¬ FunSimMU f g := by
  intro hs
  obtain ⟨R, hR, hrel⟩ := hs.entry_rel hb hb' hty hr hsl
  obtain ⟨g1, hs1, hr1⟩ := hR.toIsSimM.star hrel rfl hf
  obtain ⟨g2, rs2, rest2, hs2, hc2, hk⟩ := hR.toIsSimM.call hr1 (LStar.frame hf).2.2 hfc
  obtain ⟨rfl, rfl⟩ := LStar.det hg (fun _ _ h => by rw [hgc] at h; cases h) (hs1.trans hs2)
    (fun _ _ h => by rw [hc2] at h; cases h)
  rw [hgc] at hc2
  obtain ⟨-, -, rfl, rfl⟩ := LRes.call.inj hc2
  obtain ⟨regs2, hr2, hk2⟩ := hk vs regsc m' hvs hm' hrc
  rw [hrc'] at hr2
  cases hr2
  exact hne (hR.toIsSimM.ret_eq hk2 hm' hf' hf1 hg' hg1)

end Opt
