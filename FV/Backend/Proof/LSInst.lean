import FV.Backend.Proof.LSFacts
import FV.Backend.Proof.SpillLocal

/-!
# One instruction of the Lean allocator's builder (V4b-3, #275)

`inst_facts`: for an instruction meeting `OpsOk` (in-scope operand facts) in a plan that passes
the validator (`PlanFacts`), what `Ctx.inst` computes (`InstFacts`): the checker's static checks
accept the operand registers; every move before reads a use's location and writes that use's
register, no move before writes a location another reads, the destinations are distinct; every
use is in its location (not overwritten before) or moved into its register; every move after
copies a stored def's register into its location (same conditions); and every vreg live
across the instruction that it does not define keeps its location: no move before or after and
no def writes it (`frame`).

The argument: every register the builder writes is a fixed operand register (claimed by its
vreg: `PlanFacts.claim`), a clobber, the register of the vreg written (`PlanFacts.inter`), or a
scratch register `regFree` found free over the positions it is used (`regFree_sound`), and the
registers taken for one instruction are distinct where their position ranges meet.
-/

namespace Backend.Proof.LS

open Backend Backend.LinearScan Backend.Proof.Spill

/-! ## Helpers -/

/-- Two position intervals meet. -/
private def Ov (a b : Nat × Nat) : Prop := a.1 ≤ b.2 ∧ b.1 ≤ a.2

/-- A `taken` entry of register `x` contains the interval `I`. -/
private def TK (taken : List (Reg × Nat × Nat)) (x : Reg) (I : Nat × Nat) : Prop :=
  ∃ t ∈ taken, t.1 = x ∧ t.2.1 ≤ I.1 ∧ I.2 ≤ t.2.2

/-- Two operands may share a register where their intervals meet: two uses of one vreg, or a
reuse def and the use it reuses. -/
private def Legit (j : Nat) (o : Operand) (j' : Nat) (o' : Operand) : Prop :=
  (o.kind = .use ∧ o'.kind = .use ∧ o.vreg = o'.vreg) ∨ o.con = .reuse j' ∨ o'.con = .reuse j

private theorem Legit.symm {j j' : Nat} {o o' : Operand} (h : Legit j o j' o') : Legit j' o' j o := by
  rcases h with ⟨a, b, c⟩ | h | h
  · exact .inl ⟨b, a, c.symm⟩
  · exact .inr (.inr h)
  · exact .inr (.inl h)

private theorem Ov.symm {a b : Nat × Nat} (h : Ov a b) : Ov b a := ⟨h.2, h.1⟩

private theorem TK.mono {t t' : List (Reg × Nat × Nat)} {x : Reg} {I : Nat × Nat} (h : TK t x I)
    (ht : ∀ y ∈ t, y ∈ t') : TK t' x I := by
  obtain ⟨y, hy, h1⟩ := h; exact ⟨y, ht y hy, h1⟩

private theorem Excl.mono {pl : LinearScan.Plan} {x : Reg} {s e s' e' : Nat} (h : Excl pl x s e none)
    (h1 : s ≤ s') (h2 : e' ≤ e) : Excl pl x s' e' none :=
  fun w hw q hq1 hq2 hc => h w hw q (by omega) (by omega) hc

private theorem cov_of_covI {pl : LinearScan.Plan} {v p q r : Nat} (h : pl.covI v p q = true) (h1 : p ≤ r)
    (h2 : r ≤ q) : pl.cov v r = true := by
  unfold Plan.covI at h; unfold Plan.cov
  rw [Array.any_eq_true] at h ⊢
  obtain ⟨i, hi, hh⟩ := h
  refine ⟨i, hi, ?_⟩
  revert hh
  rcases (pl.segs.getD v #[])[i] with ⟨s, e⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

private theorem loc_reg {c : LinearScan.Ctx} {w : Nat} {x : Reg} :
    c.loc w = .reg x ↔ c.pl.regOf w = some x := by
  unfold Ctx.loc Fn.loc
  split <;> simp_all

private theorem locReg_loc {c : LinearScan.Ctx} {w : Nat} {x : Reg} :
    locReg? (c.loc w) = some x ↔ c.pl.regOf w = some x := by
  unfold Ctx.loc Fn.loc
  split <;> simp_all [locReg?]

private theorem locReg_eq {l : Loc} {x : Reg} (h : locReg? l = some x) : l = .reg x := by
  cases l <;> simp_all [locReg?]

private theorem loc_stack {c : LinearScan.Ctx} {w h : Nat} {k : RegClass} (hl : c.loc w = .stack h k) :
    c.pl.regOf w = none ∧ c.pl.home.getD w 0 = h ∧ c.fn.clsOf w = k := by
  unfold Ctx.loc Fn.loc at hl
  split at hl <;> simp_all

private theorem iv_le (g : Nat) (o : Operand) : (opRange g o false).1 ≤ (opRange g o false).2 := by
  unfold opRange pos
  cases o.kind <;> simp <;> (try split) <;> omega

private theorem iv_use {g : Nat} {o : Operand} (hu : o.kind = .use) (he : o.pos = .early) :
    opRange g o false = (pos g 1, pos g 2) := by
  simp [opRange, hu, he]

private theorem iv_def {g : Nat} {o : Operand} (hd : o.kind = .def) :
    opRange g o false = (pos g (opSlot o), pos g 3) := by
  simp [opRange, hd, opSlot]

private theorem iv_true {g : Nat} {o : Operand} :
    (opRange g o true).1 = (opRange g o false).1 ∧ (opRange g o false).2 ≤ (opRange g o true).2 := by
  unfold opRange pos
  cases o.kind <;> simp only <;> split <;> simp

private theorem ov_pt {a b : Nat × Nat} (h : Ov a b) (ha : a.1 ≤ a.2) (hb : b.1 ≤ b.2) :
    ∃ q, a.1 ≤ q ∧ q ≤ a.2 ∧ b.1 ≤ q ∧ q ≤ b.2 :=
  ⟨max a.1 b.1, by simp only [Ov] at h; omega⟩

private theorem nodup_filter_map_inj {α β : Type} (p : α → Bool) (f : α → β) :
    ∀ (L : List α), ((L.filter p).map f).Nodup → ∀ {j j' : Nat} {a a' : α}, L[j]? = some a →
      L[j']? = some a' → p a = true → p a' = true → f a = f a' → j = j'
  | [], _, j, j', a, a', h, _, _, _, _ => by simp at h
  | b :: L, hn, j, j', a, a', h, h', hp, hp', hf => by
    have hmem : ∀ {k : Nat} {a'' : α}, L[k]? = some a'' → p a'' = true → f a'' ∈ (L.filter p).map f :=
      fun hk hp'' => List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨List.mem_of_getElem? hk, hp''⟩, rfl⟩
    cases j with
    | zero =>
      cases j' with
      | zero => rfl
      | succ k' =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at h h'
        subst h
        rw [List.filter_cons_of_pos hp, List.map_cons, List.nodup_cons] at hn
        exact absurd (hf ▸ hmem h' hp') hn.1
    | succ k =>
      cases j' with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at h h'
        subst h'
        rw [List.filter_cons_of_pos hp', List.map_cons, List.nodup_cons] at hn
        exact absurd (hf.symm ▸ hmem h hp) hn.1
      | succ k' =>
        simp only [List.getElem?_cons_succ] at h h'
        have hn' : ((L.filter p).map f).Nodup := by
          rw [List.filter_cons] at hn
          split at hn
          · exact (List.nodup_cons.mp hn).2
          · exact hn
        rw [nodup_filter_map_inj p f L hn' h h' hp hp' hf]

/-! ## The instruction's environment -/

/-- The facts every step of `Ctx.inst` uses (plan facts, operand facts). -/
private structure Env (vc : VCode) (c : LinearScan.Ctx) (g : Nat) (os : Array Operand) (clob : List Reg)
    (st : Nat → Operand → Bool) : Prop where
  pf : PlanFacts vc c
  occ : c.occ = c.pl.occ
  hos : c.fn.ops[g]? = some os
  ok : OpsOk os clob
  cls : ∀ o ∈ os.toList, c.fn.clsOf o.vreg = o.cls
  nv : ∀ o ∈ os.toList, o.vreg < c.fn.nv
  clob : ∀ r ∈ clob, ∀ w, c.pl.regOf w = some r → c.pl.cov w (pos g 3) = false
  st : ∀ j o, st j o = true → c.pl.cov o.vreg (pos g 4) = true

section
variable {vc : VCode} {c : LinearScan.Ctx} {g : Nat} {os : Array Operand} {clob : List Reg}
  {st : Nat → Operand → Bool}

private theorem Env.mem (_E : Env vc c g os clob st) {j : Nat} {o : Operand} (hj : os[j]? = some o) :
    o ∈ os.toList := by
  rw [← Array.getElem?_toList] at hj; exact List.mem_of_getElem? hj

private theorem tl {j : Nat} {o : Operand} (hj : os[j]? = some o) : os.toList[j]? = some o := by
  rw [Array.getElem?_toList]; exact hj

private theorem Env.early (E : Env vc c g os clob st) {j : Nat} {o : Operand} (hj : os[j]? = some o)
    (hu : o.kind = .use) : o.pos = .early := E.ok.useEarly o (E.mem hj) hu

private theorem Env.ivU (E : Env vc c g os clob st) {j : Nat} {o : Operand} (hj : os[j]? = some o)
    (hu : o.kind = .use) : opRange g o false = (pos g 1, pos g 2) := iv_use hu (E.early hj hu)

/-- An operand's vreg covers its interval. -/
private theorem Env.cov (E : Env vc c g os clob st) {j : Nat} {o : Operand} (hj : os[j]? = some o)
    {q : Nat} (h1 : (opRange g o false).1 ≤ q) (h2 : q ≤ (opRange g o false).2) : c.pl.cov o.vreg q = true := by
  cases hk : o.kind with
  | use =>
    have hc := E.pf.use g os E.hos o (E.mem hj) hk
    rw [E.ivU hj hk] at h1 h2
    have : opSlot o = 2 := by simp [opSlot, E.early hj hk]
    rw [this] at hc
    exact cov_of_covI hc (by simp only [pos] at h1 ⊢; omega) h2
  | «def» =>
    have hc := E.pf.def_ g os E.hos o (E.mem hj) hk
    rw [iv_def hk] at h1 h2
    exact cov_of_covI hc h1 h2

/-- A def's interval contains position 3. -/
private theorem iv_def3 {g : Nat} {o : Operand} (hd : o.kind = .def) :
    (opRange g o false).1 ≤ pos g 3 ∧ pos g 3 ≤ (opRange g o false).2 := by
  rw [iv_def hd]; simp only [opSlot, pos]; split <;> omega

private theorem Env.def_inj (E : Env vc c g os clob st) {j j' : Nat} {o o' : Operand}
    (hj : os[j]? = some o) (hj' : os[j']? = some o') (hd : o.kind = .def) (hd' : o'.kind = .def)
    (hv : o.vreg = o'.vreg) : j = j' :=
  nodup_filter_map_inj (·.kind == .def) (·.vreg) os.toList E.ok.defsNodup (tl hj) (tl hj')
    (by simp [hd]) (by simp [hd']) hv

/-- Two operands of one vreg with a register whose intervals meet are uses. -/
private theorem Env.sameV (E : Env vc c g os clob st) {j j' : Nat} {o o' : Operand}
    (hj : os[j]? = some o) (hj' : os[j']? = some o') (hne : j ≠ j') (hv : o.vreg = o'.vreg)
    (hr : (c.pl.regOf o.vreg).isSome) (hov : Ov (opRange g o false) (opRange g o' false)) :
    o.kind = .use ∧ o'.kind = .use := by
  cases hk : o.kind <;> cases hk' : o'.kind
  · exact ⟨rfl, rfl⟩
  · obtain ⟨hl, -⟩ := E.pf.defUse g os E.hos o' (E.mem hj') hk' (hv ▸ hr) o (E.mem hj) hk hv
    rw [E.ivU hj hk, iv_def hk', opSlot, hl] at hov
    simp [Ov, pos] at hov
  · obtain ⟨hl, -⟩ := E.pf.defUse g os E.hos o (E.mem hj) hk hr o' (E.mem hj') hk' hv.symm
    rw [E.ivU hj' hk', iv_def hk, opSlot, hl] at hov
    simp [Ov, pos] at hov
  · exact absurd (E.def_inj hj hj' hk hk' hv) hne

/-- Two fixed operands of one register whose intervals meet are uses of one vreg. -/
private theorem Env.fixFix (E : Env vc c g os clob st) {j j' : Nat} {o o' : Operand} {p : Reg}
    (hj : os[j]? = some o) (hj' : os[j']? = some o') (hne : j ≠ j') (hp : o.con = .fixed p)
    (hp' : o'.con = .fixed p) (hov : Ov (opRange g o false) (opRange g o' false)) : Legit j o j' o' := by
  have late : ∀ {k : Nat} {o'' : Operand}, os[k]? = some o'' → o''.kind = .def → o''.con = .fixed p →
      opRange g o'' false = (pos g 3, pos g 3) := by
    intro k o'' hk hd hf
    rw [iv_def hd]
    cases hpos : o''.pos
    · have := E.ok.earlyDef o'' (E.mem hk) hd hpos; rw [hf] at this; cases this
    · simp [opSlot, hpos]
  cases hk : o.kind <;> cases hk' : o'.kind
  · exact .inl ⟨hk, hk', E.ok.fixedUse o (E.mem hj) o' (E.mem hj') p hk hk' hp hp'⟩
  · rw [E.ivU hj hk, late hj' hk' hp'] at hov; simp [Ov, pos] at hov
  · rw [E.ivU hj' hk', late hj hk hp] at hov; simp [Ov, pos] at hov
  · exact absurd (E.ok.fixedDefs j j' o o' p (tl hj) (tl hj') hk hk' hp hp') hne

end

/-! ## The builder's state invariant -/

/-- What the register `x` chosen for operand `j` (`o`) satisfies in state `s`. -/
private structure Cat (c : LinearScan.Ctx) (g : Nat) (clob : List Reg) (st : Nat → Operand → Bool)
    (s : IS) (j : Nat) (o : Operand) (x : Reg) : Prop where
  ok : x.allocatable = true ∧ x.realClass? = some o.cls
  fix : ∀ p, o.con = .fixed p → x = p
  reu : ∀ ui, o.con = .reuse ui → s.R[ui]? = some (some x)
  use : o.kind = .use → c.loc o.vreg = .reg x ∨ (c.loc o.vreg, .reg x) ∈ s.pre
  dfn : o.kind = .def → st j o = true → c.loc o.vreg = .reg x ∨ (.reg x, c.loc o.vreg) ∈ s.post
  clob : o.kind = .def → x ∉ clob
  kind : c.pl.regOf o.vreg = some x ∨ (TK s.taken x (opRange g o false) ∧
    ((∃ p, o.con = .fixed p) ∨ Excl c.pl x (opRange g o false).1 (opRange g o false).2 none))

/-- **The invariant** of the builder's passes. -/
private structure Inv (c : LinearScan.Ctx) (g : Nat) (os : Array Operand) (clob : List Reg)
    (st : Nat → Operand → Bool) (s : IS) : Prop where
  size : s.R.size = os.size
  cat : ∀ (j : Nat) (o : Operand) (x : Reg), os[j]? = some o → s.R[j]? = some (some x) → Cat c g clob st s j o x
  disj : ∀ (j : Nat) (o : Operand) (j' : Nat) (o' : Operand) (x : Reg), os[j]? = some o → os[j']? = some o' → j ≠ j' → s.R[j]? = some (some x) →
    s.R[j']? = some (some x) → Ov (opRange g o false) (opRange g o' false) → Legit j o j' o'
  pre : ∀ m ∈ s.pre, ∃ (j : Nat) (o : Operand) (x : Reg), os[j]? = some o ∧ o.kind = .use ∧ s.R[j]? = some (some x) ∧
    m = (c.loc o.vreg, .reg x)
  post : ∀ m ∈ s.post, ∃ (j : Nat) (o : Operand) (x : Reg), os[j]? = some o ∧ o.kind = .def ∧ st j o = true ∧
    s.R[j]? = some (some x) ∧ m = (.reg x, c.loc o.vreg)
  scr : ∀ (v : Nat) (r : Reg), (v, r) ∈ s.useScr → ∃ (j : Nat) (o : Operand), os[j]? = some o ∧ o.kind = .use ∧ o.vreg = v ∧
    s.R[j]? = some (some r) ∧ Excl c.pl r (pos g 1) (pos g 2) none ∧ TK s.taken r (pos g 1, pos g 2) ∧
    ∀ (j' : Nat) (o' : Operand), os[j']? = some o' → s.R[j']? = some (some r) →
      Ov (pos g 1, pos g 2) (opRange g o' false) → o'.kind = .use ∧ o'.vreg = v

section
variable {vc : VCode} {c : LinearScan.Ctx} {g : Nat} {os : Array Operand} {clob : List Reg}
  {st : Nat → Operand → Bool}

private theorem Cat.mono {s s' : IS} {j : Nat} {o : Operand} {x : Reg} (h : Cat c g clob st s j o x)
    (hR : ∀ (k : Nat) (y : Reg), s.R[k]? = some (some y) → s'.R[k]? = some (some y))
    (ht : ∀ t ∈ s.taken, t ∈ s'.taken) (hp : ∀ m ∈ s.pre, m ∈ s'.pre)
    (hq : ∀ m ∈ s.post, m ∈ s'.post) : Cat c g clob st s' j o x where
  ok := h.ok
  fix := h.fix
  reu ui hu := hR _ _ (h.reu ui hu)
  use hu := (h.use hu).imp id (hp _)
  dfn hd hs := (h.dfn hd hs).imp id (hq _)
  clob := h.clob
  kind := h.kind.imp id fun ⟨a, b⟩ => ⟨a.mono ht, b⟩

private theorem get_set {R : Array (Option Reg)} {j k : Nat} {x : Reg} (hj : j < R.size) :
    (R.set! j (some x))[k]? = if j = k then some (some x) else R[k]? := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  split <;> simp_all

/-- **Adding operand `j`** with register `x` to the state. -/
private theorem Inv.add {s s' : IS} (hI : Inv c g os clob st s) {j : Nat} {o : Operand} {x : Reg}
    (hj : os[j]? = some o) (hn : s.R[j]? = some none)
    (hR : ∀ k : Nat, s'.R[k]? = (s.R.set! j (some x))[k]?)
    (ht : ∀ t ∈ s.taken, t ∈ s'.taken)
    (hp1 : ∀ m ∈ s.pre, m ∈ s'.pre)
    (hp2 : ∀ m ∈ s'.pre, m ∈ s.pre ∨ (o.kind = .use ∧ m = (c.loc o.vreg, .reg x)))
    (hq1 : ∀ m ∈ s.post, m ∈ s'.post)
    (hq2 : ∀ m ∈ s'.post, m ∈ s.post ∨ (o.kind = .def ∧ st j o = true ∧ m = (.reg x, c.loc o.vreg)))
    (hu : s'.useScr = s.useScr)
    (hcat : Cat c g clob st s' j o x)
    (hd : ∀ (j' : Nat) (o' : Operand), os[j']? = some o' → j' ≠ j → s.R[j']? = some (some x) →
      Ov (opRange g o false) (opRange g o' false) → Legit j o j' o')
    (hsc : ∀ (v : Nat) (r : Reg), (v, r) ∈ s.useScr → r = x → Ov (pos g 1, pos g 2) (opRange g o false) →
      o.kind = .use ∧ o.vreg = v) :
    Inv c g os clob st s' := by
  have hjs : j < s.R.size := (Array.getElem?_eq_some_iff.mp hn).1
  have hR' : ∀ k : Nat, s'.R[k]? = if j = k then some (some x) else s.R[k]? := fun k => by
    rw [hR, get_set hjs]
  have hmono : ∀ (k : Nat) (y : Reg), s.R[k]? = some (some y) → s'.R[k]? = some (some y) := by
    intro k y hk
    rw [hR']
    split
    · subst_vars; rw [hn] at hk; cases hk
    · exact hk
  have hsize : s'.R.size = os.size := by
    rw [Array.ext_getElem? hR, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hI.size]
  have hnew : ∀ (k : Nat) (y : Reg), s'.R[k]? = some (some y) → (k = j ∧ y = x) ∨ (k ≠ j ∧ s.R[k]? = some (some y)) := by
    intro k y hk
    rw [hR'] at hk
    split at hk
    · subst_vars; simp at hk; exact .inl ⟨rfl, hk.symm⟩
    · exact .inr ⟨Ne.symm ‹_›, hk⟩
  refine ⟨hsize, ?_, ?_, ?_, ?_, ?_⟩
  · intro k o' y hk hy
    rcases hnew k y hy with ⟨rfl, rfl⟩ | ⟨-, hy⟩
    · rw [hj] at hk; cases hk; exact hcat
    · exact (hI.cat k o' y hk hy).mono hmono ht hp1 hq1
  · intro k o1 k' o2 y hk hk' hne hy hy' hov
    rcases hnew k y hy with ⟨hkj, hyx⟩ | ⟨hkj, hy⟩ <;>
      rcases hnew k' y hy' with ⟨hkj', hyx'⟩ | ⟨hkj', hy'⟩
    · exact absurd (hkj.trans hkj'.symm) hne
    · subst hkj hyx; rw [hj] at hk; cases hk; exact hd k' o2 hk' hkj' hy' hov
    · subst hkj' hyx'; rw [hj] at hk'; cases hk'; exact (hd k o1 hk hkj hy hov.symm).symm
    · exact hI.disj k o1 k' o2 y hk hk' hne hy hy' hov
  · intro m hm
    rcases hp2 m hm with hm | ⟨hk, rfl⟩
    · obtain ⟨k, o', y, a, b, hy, e⟩ := hI.pre m hm
      exact ⟨k, o', y, a, b, hmono _ _ hy, e⟩
    · exact ⟨j, o, x, hj, hk, by rw [hR']; simp, rfl⟩
  · intro m hm
    rcases hq2 m hm with hm | ⟨hk, hs, rfl⟩
    · obtain ⟨k, o', y, a, b, b', hy, e⟩ := hI.post m hm
      exact ⟨k, o', y, a, b, b', hmono _ _ hy, e⟩
    · exact ⟨j, o, x, hj, hk, hs, by rw [hR']; simp, rfl⟩
  · intro v r hm
    rw [hu] at hm
    obtain ⟨k, o', a, b, e, hy, hx, htk, hcl⟩ := hI.scr v r hm
    refine ⟨k, o', a, b, e, hmono _ _ hy, hx, htk.mono ht, ?_⟩
    intro k' o2 hk' hy' hov
    rcases hnew k' r hy' with ⟨rfl, rfl⟩ | ⟨-, hy'⟩
    · rw [hj] at hk'; cases hk'; exact hsc v r hm rfl hov
    · exact hcl k' o2 hk' hy' hov

/-- Recording the scratch register `r` of the spilled use vreg `v`. -/
private theorem Inv.addScr {s : IS} (hI : Inv c g os clob st s) {v : Nat} {r : Reg}
    (h : ∃ (j : Nat) (o : Operand), os[j]? = some o ∧ o.kind = .use ∧ o.vreg = v ∧
      s.R[j]? = some (some r) ∧ Excl c.pl r (pos g 1) (pos g 2) none ∧ TK s.taken r (pos g 1, pos g 2) ∧
      ∀ (j' : Nat) (o' : Operand), os[j']? = some o' → s.R[j']? = some (some r) →
        Ov (pos g 1, pos g 2) (opRange g o' false) → o'.kind = .use ∧ o'.vreg = v) :
    Inv c g os clob st { s with useScr := (v, r) :: s.useScr } where
  size := hI.size
  cat j o x hj hx := (hI.cat j o x hj hx).mono (fun _ _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h)
  disj := hI.disj
  pre := hI.pre
  post := hI.post
  scr v' r' hm := by
    rcases List.mem_cons.mp hm with he | hm
    · cases he; exact h
    · exact hI.scr v' r' hm

/-- More `taken` entries. -/
private theorem Inv.taken {s : IS} (hI : Inv c g os clob st s) (t : List (Reg × Nat × Nat))
    (ht : ∀ y ∈ s.taken, y ∈ t) : Inv c g os clob st { s with taken := t } where
  size := hI.size
  cat j o x hj hx := (hI.cat j o x hj hx).mono (fun _ _ h => h) ht (fun _ h => h) (fun _ h => h)
  disj := hI.disj
  pre := hI.pre
  post := hI.post
  scr v r hm := by
    obtain ⟨k, o', a, b, e, hy, hx, htk, hcl⟩ := hI.scr v r hm
    exact ⟨k, o', a, b, e, hy, hx, htk.mono ht, hcl⟩

/-! ### A new register against the registers chosen so far -/

/-- A register in place (the vreg's own) meets the registers chosen so far only legitimately. -/
private theorem Inv.legitIn (E : Env vc c g os clob st) {s : IS} (hI : Inv c g os clob st s)
    {j : Nat} {o : Operand} {x : Reg} (hj : os[j]? = some o) (hx : c.pl.regOf o.vreg = some x) :
    ∀ (j' : Nat) (o' : Operand), os[j']? = some o' → j' ≠ j → s.R[j']? = some (some x) →
      Ov (opRange g o false) (opRange g o' false) → Legit j o j' o' := by
  intro j' o' hj' hne hy hov
  obtain ⟨q, h1, h2, h3, h4⟩ := ov_pt hov (iv_le g o) (iv_le g o')
  have hq := E.cov hj h1 h2
  have same : o.vreg = o'.vreg → Legit j o j' o' := fun hv =>
    have := E.sameV hj hj' (Ne.symm hne) hv (by rw [hx]; rfl) hov
    .inl ⟨this.1, this.2, hv⟩
  have hc := hI.cat j' o' x hj' hy
  rcases hc.kind with hr | ⟨-, ⟨p, hp⟩ | hex⟩
  · exact same (E.pf.inter _ _ x q hx hr hq (E.cov hj' h3 h4))
  · have hxp := hc.fix p hp; subst hxp
    have := (E.pf.claim g os E.hos o' (E.mem hj') x hp).2 o.vreg hx q (by rw [iv_true.1]; exact h3)
      (Nat.le_trans h4 iv_true.2) hq
    exact same this
  · exact absurd (hex o.vreg hx q h3 h4 hq) (by simp)

/-- A register `regFree` reports over a superset of the interval meets no register chosen so far. -/
private theorem Inv.fresh (E : Env vc c g os clob st) {s : IS} (hI : Inv c g os clob st s)
    {o : Operand} {x : Reg} {a b : Nat} (hf : regFree c.occ s.taken x a b = true)
    (ha : a ≤ (opRange g o false).1) (hb : (opRange g o false).2 ≤ b) :
    ∀ (j' : Nat) (o' : Operand), os[j']? = some o' → s.R[j']? = some (some x) →
      Ov (opRange g o false) (opRange g o' false) → False := by
  intro j' o' hj' hy hov
  obtain ⟨hex, -, hfree⟩ := regFree_sound E.pf E.occ hf
  obtain ⟨q, h1, h2, h3, h4⟩ := ov_pt hov (iv_le g o) (iv_le g o')
  rcases (hI.cat j' o' x hj' hy).kind with hr | ⟨⟨t, ht, rfl, t1, t2⟩, -⟩
  · exact absurd (hex o'.vreg hr q (by omega) (by omega) (E.cov hj' h3 h4)) (by simp)
  · have := hfree t ht rfl
    simp only [Ov] at hov
    omega

/-- A register reserved (`Excl` and taken) over `I` is not a vreg's own over a meeting interval. -/
private theorem noIn (E : Env vc c g os clob st) {j : Nat} {o : Operand} {x : Reg}
    {I : Nat × Nat} (hex : Excl c.pl x I.1 I.2 none) (hj : os[j]? = some o)
    (hx : c.pl.regOf o.vreg = some x) (hov : Ov I (opRange g o false)) (hI1 : I.1 ≤ I.2) : False := by
  obtain ⟨q, h1, h2, h3, h4⟩ := ov_pt hov hI1 (iv_le g o)
  exact absurd (hex o.vreg hx q h1 h2 (E.cov hj h3 h4)) (by simp)

/-- A register taken over `I` is not `regFree` over a superset of a meeting interval. -/
private theorem noFree (E : Env vc c g os clob st) {taken : List (Reg × Nat × Nat)} {x : Reg}
    {I J : Nat × Nat} {a b : Nat} (htk : TK taken x I) (hf : regFree c.occ taken x a b = true)
    (ha : a ≤ J.1) (hb : J.2 ≤ b) (hov : Ov I J) : False := by
  obtain ⟨-, -, hfree⟩ := regFree_sound E.pf E.occ hf
  obtain ⟨t, ht, rfl, t1, t2⟩ := htk
  have := hfree t ht rfl
  simp only [Ov] at hov
  omega

/-- A register `regFree` reports over a range containing position 3 is no clobber (they are taken
at 3). -/
private theorem notClob (E : Env vc c g os clob st) {taken : List (Reg × Nat × Nat)} {x : Reg} {a b : Nat}
    (hcl : ∀ r ∈ clob, (r, pos g 3, pos g 3) ∈ taken) (hf : regFree c.occ taken x a b = true)
    (ha : a ≤ pos g 3) (hb : pos g 3 ≤ b) : x ∉ clob := fun hm =>
  noFree E ⟨_, hcl x hm, rfl, Nat.le_refl _, Nat.le_refl _⟩ hf (J := (pos g 3, pos g 3)) ha hb
    ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- A def's own register is no clobber. -/
private theorem Env.inClob (E : Env vc c g os clob st) {j : Nat} {o : Operand} {x : Reg}
    (hj : os[j]? = some o) (hd : o.kind = .def) (hx : c.pl.regOf o.vreg = some x) : x ∉ clob := by
  intro hm
  have := E.clob x hm o.vreg hx
  rw [E.cov hj (iv_def3 hd).1 (iv_def3 hd).2] at this
  cases this

end

/-! ## The passes -/

section
variable {vc : VCode} {c : LinearScan.Ctx} {g : Nat} {os : Array Operand} {clob : List Reg}
  {st : Nat → Operand → Bool}

private theorem none_of_lt {s : IS} (hI : Inv c g os clob st s) {j : Nat} {o : Operand}
    (hj : os[j]? = some o) (h : ∀ y, s.R[j]? ≠ some (some y)) : s.R[j]? = some none := by
  have hjs : j < s.R.size := by rw [hI.size]; exact (Array.getElem?_eq_some_iff.mp hj).1
  rcases hr : s.R[j]? with _ | (_ | y)
  · rw [Array.getElem?_eq_getElem hjs] at hr; cases hr
  · rfl
  · exact absurd hr (h y)

/-- One fixed operand. -/
private theorem fixed_step (E : Env vc c g os clob st) {s : IS} (hI : Inv c g os clob st s)
    (hus : s.useScr = [])
    (hfx : ∀ (k : Nat) (y : Reg), s.R[k]? = some (some y) → ∃ o p, os[k]? = some o ∧ o.con = .fixed p)
    {j : Nat} {o : Operand} {p : Reg} (hj : os[j]? = some o) (hp : o.con = .fixed p)
    (hn : s.R[j]? = some none) (s2 : IS)
    (hR : s2.R = s.R.set! j (some p))
    (ht : s2.taken = (p, (opRange g o true).1, (opRange g o true).2) :: s.taken)
    (hu : s2.useScr = s.useScr)
    (hpre : s2.pre = if o.kind = .use ∧ c.loc o.vreg ≠ .reg p then (c.loc o.vreg, .reg p) :: s.pre
      else s.pre)
    (hpost : s2.post = if o.kind = .def ∧ st j o = true ∧ c.loc o.vreg ≠ .reg p then
      (.reg p, c.loc o.vreg) :: s.post else s.post) :
    Inv c g os clob st s2 := by
  have hmem := E.mem hj
  refine hI.add hj hn (fun k => by rw [hR]) (fun t h => by rw [ht]; exact List.mem_cons_of_mem _ h)
    (fun m h => by rw [hpre]; split; (first | exact List.mem_cons_of_mem _ h | exact h); exact h) (fun m h => ?_)
    (fun m h => by rw [hpost]; split; (first | exact List.mem_cons_of_mem _ h | exact h); exact h) (fun m h => ?_) hu ?_ ?_
    (fun v r h => by rw [hus] at h; cases h)
  · rw [hpre] at h
    split at h
    · rename_i hc
      rcases List.mem_cons.mp h with rfl | h
      · exact .inr ⟨hc.1, rfl⟩
      · exact .inl h
    · exact .inl h
  · rw [hpost] at h
    split at h
    · rename_i hc
      rcases List.mem_cons.mp h with rfl | h
      · exact .inr ⟨hc.1, hc.2.1, rfl⟩
      · exact .inl h
    · exact .inl h
  · refine ⟨E.ok.fixedReg o hmem p hp, fun p' h => (by rw [hp] at h; cases h; rfl),
      fun ui h => (by rw [hp] at h; cases h), fun hk => ?_, fun hk hs => ?_,
      fun hk => E.ok.fixedDefClob o hmem p hk hp, .inr ⟨⟨_, by rw [ht]; exact List.mem_cons_self,
        rfl, Nat.le_of_eq iv_true.1, iv_true.2⟩, .inl ⟨p, hp⟩⟩⟩
    · by_cases hl : c.loc o.vreg = .reg p
      · exact .inl hl
      · exact .inr (by rw [hpre, ite_eq_left ⟨hk, hl⟩]; exact List.mem_cons_self)
    · by_cases hl : c.loc o.vreg = .reg p
      · exact .inl hl
      · exact .inr (by rw [hpost, ite_eq_left ⟨hk, hs, hl⟩]; exact List.mem_cons_self)
  · intro j' o' hj' hne hy hov
    obtain ⟨o'', p', hj'', hp'⟩ := hfx j' p hy
    rw [hj'] at hj''; cases hj''
    have := (hI.cat j' o' p hj' hy).fix p' hp'
    subst this
    exact E.fixFix hj hj' (Ne.symm hne) hp hp' hov

/-- **The fixed pass**. -/
private theorem fixed_pass (E : Env vc c g os clob st) :
    ∀ (L : List (Operand × Nat)) (s s' : IS), (∀ x ∈ L, os[x.2]? = some x.1) → (L.map (·.2)).Nodup →
    Inv c g os clob st s → s.useScr = [] →
    (∀ (k : Nat) (y : Reg), s.R[k]? = some (some y) →
      (∃ o p, os[k]? = some o ∧ o.con = .fixed p) ∧ k ∉ L.map (·.2)) →
    c.fixedPass g st L s = .ok s' →
    Inv c g os clob st s' ∧ s'.useScr = [] ∧
    (∀ (k : Nat) (y : Reg), s'.R[k]? = some (some y) → ∃ o p, os[k]? = some o ∧ o.con = .fixed p) ∧
    (∀ x ∈ L, ∀ p, x.1.con = .fixed p → ∃ y, s'.R[x.2]? = some (some y)) ∧
    (∀ (k : Nat) (y : Reg), s.R[k]? = some (some y) → s'.R[k]? = some (some y))
  | [], s, s', _, _, hI, hu, hfx, h => by
    simp only [Ctx.fixedPass, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hI, hu, fun k y hy => (hfx k y hy).1, by simp, fun _ _ h => h⟩
  | (o, j) :: rest, s, s', hL, hnd, hI, hu, hfx, h => by
    have hj : os[j]? = some o := hL (o, j) List.mem_cons_self
    have hL' : ∀ x ∈ rest, os[x.2]? = some x.1 := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    rw [List.map_cons, List.nodup_cons] at hnd
    have hn : s.R[j]? = some none :=
      none_of_lt hI hj fun y hy => (hfx j y hy).2 List.mem_cons_self
    simp only [Ctx.fixedPass] at h
    split at h
    · rename_i p hp
      obtain ⟨s2, hs2, hR2, ht2, hu2, hpre2, hpost2⟩ : ∃ s2 : IS, c.fixedPass g st rest s2 = .ok s' ∧
          s2.R = s.R.set! j (some p) ∧
          s2.taken = (p, (opRange g o true).1, (opRange g o true).2) :: s.taken ∧
          s2.useScr = s.useScr ∧
          s2.pre = (if o.kind = .use ∧ c.loc o.vreg ≠ .reg p then (c.loc o.vreg, .reg p) :: s.pre
            else s.pre) ∧
          s2.post = (if o.kind = .def ∧ st j o = true ∧ c.loc o.vreg ≠ .reg p then
            (.reg p, c.loc o.vreg) :: s.post else s.post) :=
        ⟨_, h, by split <;> (try split) <;> rfl, by split <;> (try split) <;> rfl,
          by split <;> (try split) <;> rfl,
          by cases o.kind <;> by_cases hl : c.loc o.vreg = .reg p <;> simp [hl] <;> split <;> rfl,
          by cases o.kind <;> by_cases hl : c.loc o.vreg = .reg p <;> simp [hl] <;> split <;> rfl⟩
      have hI2 := fixed_step E hI hu (fun k y hy => (hfx k y hy).1) hj hp hn s2 hR2 ht2 hu2 hpre2 hpost2
      have hjs : j < s.R.size := (Array.getElem?_eq_some_iff.mp hn).1
      obtain ⟨h1, h2, h3, h4, h5⟩ := fixed_pass E rest s2 s' hL' hnd.2 hI2 (hu2.trans hu)
        (fun k y hy => by
          rw [hR2, get_set hjs] at hy
          split at hy
          · subst_vars; exact ⟨⟨o, p, hj, hp⟩, hnd.1⟩
          · exact ⟨(hfx k y hy).1, fun hm => (hfx k y hy).2 (List.mem_cons_of_mem _ hm)⟩) hs2
      refine ⟨h1, h2, h3, fun x hx p' hp' => ?_, fun k y hy => h5 k y ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨p, h5 j p (by rw [hR2, get_set hjs]; simp)⟩
        · exact h4 x hx p' hp'
      · rw [hR2, get_set hjs, ite_eq_right]; exact hy
        rintro rfl; rw [hn] at hy; cases hy
    · cases h
    · rename_i hnf _
      obtain ⟨h1, h2, h3, h4, h5⟩ := fixed_pass E rest s s' hL' hnd.2 hI hu
        (fun k y hy => ⟨(hfx k y hy).1, fun hm => (hfx k y hy).2 (List.mem_cons_of_mem _ hm)⟩) h
      refine ⟨h1, h2, h3, fun x hx p hp => ?_, h5⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact absurd hp (hnf p)
      · exact h4 x hx p hp

end


section
variable {vc : VCode} {c : LinearScan.Ctx} {g : Nat} {os : Array Operand} {clob : List Reg}
  {st : Nat → Operand → Bool}

private theorem scratch_spec {occ : Array (Array LinearScan.Seg)} {taken : List (Reg × Nat × Nat)} {cl : RegClass}
    {s e : Nat} {x : Reg} (h : scratchReg occ taken cl s e [] = some x) :
    regFree occ taken x s e = true ∧ x ∈ scratchOrder cl := by
  unfold scratchReg at h
  have := List.find?_some h
  simp only [List.contains_nil, Bool.not_false, Bool.true_and] at this
  exact ⟨this, List.mem_of_find?_eq_some h⟩

private theorem reuseReg_cases {c : LinearScan.Ctx} {g : Nat} {taken : List (Reg × Nat × Nat)}
    {cl : RegClass} {lrd lrn : Loc} {x : Reg} {a b : Bool}
    (h : c.reuseReg g taken cl lrd lrn = .ok (x, a, b)) :
    (locReg? lrd = some x ∧ locReg? lrn = some x ∧ a = false ∧ b = false) ∨
    (locReg? lrd = some x ∧ regFree c.occ taken x (pos g 1) (pos g 2) = true ∧ a = true ∧ b = false) ∨
    (locReg? lrn = some x ∧ regFree c.occ taken x (pos g 3) (pos g 4) = true ∧ a = false ∧ b = true) ∨
    (regFree c.occ taken x (pos g 1) (pos g 4) = true ∧ x ∈ scratchOrder cl ∧ a = true ∧ b = true) := by
  have ok3 : ∀ {r : Reg} {a' b' : Bool}, (pure (r, a', b') : Except String (Reg × Bool × Bool)) =
      .ok (x, a, b) → r = x ∧ a' = a ∧ b' = b := by
    intro r a' b' h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h; exact h
  have scr : ∀ {o : Option Reg}, o = scratchReg c.occ taken cl (pos g 1) (pos g 4) [] →
      (match o with | some x => pure (x, true, true) | none => throw "no scratch register" :
        Except String (Reg × Bool × Bool)) = .ok (x, a, b) →
      regFree c.occ taken x (pos g 1) (pos g 4) = true ∧ x ∈ scratchOrder cl ∧ a = true ∧ b = true := by
    intro o ho h
    cases o with
    | none => cases h
    | some x' =>
      obtain ⟨rfl, rfl, rfl⟩ := ok3 h
      exact ⟨(scratch_spec ho.symm).1, (scratch_spec ho.symm).2, rfl, rfl⟩
  unfold Ctx.reuseReg at h
  split at h
  · rename_i r r' hd hn
    split at h
    · rename_i he
      obtain ⟨rfl, rfl, rfl⟩ := ok3 h
      have : r = r' := by simpa using he
      subst this
      exact .inl ⟨hd, hn, rfl, rfl⟩
    · split at h
      · obtain ⟨rfl, rfl, rfl⟩ := ok3 h; exact .inr (.inl ⟨hd, ‹_›, rfl, rfl⟩)
      · split at h
        · obtain ⟨rfl, rfl, rfl⟩ := ok3 h; exact .inr (.inr (.inl ⟨hn, ‹_›, rfl, rfl⟩))
        · exact .inr (.inr (.inr (scr rfl h)))
  · rename_i r hd hn
    split at h
    · obtain ⟨rfl, rfl, rfl⟩ := ok3 h; exact .inr (.inl ⟨hd, ‹_›, rfl, rfl⟩)
    · exact .inr (.inr (.inr (scr rfl h)))
  · rename_i r' hd hn
    split at h
    · obtain ⟨rfl, rfl, rfl⟩ := ok3 h; exact .inr (.inr (.inl ⟨hn, ‹_›, rfl, rfl⟩))
    · exact .inr (.inr (.inr (scr rfl h)))
  · exact .inr (.inr (.inr (scr rfl h)))

end


section
variable {vc : VCode} {c : LinearScan.Ctx} {g : Nat} {os : Array Operand} {clob : List Reg}
  {st : Nat → Operand → Bool}

private theorem mem_ite1 {α : Type} {p : Prop} [Decidable p] {y m : α} {l : List α} (h : m ∈ l) :
    m ∈ (if p then y :: l else l) := by
  split
  · exact List.mem_cons_of_mem _ h
  · exact h

private theorem mem_ite2 {α : Type} {p : Prop} [Decidable p] {y m : α} {l : List α}
    (h : m ∈ (if p then y :: l else l)) : m ∈ l ∨ (p ∧ m = y) := by
  split at h
  · rcases List.mem_cons.mp h with rfl | h
    · exact .inr ⟨‹_›, rfl⟩
    · exact .inl h
  · exact .inl h

private theorem mem_ite3 {α : Type} {p : Prop} [Decidable p] {y : α} {l : List α} (hp : p) :
    y ∈ (if p then y :: l else l) := by
  rw [ite_eq_left hp]; exact List.mem_cons_self

/-- A vreg's own register is allocatable and of the operand's class. -/
private theorem Env.regCls (E : Env vc c g os clob st) {j : Nat} {o : Operand} {x : Reg}
    (hj : os[j]? = some o) (hx : c.pl.regOf o.vreg = some x) :
    x.allocatable = true ∧ x.realClass? = some o.cls := by
  have := pool_ok (E.pf.regs o.vreg x hx)
  rw [E.cls o (E.mem hj)] at this
  exact ⟨this.1, this.2.1⟩

private theorem not_fixed {o : Operand} (h : scratch o.con = true) (p : Reg) : o.con ≠ .fixed p := by
  intro he; rw [he] at h; cases h

private theorem not_reuse {o : Operand} (h : scratch o.con = true) (i : Nat) : o.con ≠ .reuse i := by
  intro he; rw [he] at h; cases h

/-- One reuse def `j` (`o`) and the use `ui` (`u`) it reuses. -/
private theorem reuse_step (E : Env vc c g os clob st) {s s' : IS} (hI : Inv c g os clob st s)
    (hus : s.useScr = []) (hcl : ∀ r ∈ clob, (r, pos g 3, pos g 3) ∈ s.taken)
    {j ui : Nat} {o u : Operand} {x : Reg} {a b : Bool}
    (hj : os[j]? = some o) (hr : o.con = .reuse ui) (hu : os[ui]? = some u)
    (hn : s.R[j]? = some none) (hnu : s.R[ui]? = some none)
    (hrr : c.reuseReg g s.taken o.cls (c.loc o.vreg) (c.loc u.vreg) = .ok (x, a, b))
    (hR : s'.R = (s.R.set! j (some x)).set! ui (some x))
    (ht : s'.taken = (x, pos g 1, pos g 4) :: s.taken)
    (hpre : s'.pre = if a = true then (c.loc u.vreg, .reg x) :: s.pre else s.pre)
    (hpost : s'.post = if (b && st j o) = true then (.reg x, c.loc o.vreg) :: s.post else s.post)
    (hsc : s'.useScr = s.useScr) : Inv c g os clob st s' := by
  obtain ⟨hdef, hlate, oi, hoi, huse, hscr, hcls, -⟩ := E.ok.reuse j o ui (tl hj) hr
  rw [Array.getElem?_toList, hu] at hoi; cases hoi
  have hne : j ≠ ui := by
    rintro rfl; rw [hj] at hu; cases hu; rw [hdef] at huse; cases huse
  have ivU := E.ivU hu huse
  have ivJ : opRange g o false = (pos g 3, pos g 3) := by rw [iv_def hdef]; simp [opSlot, hlate]
  obtain ⟨hU, hJ, hok⟩ : (c.pl.regOf u.vreg = some x ∧ a = false ∨
      ∃ e, pos g 2 ≤ e ∧ regFree c.occ s.taken x (pos g 1) e = true ∧ a = true) ∧
      (c.pl.regOf o.vreg = some x ∧ b = false ∨
        ∃ a', a' ≤ pos g 3 ∧ regFree c.occ s.taken x a' (pos g 4) = true ∧ b = true) ∧
      (x.allocatable = true ∧ x.realClass? = some o.cls) := by
    rcases reuseReg_cases hrr with ⟨h1, h2, rfl, rfl⟩ | ⟨h1, h2, rfl, rfl⟩ | ⟨h1, h2, rfl, rfl⟩ |
      ⟨h1, h2, rfl, rfl⟩
    · exact ⟨.inl ⟨locReg_loc.mp h2, rfl⟩, .inl ⟨locReg_loc.mp h1, rfl⟩, E.regCls hj (locReg_loc.mp h1)⟩
    · exact ⟨.inr ⟨_, Nat.le_refl _, h2, rfl⟩, .inl ⟨locReg_loc.mp h1, rfl⟩,
        E.regCls hj (locReg_loc.mp h1)⟩
    · exact ⟨.inl ⟨locReg_loc.mp h1, rfl⟩, .inr ⟨_, Nat.le_refl _, h2, rfl⟩,
        hcls ▸ E.regCls hu (locReg_loc.mp h1)⟩
    · have := scratchOrder_ok h2
      exact ⟨.inr ⟨_, by simp [pos], h1, rfl⟩, .inr ⟨_, by simp [pos], h1, rfl⟩, this.1, this.2.1⟩
  -- the use first
  obtain ⟨s1, h1R, h1t, h1p, h1q, h1u⟩ : ∃ s1 : IS, s1.R = s.R.set! ui (some x) ∧
      s1.taken = (x, pos g 1, pos g 4) :: s.taken ∧ s1.pre = s'.pre ∧ s1.post = s.post ∧
      s1.useScr = s.useScr := ⟨⟨_, _, _, _, _⟩, rfl, rfl, rfl, rfl, rfl⟩
  have hI1 : Inv c g os clob st s1 := by
    refine hI.add hu hnu (fun k => by rw [h1R]) (fun t h => by rw [h1t]; exact List.mem_cons_of_mem _ h)
      (fun m h => by rw [h1p, hpre]; exact mem_ite1 h)
      (fun m h => by
        rw [h1p, hpre] at h
        exact (mem_ite2 h).imp id fun ⟨_, e⟩ => ⟨huse, e⟩)
      (fun m h => by rw [h1q]; exact h) (fun m h => by rw [h1q] at h; exact .inl h) h1u ?_ ?_
      (fun v r h => by rw [hus] at h; cases h)
    · refine ⟨⟨hok.1, hcls ▸ hok.2⟩, fun p h => absurd h (not_fixed hscr p),
        fun i h => absurd h (not_reuse hscr i), fun _ => ?_, fun hd => (by rw [huse] at hd; cases hd),
        fun hd => (by rw [huse] at hd; cases hd), ?_⟩
      · rcases hU with ⟨h, -⟩ | ⟨e, -, -, ha⟩
        · exact .inl (loc_reg.mpr h)
        · exact .inr (by rw [h1p, hpre]; exact mem_ite3 ha)
      · rcases hU with ⟨h, -⟩ | ⟨e, he, hf, -⟩
        · exact .inl h
        · refine .inr ⟨⟨_, by rw [h1t]; exact List.mem_cons_self, rfl, by rw [ivU]; exact Nat.le_refl _,
            by rw [ivU]; simp [pos]⟩, .inr ?_⟩
          rw [ivU]; exact (regFree_sound E.pf E.occ hf).1.mono (Nat.le_refl _) he
    · intro j' o' hj' hne' hy hov
      rcases hU with ⟨h, -⟩ | ⟨e, he, hf, -⟩
      · exact hI.legitIn E hu h j' o' hj' hne' hy hov
      · exact (hI.fresh E hf (by rw [ivU]; exact Nat.le_refl _) (by rw [ivU]; exact he) j' o' hj' hy hov).elim
  have hjs : j < s.R.size := (Array.getElem?_eq_some_iff.mp hn).1
  have hus' : ui < s.R.size := (Array.getElem?_eq_some_iff.mp hnu).1
  have hn1 : s1.R[j]? = some none := by rw [h1R, get_set hus', ite_eq_right (Ne.symm hne)]; exact hn
  refine hI1.add hj hn1
    (fun k => by
      rw [hR, h1R, Array.set!_eq_setIfInBounds, Array.set!_eq_setIfInBounds, Array.set!_eq_setIfInBounds,
        Array.set!_eq_setIfInBounds, Array.setIfInBounds_comm _ _ hne])
    (fun t h => by rw [ht, ← h1t]; exact h) (fun m h => by rw [← h1p]; exact h)
    (fun m h => by rw [← h1p] at h; exact .inl h)
    (fun m h => by rw [hpost, ← h1q]; exact mem_ite1 h)
    (fun m h => by
      rw [hpost, ← h1q] at h
      exact (mem_ite2 h).imp id fun ⟨hb, e⟩ => ⟨hdef, by simp at hb; exact hb.2, e⟩)
    (hsc.trans h1u.symm) ?_ ?_ (fun v r h => by rw [h1u, hus] at h; cases h)
  · refine ⟨hok, fun p h => (by rw [hr] at h; cases h), fun i h => ?_,
      fun hk => (by rw [hdef] at hk; cases hk), fun _ hs => ?_, fun _ => ?_, ?_⟩
    · rw [hr] at h; cases h
      rw [hR, get_set (by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hus'), ite_eq_left rfl]
    · rcases hJ with ⟨h, -⟩ | ⟨a', -, -, hb⟩
      · exact .inl (loc_reg.mpr h)
      · exact .inr (by rw [hpost]; exact mem_ite3 (by simp [hb, hs]))
    · rcases hJ with ⟨h, -⟩ | ⟨a', ha', hf, -⟩
      · exact E.inClob hj hdef h
      · exact notClob E hcl hf ha' (by simp [pos])
    · rcases hJ with ⟨h, -⟩ | ⟨a', ha', hf, -⟩
      · exact .inl h
      · refine .inr ⟨⟨_, by rw [ht]; exact List.mem_cons_self, rfl, by rw [ivJ]; simp [pos],
          by rw [ivJ]; simp [pos]⟩, .inr ?_⟩
        rw [ivJ]; exact (regFree_sound E.pf E.occ hf).1.mono ha' (by simp [pos])
  · intro j' o' hj' hne' hy hov
    by_cases hju : j' = ui
    · subst hju; exact .inr (.inl hr)
    · rw [h1R, get_set hus', ite_eq_right (Ne.symm hju)] at hy
      rcases hJ with ⟨h, -⟩ | ⟨a', ha', hf, -⟩
      · exact hI.legitIn E hj h j' o' hj' hne' hy hov
      · exact (hI.fresh E hf (by rw [ivJ]; exact ha') (by rw [ivJ]; simp [pos]) j' o' hj' hy hov).elim

end


section
variable {vc : VCode} {c : LinearScan.Ctx} {g : Nat} {os : Array Operand} {clob : List Reg}
  {st : Nat → Operand → Bool}

/-- **The reuse pass**. -/
private theorem reuse_pass (E : Env vc c g os clob st) :
    ∀ (L : List (Operand × Nat)) (s s' : IS), (∀ x ∈ L, os[x.2]? = some x.1) → (L.map (·.2)).Nodup →
    Inv c g os clob st s → s.useScr = [] → (∀ r ∈ clob, (r, pos g 3, pos g 3) ∈ s.taken) →
    (∀ (k : Nat) (y : Reg), s.R[k]? = some (some y) → (∃ o p, os[k]? = some o ∧ o.con = .fixed p) ∨
      ∃ j' o' ui, os[j']? = some o' ∧ o'.con = .reuse ui ∧ j' ∉ L.map (·.2) ∧ (k = j' ∨ k = ui)) →
    c.reusePass g st os L s = .ok s' →
    Inv c g os clob st s' ∧ s'.useScr = [] ∧ (∀ r ∈ clob, (r, pos g 3, pos g 3) ∈ s'.taken) ∧
    (∀ x ∈ L, ∀ ui, x.1.con = .reuse ui → ∃ y, s'.R[x.2]? = some (some y)) ∧
    (∀ (k : Nat) (y : Reg), s.R[k]? = some (some y) → s'.R[k]? = some (some y))
  | [], s, s', _, _, hI, hu, hcl, _, h => by
    simp only [Ctx.reusePass, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hI, hu, hcl, by simp, fun _ _ h => h⟩
  | (o, j) :: rest, s, s', hL, hnd, hI, hu, hcl, hfx, h => by
    have hj : os[j]? = some o := hL (o, j) List.mem_cons_self
    have hL' : ∀ x ∈ rest, os[x.2]? = some x.1 := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [Ctx.reusePass] at h
    split at h
    · rename_i ui hr
      obtain ⟨hdef, -, u, hu', huse, hscr, -, huniq⟩ := E.ok.reuse j o ui (tl hj) hr
      rw [Array.getElem?_toList] at hu'
      rw [hu'] at h
      dsimp only at h
      cases hrr : c.reuseReg g s.taken o.cls (c.loc o.vreg) (c.loc u.vreg) with
      | error e => rw [hrr] at h; dsimp only [bind, Except.bind] at h; cases h
      | ok xab =>
        obtain ⟨x, a, b⟩ := xab
        rw [hrr] at h
        dsimp only [bind, Except.bind] at h
        obtain ⟨s2, hs2, hR2, ht2, hp2, hq2, hu2⟩ : ∃ s2 : IS, c.reusePass g st os rest s2 = .ok s' ∧
            s2.R = (s.R.set! j (some x)).set! ui (some x) ∧ s2.taken = (x, pos g 1, pos g 4) :: s.taken ∧
            s2.pre = (if a = true then (c.loc u.vreg, .reg x) :: s.pre else s.pre) ∧
            s2.post = (if (b && st j o) = true then (.reg x, c.loc o.vreg) :: s.post else s.post) ∧
            s2.useScr = s.useScr := ⟨_, h, rfl, rfl, rfl, rfl, rfl⟩
        have hn : s.R[j]? = some none := by
          refine none_of_lt hI hj fun y hy => ?_
          rcases hfx j y hy with ⟨o', p, hj', hp⟩ | ⟨j', o', ui', hj', hr', hnm, hk | hk⟩
          · rw [hj] at hj'; cases hj'; rw [hr] at hp; cases hp
          · subst hk; exact hnm List.mem_cons_self
          · subst hk
            obtain ⟨-, -, oi, hoi, hui, -⟩ := E.ok.reuse j' o' j (tl hj') hr'
            rw [Array.getElem?_toList, hj] at hoi; cases hoi; rw [hdef] at hui; cases hui
        have hnu : s.R[ui]? = some none := by
          refine none_of_lt hI hu' fun y hy => ?_
          rcases hfx ui y hy with ⟨o', p, hj', hp⟩ | ⟨j', o', ui', hj', hr', hnm, hk | hk⟩
          · rw [hu'] at hj'; cases hj'; exact not_fixed hscr p hp
          · subst hk; rw [hu'] at hj'; cases hj'; exact not_reuse hscr ui' hr'
          · subst hk
            obtain ⟨-, -, -, -, -, -, -, hu2⟩ := E.ok.reuse j' o' ui (tl hj') hr'
            have := hu2 j o (tl hj) hr; subst this; exact hnm List.mem_cons_self
        have hI2 := reuse_step E hI hu hcl hj hr hu' hn hnu hrr hR2 ht2 hp2 hq2 hu2
        have hjs : j < s.R.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hus : ui < (s.R.set! j (some x)).size := by
          rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
          exact (Array.getElem?_eq_some_iff.mp hnu).1
        have hget : ∀ k, s2.R[k]? = if ui = k then some (some x) else if j = k then some (some x)
            else s.R[k]? := fun k => by rw [hR2, get_set hus, get_set hjs]
        obtain ⟨h1, h2, h3, h4, h5⟩ := reuse_pass E rest s2 s' hL' hnd.2 hI2 (hu2.trans hu)
          (fun r hr => by rw [ht2]; exact List.mem_cons_of_mem _ (hcl r hr))
          (fun k y hy => by
            rw [hget] at hy
            split at hy
            · subst_vars; exact .inr ⟨j, o, k, hj, hr, hnd.1, .inr rfl⟩
            · split at hy
              · subst_vars; exact .inr ⟨k, o, ui, hj, hr, hnd.1, .inl rfl⟩
              · exact (hfx k y hy).imp id fun ⟨j', o', ui', a, b, c', d⟩ =>
                  ⟨j', o', ui', a, b, fun hm => c' (List.mem_cons_of_mem _ hm), d⟩) hs2
        refine ⟨h1, h2, h3, fun x' hx ui' hr' => ?_, fun k y hy => h5 k y ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨x, h5 j x (by rw [hget]; split <;> simp)⟩
          · exact h4 x' hx ui' hr'
        · rw [hget, ite_eq_right, ite_eq_right]
          · exact hy
          · rintro rfl; rw [hn] at hy; cases hy
          · rintro rfl; rw [hnu] at hy; cases hy
    · rename_i hnr
      obtain ⟨h1, h2, h3, h4, h5⟩ := reuse_pass E rest s s' hL' hnd.2 hI hu hcl
        (fun k y hy => (hfx k y hy).imp id fun ⟨j', o', ui, a, b, c', d⟩ =>
          ⟨j', o', ui, a, b, fun hm => c' (List.mem_cons_of_mem _ hm), d⟩) h
      refine ⟨h1, h2, h3, fun x hx ui hr => ?_, h5⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact absurd hr (hnr ui)
      · exact h4 x hx ui hr

end


section
variable {vc : VCode} {c : LinearScan.Ctx} {g : Nat} {os : Array Operand} {clob : List Reg}
  {st : Nat → Operand → Bool}

private theorem lookup_mem {l : List (Nat × Reg)} {v : Nat} {r : Reg} (h : l.lookup v = some r) :
    (v, r) ∈ l := by
  induction l with
  | nil => simp at h
  | cons kb l ih =>
    obtain ⟨k, b⟩ := kb
    simp only [List.lookup] at h
    split at h
    · rename_i he; cases h; simp at he; subst he; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

private theorem getD_none {s : IS} (hI : Inv c g os clob st s) {j : Nat} {o : Operand}
    (hj : os[j]? = some o) (h : (s.R.getD j none).isSome = false) : s.R[j]? = some none := by
  refine none_of_lt hI hj fun y hy => ?_
  rw [Array.getD_eq_getD_getElem?, hy] at h; cases h

/-- An operand not set by the fixed and reuse passes has a scratch constraint. -/
private theorem scratch_of (E : Env vc c g os clob st) {s : IS} {j : Nat} {o : Operand}
    (hj : os[j]? = some o) (hn : s.R[j]? = some none)
    (hset : ∀ (k : Nat) (o : Operand), os[k]? = some o → ((∃ p, o.con = .fixed p) ∨ ∃ i, o.con = .reuse i) →
      ∃ y, s.R[k]? = some (some y)) : scratch o.con = true := by
  rcases hc : o.con with _ | _ | _ | p | i
  · rfl
  · rfl
  · exact absurd hc (E.ok.noStack o (E.mem hj))
  · obtain ⟨y, hy⟩ := hset j o hj (.inl ⟨p, hc⟩); rw [hn] at hy; cases hy
  · obtain ⟨y, hy⟩ := hset j o hj (.inr ⟨i, hc⟩); rw [hn] at hy; cases hy

/-- A use in place. -/
private theorem use_in (E : Env vc c g os clob st) {s : IS} (hI : Inv c g os clob st s)
    {j : Nat} {o : Operand} {r : Reg} (hj : os[j]? = some o) (hn : s.R[j]? = some none)
    (hu : o.kind = .use) (hs : scratch o.con = true) (hr : c.pl.regOf o.vreg = some r) :
    Inv c g os clob st { s with R := s.R.set! j (some r) } :=
  hI.add hj hn (fun _ => rfl) (fun _ h => h) (fun _ h => h) (fun _ h => .inl h) (fun _ h => h)
    (fun _ h => .inl h) rfl
    ⟨E.regCls hj hr, fun p h => absurd h (not_fixed hs p), fun i h => absurd h (not_reuse hs i),
      fun _ => .inl (loc_reg.mpr hr), fun hd => (by rw [hu] at hd; cases hd),
      fun hd => (by rw [hu] at hd; cases hd), .inl hr⟩
    (hI.legitIn E hj hr)
    (fun v r' hm hrr hov => by
      obtain ⟨-, -, -, -, -, -, hex, -, -⟩ := hI.scr v r' hm
      subst hrr
      exact (noIn E hex hj hr hov (by simp [pos])).elim)

/-- A use of a spilled vreg already loaded into a scratch register. -/
private theorem use_lookup (E : Env vc c g os clob st) {s : IS} (hI : Inv c g os clob st s)
    {j : Nat} {o : Operand} {r : Reg} (hj : os[j]? = some o) (hn : s.R[j]? = some none)
    (hu : o.kind = .use) (hs : scratch o.con = true) (hm : (o.vreg, r) ∈ s.useScr) :
    Inv c g os clob st { s with R := s.R.set! j (some r) } := by
  obtain ⟨j0, o0, hj0, hu0, hv0, hy0, hex, htk, hcl⟩ := hI.scr _ _ hm
  have hc0 := hI.cat j0 o0 r hj0 hy0
  have ivU := E.ivU hj hu
  refine hI.add hj hn (fun _ => rfl) (fun _ h => h) (fun _ h => h) (fun _ h => .inl h) (fun _ h => h)
    (fun _ h => .inl h) rfl
    ⟨⟨hc0.ok.1, ?_⟩, fun p h => absurd h (not_fixed hs p), fun i h => absurd h (not_reuse hs i),
      fun _ => hv0 ▸ hc0.use hu0, fun hd => (by rw [hu] at hd; cases hd),
      fun hd => (by rw [hu] at hd; cases hd), .inr ⟨by rw [ivU]; exact htk, .inr (by rw [ivU]; exact hex)⟩⟩
    ?_ ?_
  · rw [hc0.ok.2, ← E.cls o0 (E.mem hj0), ← E.cls o (E.mem hj), hv0]
  · intro j' o' hj' _ hy hov
    obtain ⟨h1, h2⟩ := hcl j' o' hj' hy (by rw [← ivU]; exact hov)
    exact .inl ⟨hu, h1, h2.symm⟩
  · intro v r' hm' hrr hov
    subst hrr
    obtain ⟨j1, o1, hj1, hu1, hv1, hy1, -, -, -⟩ := hI.scr v r' hm'
    obtain ⟨-, h2⟩ := hcl j1 o1 hj1 hy1 (by rw [E.ivU hj1 hu1]; exact ⟨by simp [pos], by simp [pos]⟩)
    exact ⟨hu, hv1 ▸ h2.symm⟩

/-- A use of a spilled vreg loaded into a fresh scratch register. -/
private theorem use_scr (E : Env vc c g os clob st) {s : IS} (hI : Inv c g os clob st s)
    {j : Nat} {o : Operand} {r : Reg} (hj : os[j]? = some o) (hn : s.R[j]? = some none)
    (hu : o.kind = .use) (hs : scratch o.con = true)
    (hf : regFree c.occ s.taken r (pos g 1) (pos g 2) = true) (hsc : r ∈ scratchOrder o.cls) :
    Inv c g os clob st
      { s with
        R := s.R.set! j (some r)
        taken := (r, pos g 1, pos g 2) :: s.taken
        useScr := (o.vreg, r) :: s.useScr
        pre := (c.loc o.vreg, .reg r) :: s.pre } := by
  have ivU := E.ivU hj hu
  have hex := (regFree_sound E.pf E.occ hf).1
  have hok := scratchOrder_ok hsc
  have hI1 : Inv c g os clob st
      { s with
        R := s.R.set! j (some r)
        taken := (r, pos g 1, pos g 2) :: s.taken
        pre := (c.loc o.vreg, .reg r) :: s.pre } :=
    hI.add hj hn (fun _ => rfl) (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => List.mem_cons_of_mem _ h)
      (fun m h => (List.mem_cons.mp h).symm.imp id fun e => ⟨hu, e⟩) (fun _ h => h) (fun _ h => .inl h) rfl
      ⟨⟨hok.1, hok.2.1⟩, fun p h => absurd h (not_fixed hs p), fun i h => absurd h (not_reuse hs i),
        fun _ => .inr List.mem_cons_self, fun hd => (by rw [hu] at hd; cases hd),
        fun hd => (by rw [hu] at hd; cases hd),
        .inr ⟨⟨_, List.mem_cons_self, rfl, by rw [ivU]; exact Nat.le_refl _, by rw [ivU]; exact Nat.le_refl _⟩,
          .inr (by rw [ivU]; exact hex)⟩⟩
      (fun j' o' hj' _ hy hov =>
        (hI.fresh E hf (by rw [ivU]; exact Nat.le_refl _) (by rw [ivU]; exact Nat.le_refl _) j' o' hj' hy hov).elim)
      (fun v r' hm hrr hov => by
        obtain ⟨-, -, -, -, -, -, -, htk, -⟩ := hI.scr v r' hm
        subst hrr
        exact (noFree E htk hf (by rw [ivU]; exact Nat.le_refl _) (by rw [ivU]; exact Nat.le_refl _) hov).elim)
  have hjs : j < s.R.size := (Array.getElem?_eq_some_iff.mp hn).1
  refine hI1.addScr ⟨j, o, hj, hu, rfl, by simp only; rw [get_set hjs]; simp, hex,
    ⟨_, List.mem_cons_self, rfl, Nat.le_refl _, Nat.le_refl _⟩, ?_⟩
  intro j' o' hj' hy hov
  simp only at hy
  rw [get_set hjs] at hy
  split at hy
  · subst_vars; rw [hj] at hj'; cases hj'; exact ⟨hu, rfl⟩
  · exact (hI.fresh E hf (o := o) (by rw [ivU]; exact Nat.le_refl _) (by rw [ivU]; exact Nat.le_refl _)
      j' o' hj' hy (by rw [ivU]; exact hov)).elim

private theorem keep_iv {g : Nat} {o : Operand} (hd : o.kind = .def) (k : Bool) :
    (opRange g o k).1 = (opRange g o false).1 ∧ (opRange g o false).2 ≤ (opRange g o k).2 ∧
      (opRange g o k).1 ≤ pos g 3 ∧ pos g 3 ≤ (opRange g o k).2 := by
  cases k
  · exact ⟨rfl, Nat.le_refl _, iv_def3 hd⟩
  · have := iv_def3 (g := g) hd
    exact ⟨iv_true.1, iv_true.2, iv_true.1 ▸ this.1, Nat.le_trans this.2 iv_true.2⟩

/-- A def in place. -/
private theorem def_in (E : Env vc c g os clob st) {s : IS} (hI : Inv c g os clob st s)
    {j : Nat} {o : Operand} {r : Reg} (hj : os[j]? = some o) (hn : s.R[j]? = some none)
    (hd : o.kind = .def) (hs : scratch o.con = true) (hr : c.pl.regOf o.vreg = some r) :
    Inv c g os clob st { s with R := s.R.set! j (some r) } :=
  hI.add hj hn (fun _ => rfl) (fun _ h => h) (fun _ h => h) (fun _ h => .inl h) (fun _ h => h)
    (fun _ h => .inl h) rfl
    ⟨E.regCls hj hr, fun p h => absurd h (not_fixed hs p), fun i h => absurd h (not_reuse hs i),
      fun hu => (by rw [hd] at hu; cases hu), fun _ _ => .inl (loc_reg.mpr hr),
      fun _ => E.inClob hj hd hr, .inl hr⟩
    (hI.legitIn E hj hr)
    (fun v r' hm hrr hov => by
      obtain ⟨-, -, -, -, -, -, hex, -, -⟩ := hI.scr v r' hm
      subst hrr
      exact (noIn E hex hj hr hov (by simp [pos])).elim)

/-- A def of a spilled vreg in a scratch register. -/
private theorem def_scr (E : Env vc c g os clob st) {s : IS} (hI : Inv c g os clob st s)
    (hcl : ∀ r ∈ clob, (r, pos g 3, pos g 3) ∈ s.taken)
    {j : Nat} {o : Operand} {r : Reg} (hj : os[j]? = some o) (hn : s.R[j]? = some none)
    (hd : o.kind = .def) (hs : scratch o.con = true)
    (hf : regFree c.occ s.taken r (opRange g o (st j o)).1 (opRange g o (st j o)).2 = true)
    (hsc : r ∈ scratchOrder o.cls) :
    Inv c g os clob st
      { s with
        R := s.R.set! j (some r)
        taken := (r, (opRange g o (st j o)).1, (opRange g o (st j o)).2) :: s.taken
        post := if st j o = true then (.reg r, c.loc o.vreg) :: s.post else s.post } := by
  have hex := (regFree_sound E.pf E.occ hf).1
  have hok := scratchOrder_ok hsc
  obtain ⟨k1, k2, k3, k4⟩ := keep_iv (g := g) hd (st j o)
  exact hI.add hj hn (fun _ => rfl) (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h) (fun _ h => .inl h)
    (fun _ h => mem_ite1 h) (fun m h => (mem_ite2 h).imp id fun ⟨h1, h2⟩ => ⟨hd, h1, h2⟩) rfl
    ⟨⟨hok.1, hok.2.1⟩, fun p h => absurd h (not_fixed hs p), fun i h => absurd h (not_reuse hs i),
      fun hu => (by rw [hd] at hu; cases hu), fun _ hst => .inr (mem_ite3 hst),
      fun _ => notClob E hcl hf k3 k4,
      .inr ⟨⟨_, List.mem_cons_self, rfl, Nat.le_of_eq k1, k2⟩, .inr (hex.mono (Nat.le_of_eq k1) k2)⟩⟩
    (fun j' o' hj' _ hy hov => (hI.fresh E hf (Nat.le_of_eq k1) k2 j' o' hj' hy hov).elim)
    (fun v r' hm hrr hov => by
      obtain ⟨-, -, -, -, -, -, -, htk, -⟩ := hI.scr v r' hm
      subst hrr
      exact (noFree E htk hf (Nat.le_of_eq k1) k2 hov).elim)

end


section
variable {vc : VCode} {c : LinearScan.Ctx} {g : Nat} {os : Array Operand} {clob : List Reg}
  {st : Nat → Operand → Bool}

private theorem mono_set {s s2 : IS} {j : Nat} {x : Reg} (hn : s.R[j]? = some none)
    (hR : s2.R = s.R.set! j (some x)) :
    (∀ (k : Nat) (y : Reg), s.R[k]? = some (some y) → s2.R[k]? = some (some y)) ∧
      s2.R[j]? = some (some x) := by
  have hjs : j < s.R.size := (Array.getElem?_eq_some_iff.mp hn).1
  refine ⟨fun k y hy => ?_, by rw [hR, get_set hjs]; simp⟩
  rw [hR, get_set hjs, ite_eq_right]; exact hy
  rintro rfl; rw [hn] at hy; cases hy

private theorem no_late (E : Env vc c g os clob st) (v : Nat) :
    (os.any fun o' => o'.vreg == v && o'.kind == .use && o'.pos == .late) = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [Array.any_eq_true] at h
  obtain ⟨i, hi, h⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have := E.early (j := i) (by simp [hi]) h.1.2
  rw [this] at h; cases h.2

/-- **The use pass**. -/
private theorem use_pass (E : Env vc c g os clob st) :
    ∀ (L : List (Operand × Nat)) (s s' : IS), (∀ x ∈ L, os[x.2]? = some x.1) →
    Inv c g os clob st s → (∀ r ∈ clob, (r, pos g 3, pos g 3) ∈ s.taken) →
    (∀ (k : Nat) (o : Operand), os[k]? = some o → ((∃ p, o.con = .fixed p) ∨ ∃ i, o.con = .reuse i) →
      ∃ y, s.R[k]? = some (some y)) →
    c.usePass g os L s = .ok s' →
    Inv c g os clob st s' ∧ (∀ r ∈ clob, (r, pos g 3, pos g 3) ∈ s'.taken) ∧
    (∀ x ∈ L, x.1.kind = .use → ∃ y, s'.R[x.2]? = some (some y)) ∧
    (∀ (k : Nat) (y : Reg), s.R[k]? = some (some y) → s'.R[k]? = some (some y))
  | [], s, s', _, hI, hcl, _, h => by
    simp only [Ctx.usePass, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hI, hcl, by simp, fun _ _ h => h⟩
  | (o, j) :: rest, s, s', hL, hI, hcl, hset, h => by
    have hj : os[j]? = some o := hL (o, j) List.mem_cons_self
    have hL' : ∀ x ∈ rest, os[x.2]? = some x.1 := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    -- one step to `s2`, setting `j` (if it is an unset use)
    have step : ∀ s2 : IS, c.usePass g os rest s2 = .ok s' → Inv c g os clob st s2 →
        (∀ r ∈ clob, (r, pos g 3, pos g 3) ∈ s2.taken) →
        (∀ (k : Nat) (y : Reg), s.R[k]? = some (some y) → s2.R[k]? = some (some y)) →
        (o.kind = .use → ∃ y, s2.R[j]? = some (some y)) →
        Inv c g os clob st s' ∧ (∀ r ∈ clob, (r, pos g 3, pos g 3) ∈ s'.taken) ∧
        (∀ x ∈ (o, j) :: rest, x.1.kind = .use → ∃ y, s'.R[x.2]? = some (some y)) ∧
        (∀ (k : Nat) (y : Reg), s.R[k]? = some (some y) → s'.R[k]? = some (some y)) := by
      intro s2 hs2 hI2 hcl2 hm2 hj2
      obtain ⟨h1, h2, h3, h4⟩ := use_pass E rest s2 s' hL' hI2 hcl2
        (fun k o' hk ho' => (hset k o' hk ho').imp fun y hy => hm2 k y hy) hs2
      refine ⟨h1, h2, fun x hx hu => ?_, fun k y hy => h4 k y (hm2 k y hy)⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · obtain ⟨y, hy⟩ := hj2 hu; exact ⟨y, h4 _ _ hy⟩
      · exact h3 x hx hu
    simp only [Ctx.usePass] at h
    split at h
    · rename_i hc
      refine step s h hI hcl (fun _ _ h => h) fun hu => ?_
      simp only [Bool.or_eq_true, hu, bne_self_eq_false, Bool.false_eq_true, or_false] at hc
      rw [Array.getD_eq_getD_getElem?] at hc
      rcases hr : s.R[j]? with _ | (_ | y)
      · rw [hr] at hc; cases hc
      · rw [hr] at hc; cases hc
      · exact ⟨y, rfl⟩
    · rename_i hc
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, bne_eq_false_iff_eq] at hc
      obtain ⟨hc1, hu⟩ := hc
      have hn := getD_none hI hj hc1
      have hs := scratch_of E hj hn hset
      split at h
      · rename_i r hr
        obtain ⟨m1, m2⟩ := mono_set (s2 := { s with R := s.R.set! j (some r) }) hn rfl
        exact step _ h (use_in E hI hj hn hu hs hr) hcl m1 fun _ => ⟨r, m2⟩
      · split at h
        · rename_i r hr
          obtain ⟨m1, m2⟩ := mono_set (s2 := { s with R := s.R.set! j (some r) }) hn rfl
          exact step _ h (use_lookup E hI hj hn hu hs (lookup_mem hr)) hcl m1 fun _ => ⟨r, m2⟩
        · simp only [no_late E] at h
          split at h
          · rename_i r hr
            obtain ⟨hf, hsc⟩ := scratch_spec hr
            obtain ⟨m1, m2⟩ := mono_set (s2 := { s with
              R := s.R.set! j (some r)
              taken := (r, pos g 1, pos g 2) :: s.taken
              useScr := (o.vreg, r) :: s.useScr
              pre := (c.loc o.vreg, .reg r) :: s.pre }) hn rfl
            exact step _ h (use_scr E hI hj hn hu hs hf hsc)
              (fun r hr => List.mem_cons_of_mem _ (hcl r hr)) m1 fun _ => ⟨r, m2⟩
          · cases h

/-- **The def pass**. -/
private theorem def_pass (E : Env vc c g os clob st) :
    ∀ (L : List (Operand × Nat)) (s s' : IS), (∀ x ∈ L, os[x.2]? = some x.1) →
    Inv c g os clob st s → (∀ r ∈ clob, (r, pos g 3, pos g 3) ∈ s.taken) →
    (∀ (k : Nat) (o : Operand), os[k]? = some o → ((∃ p, o.con = .fixed p) ∨ ∃ i, o.con = .reuse i) →
      ∃ y, s.R[k]? = some (some y)) →
    (∀ (k : Nat) (o : Operand), os[k]? = some o → o.kind = .use → ∃ y, s.R[k]? = some (some y)) →
    c.defPass g st L s = .ok s' →
    Inv c g os clob st s' ∧ (∀ x ∈ L, ∃ y, s'.R[x.2]? = some (some y)) ∧
    (∀ (k : Nat) (y : Reg), s.R[k]? = some (some y) → s'.R[k]? = some (some y))
  | [], s, s', _, hI, _, _, _, h => by
    simp only [Ctx.defPass, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hI, by simp, fun _ _ h => h⟩
  | (o, j) :: rest, s, s', hL, hI, hcl, hset, huse, h => by
    have hj : os[j]? = some o := hL (o, j) List.mem_cons_self
    have hL' : ∀ x ∈ rest, os[x.2]? = some x.1 := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    have step : ∀ s2 : IS, c.defPass g st rest s2 = .ok s' → Inv c g os clob st s2 →
        (∀ r ∈ clob, (r, pos g 3, pos g 3) ∈ s2.taken) →
        (∀ (k : Nat) (y : Reg), s.R[k]? = some (some y) → s2.R[k]? = some (some y)) →
        (∃ y, s2.R[j]? = some (some y)) →
        Inv c g os clob st s' ∧ (∀ x ∈ (o, j) :: rest, ∃ y, s'.R[x.2]? = some (some y)) ∧
        (∀ (k : Nat) (y : Reg), s.R[k]? = some (some y) → s'.R[k]? = some (some y)) := by
      intro s2 hs2 hI2 hcl2 hm2 hj2
      obtain ⟨h1, h2, h3⟩ := def_pass E rest s2 s' hL' hI2 hcl2
        (fun k o' hk ho' => (hset k o' hk ho').imp fun y hy => hm2 k y hy)
        (fun k o' hk ho' => (huse k o' hk ho').imp fun y hy => hm2 k y hy) hs2
      refine ⟨h1, fun x hx => ?_, fun k y hy => h3 k y (hm2 k y hy)⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · obtain ⟨y, hy⟩ := hj2; exact ⟨y, h3 _ _ hy⟩
      · exact h2 x hx
    simp only [Ctx.defPass] at h
    split at h
    · rename_i hc
      refine step s h hI hcl (fun _ _ h => h) ?_
      rw [Array.getD_eq_getD_getElem?] at hc
      rcases hr : s.R[j]? with _ | (_ | y)
      · rw [hr] at hc; cases hc
      · rw [hr] at hc; cases hc
      · exact ⟨y, rfl⟩
    · rename_i hc
      have hn := getD_none hI hj (by simpa using hc)
      have hs := scratch_of E hj hn hset
      have hd : o.kind = .def := by
        cases hk : o.kind
        · obtain ⟨y, hy⟩ := huse j o hj hk; rw [hn] at hy; cases hy
        · rfl
      split at h
      · rename_i r hr
        obtain ⟨m1, m2⟩ := mono_set (s2 := { s with R := s.R.set! j (some r) }) hn rfl
        exact step _ h (def_in E hI hj hn hd hs hr) hcl m1 ⟨r, m2⟩
      · split at h
        · rename_i r hr
          obtain ⟨hf, hsc⟩ := scratch_spec hr
          obtain ⟨m1, m2⟩ := mono_set (s2 := { s with
            R := s.R.set! j (some r)
            taken := (r, (opRange g o (st j o)).1, (opRange g o (st j o)).2) :: s.taken
            post := if st j o = true then (.reg r, c.loc o.vreg) :: s.post else s.post }) hn rfl
          exact step _ h (def_scr E hI hcl hj hn hd hs hf hsc)
            (fun r hr => List.mem_cons_of_mem _ (hcl r hr)) m1 ⟨r, m2⟩
        · cases h

end


/-! ## The result -/

private theorem forM_ok' {α : Type} {l : List α} {f : α → Except String Unit} (h : ∀ x ∈ l, f x = .ok ()) :
    l.forM f = .ok () := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.forM, h a List.mem_cons_self]
    exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)

private theorem eraseDups_snd {α β : Type} [DecidableEq α] [DecidableEq β] :
    ∀ (n : Nat) (l : List (α × β)), l.length ≤ n → (∀ a ∈ l, ∀ b ∈ l, a.2 = b.2 → a = b) →
      (l.eraseDups.map (·.2)).Nodup
  | _, [], _, _ => by simp
  | 0, _ :: _, hn, _ => by simp at hn
  | n + 1, a :: l, hn, h => by
    rw [List.eraseDups_cons, List.map_cons, List.nodup_cons]
    constructor
    · intro hm
      obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
      rw [List.mem_eraseDups, List.mem_filter] at hb
      have := h a List.mem_cons_self b (List.mem_cons_of_mem _ hb.1) he.symm
      subst this; simp at hb
    · refine eraseDups_snd n _ (Nat.le_trans (List.length_filter_le _ _) (by simp at hn; omega))
        fun x hx y hy => h x (List.mem_cons_of_mem _ (List.mem_filter.mp hx).1) y
          (List.mem_cons_of_mem _ (List.mem_filter.mp hy).1)

private theorem mem_clean {m : Loc × Loc} {l : List (Loc × Loc)} :
    m ∈ cleanMoves l ↔ m ∈ l ∧ m.1 ≠ m.2 := by
  unfold cleanMoves
  rw [List.mem_eraseDups, List.mem_filter]
  rcases m with ⟨a, b⟩
  simp

private theorem clean_nodup {l : List (Loc × Loc)}
    (h : ∀ m ∈ l, ∀ m' ∈ l, m.1 ≠ m.2 → m'.1 ≠ m'.2 → m.2 = m'.2 → m = m') :
    ((cleanMoves l).map (·.2)).Nodup := by
  unfold cleanMoves
  refine eraseDups_snd _ _ (Nat.le_refl _) fun a ha b hb he => ?_
  rw [List.mem_filter] at ha hb
  rcases a with ⟨a1, a2⟩
  rcases b with ⟨b1, b2⟩
  simp only [bne_iff_ne, ne_eq] at ha hb
  exact h _ ha.1 _ hb.1 ha.2 hb.2 he

private theorem nodup_idx {γ δ : Type} (p : γ → Bool) (f : γ → δ) :
    ∀ (L : List γ), (∀ (i i' : Nat) (a a' : γ), i ≠ i' → L[i]? = some a → L[i']? = some a' → p a = true →
      p a' = true → f a ≠ f a') → ((L.filter p).map f).Nodup
  | [], _ => by simp
  | a :: L, h => by
    have ih := nodup_idx p f L fun i i' b b' hne hb hb' => h (i + 1) (i' + 1) b b' (by omega) hb hb'
    rw [List.filter_cons]
    split
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, ih⟩
      obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
      rw [List.mem_filter] at hb
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb.1
      exact h 0 (i + 1) a b (by omega) rfl hi ‹_› hb.2 he.symm
    · exact ih

section
variable {vc : VCode} {c : LinearScan.Ctx} {g : Nat} {os : Array Operand} {clob : List Reg}
  {st : Nat → Operand → Bool}

/-- The vreg in register `x` over a position of the interval of operand `j` is `j`'s. -/
private theorem owner (E : Env vc c g os clob st) {S : IS} (hI : Inv c g os clob st S) {j : Nat}
    {o : Operand} {x : Reg} (hj : os[j]? = some o) (hx : S.R[j]? = some (some x)) {w q : Nat}
    (hw : c.pl.regOf w = some x) (h1 : (opRange g o false).1 ≤ q) (h2 : q ≤ (opRange g o false).2)
    (hq : c.pl.cov w q = true) : w = o.vreg := by
  have hc := hI.cat j o x hj hx
  rcases hc.kind with hr | ⟨-, ⟨p, hp⟩ | hex⟩
  · exact E.pf.inter _ _ x q hw hr hq (E.cov hj h1 h2)
  · have hxp := hc.fix p hp; subst hxp
    exact (E.pf.claim g os E.hos o (E.mem hj) x hp).2 w hw q (by rw [iv_true.1]; exact h1)
      (Nat.le_trans h2 iv_true.2) hq
  · exact absurd (hex w hw q h1 h2 hq) (by simp)

private theorem loc_inj (E : Env vc c g os clob st) {v w : Nat} (hv : v < c.fn.nv) (hw : w < c.fn.nv)
    {p : Nat} (hcv : c.pl.cov v p = true) (hcw : c.pl.cov w p = true) (he : c.loc v = c.loc w) : v = w := by
  rcases hr : c.pl.regOf v with _ | r
  · have hl : c.loc v = .stack (c.pl.home.getD v 0) (c.fn.clsOf v) := by
      simp [Ctx.loc, Fn.loc, hr]
    obtain ⟨h1, h2, h3⟩ := loc_stack (he ▸ hl)
    exact E.pf.homes v w p hv hw hr h1 h2.symm h3.symm hcv hcw
  · exact E.pf.inter v w r p hr (loc_reg.mp (he ▸ loc_reg.mpr hr)) hcv hcw

private theorem cov1 (E : Env vc c g os clob st) {j : Nat} {o : Operand} (hj : os[j]? = some o)
    (hu : o.kind = .use) : c.pl.cov o.vreg (pos g 1) = true :=
  E.cov hj (by rw [E.ivU hj hu]; exact Nat.le_refl _) (by rw [E.ivU hj hu]; simp [pos])

private theorem cov3 (E : Env vc c g os clob st) {j : Nat} {o : Operand} (hj : os[j]? = some o)
    (hd : o.kind = .def) : c.pl.cov o.vreg (pos g 3) = true :=
  E.cov hj (iv_def3 hd).1 (iv_def3 hd).2

/-- No move before writes the location of a vreg live at position 1 (unless it is a no-op). -/
private theorem pre_dst (E : Env vc c g os clob st) {S : IS} (hI : Inv c g os clob st S)
    {m : Loc × Loc} (hm : m ∈ cleanMoves S.pre.reverse) {w : Nat} (hw : c.pl.cov w (pos g 1) = true) :
    m.2 ≠ c.loc w := by
  rw [mem_clean, List.mem_reverse] at hm
  obtain ⟨j, o, x, hj, hu, hx, rfl⟩ := hI.pre m hm.1
  intro he
  have := owner E hI hj hx (loc_reg.mp he.symm) (by rw [E.ivU hj hu]; exact Nat.le_refl _)
    (by rw [E.ivU hj hu]; simp [pos]) hw
  subst this
  exact hm.2 he.symm

/-- No move after writes the location of a vreg live at position 4 other than the def's. -/
private theorem post_dst (E : Env vc c g os clob st) {S : IS} (hI : Inv c g os clob st S)
    {m : Loc × Loc} (hm : m ∈ S.post) {w : Nat} (hwn : w < c.fn.nv) (hw : c.pl.cov w (pos g 4) = true)
    (he : m.2 = c.loc w) : ∃ (j : Nat) (o : Operand) (x : Reg), os[j]? = some o ∧ o.kind = .def ∧
      S.R[j]? = some (some x) ∧ o.vreg = w ∧
      m = (.reg x, c.loc o.vreg) := by
  obtain ⟨j, o, x, hj, hd, hs, hx, rfl⟩ := hI.post m hm
  have := loc_inj E (E.nv o (E.mem hj)) hwn (E.st j o hs) hw he
  exact ⟨j, o, x, hj, hd, hx, this, rfl⟩

private theorem pair_get {A : Array Loc} {j : Nat} {o : Operand} {l : Loc}
    (h : (os.zip A).toList[j]? = some (o, l)) : os[j]? = some o ∧ A[j]? = some l := by
  rw [Array.toList_zip, List.zip, List.getElem?_zipWith] at h
  rw [← Array.getElem?_toList, ← Array.getElem?_toList (xs := A)]
  split at h
  · cases h; simp_all
  · cases h

/-- **The static checks** accept the operand registers. -/
private theorem static_ok (E : Env vc c g os clob st) {S : IS} (hI : Inv c g os clob st S)
    (hall : ∀ j, j < os.size → ∃ y, S.R[j]? = some (some y)) (cc : CheckCtx) (w : String) :
    cc.checkStatic w os (S.R.map fun r => .reg (r.getD .sp)) clob = .ok () := by
  have hsz : (S.R.map fun r => Loc.reg (r.getD .sp)).size = os.size := by simp [hI.size]
  -- every pair: an operand with its register
  have hget : ∀ (j : Nat) (o : Operand) (l : Loc), (os.zip (S.R.map fun r => Loc.reg (r.getD .sp))).toList[j]? = some (o, l) →
      ∃ x, os[j]? = some o ∧ S.R[j]? = some (some x) ∧ l = .reg x := by
    intro j o l h
    obtain ⟨h1, h2⟩ := pair_get h
    obtain ⟨y, hy⟩ := hall j (Array.getElem?_eq_some_iff.mp h1).1
    rw [Array.getElem?_map, hy] at h2
    cases h2
    exact ⟨y, h1, hy, rfl⟩
  have hmem : ∀ (o : Operand) (l : Loc), (o, l) ∈ (os.zip (S.R.map fun r => Loc.reg (r.getD .sp))).toList →
      ∃ (j : Nat) (x : Reg), os[j]? = some o ∧ S.R[j]? = some (some x) ∧ l = .reg x := by
    intro o l h
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h
    obtain ⟨x, h1⟩ := hget j o l hj
    exact ⟨j, x, h1⟩
  have hop : ∀ y ∈ (os.zip (S.R.map fun r => Loc.reg (r.getD .sp))).toList.zipIdx,
      cc.checkOperand w os (S.R.map fun r => Loc.reg (r.getD .sp)) y = .ok () := by
    rintro ⟨⟨o, l⟩, j⟩ hy
    obtain ⟨x, hj, hx, rfl⟩ := hget j o l (List.mem_zipIdx_iff_getElem?.mp hy)
    have hc := hI.cat j o x hj hx
    unfold CheckCtx.checkOperand
    rcases hcon : o.con with _ | _ | _ | p | i
    · simp [ensure, hcon, CheckCtx.locOk, Loc.cls?, hc.ok.1, hc.ok.2]; rfl
    · simp [ensure, hcon, CheckCtx.locOk, Loc.cls?, hc.ok.1, hc.ok.2, Loc.isReg]; rfl
    · exact absurd hcon (E.ok.noStack o (E.mem hj))
    · have := hc.fix p hcon; subst this
      simp [ensure, hcon, CheckCtx.locOk, Loc.cls?, hc.ok.1, hc.ok.2]; rfl
    · obtain ⟨-, -, oi, hoi, hk, -⟩ := E.ok.reuse j o i (tl hj) hcon
      rw [Array.getElem?_toList] at hoi
      have e2 : (S.R.map fun r => Loc.reg (r.getD .sp))[i]? = some (.reg x) := by
        rw [Array.getElem?_map, hc.reu i hcon]; rfl
      simp [ensure, hcon, hoi, e2, CheckCtx.locOk, Loc.cls?, hc.ok.1, hc.ok.2, hk, Loc.isReg]; rfl
  have hnodup : (((os.zip (S.R.map fun r => Loc.reg (r.getD .sp))).toList.filter (·.1.kind == .def)).map
      (·.2)).Nodup := by
    refine nodup_idx _ _ _ fun i i' a a' hne ha ha' hp hp' he => ?_
    rcases a with ⟨o, l⟩
    rcases a' with ⟨o', l'⟩
    obtain ⟨x, hj, hx, rfl⟩ := hget i o l ha
    obtain ⟨x', hj', hx', rfl⟩ := hget i' o' l' ha'
    simp only [beq_iff_eq] at hp hp'
    simp only [Loc.reg.injEq] at he
    subst he
    have hov : Ov (opRange g o false) (opRange g o' false) :=
      ⟨Nat.le_trans (iv_def3 hp).1 (iv_def3 hp').2, Nat.le_trans (iv_def3 hp').1 (iv_def3 hp).2⟩
    rcases hI.disj i o i' o' x hj hj' hne hx hx' hov with ⟨hu, -⟩ | hr | hr
    · rw [hp] at hu; cases hu
    · obtain ⟨-, -, oi, hoi, hk, -⟩ := E.ok.reuse i o i' (tl hj) hr
      rw [Array.getElem?_toList, hj'] at hoi; cases hoi; rw [hp'] at hk; cases hk
    · obtain ⟨-, -, oi, hoi, hk, -⟩ := E.ok.reuse i' o' i (tl hj') hr
      rw [Array.getElem?_toList, hj] at hoi; cases hoi; rw [hp] at hk; cases hk
  have hnolate : ∀ y ∈ ((os.zip (S.R.map fun r => Loc.reg (r.getD .sp))).toList.filter
      (·.1.kind == .use)).filter (·.1.pos == .late), False := by
    rintro ⟨o, l⟩ hy
    rw [List.mem_filter, List.mem_filter] at hy
    obtain ⟨j, x, hj, -, -⟩ := hmem o l hy.1.1
    have := E.early hj (by simpa using hy.1.2)
    have hl : o.pos = .late := by simpa using hy.2
    rw [this] at hl; cases hl
  have hconf : ∀ y ∈ (os.zip (S.R.map fun r => Loc.reg (r.getD .sp))).toList.filter (·.1.kind == .def),
      (!(defConflicts ((os.zip (S.R.map fun r => Loc.reg (r.getD .sp))).toList.filter (·.1.kind == .use))
        (clob.map Loc.reg) y.1.pos).contains y.2) = true := by
    rintro ⟨o, l⟩ hy
    rw [List.mem_filter] at hy
    obtain ⟨j, x, hj, hx, rfl⟩ := hmem o l hy.1
    have hd : o.kind = .def := by simpa using hy.2
    have hc := hI.cat j o x hj hx
    have hcl : Loc.reg x ∉ clob.map Loc.reg := fun h => by
      obtain ⟨r, hr, he⟩ := List.mem_map.mp h
      cases he; exact hc.clob hd hr
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, List.contains_iff_mem]
    rcases hpos : o.pos
    · simp only [defConflicts, List.mem_append, not_or]
      refine ⟨fun hu => ?_, hcl⟩
      obtain ⟨⟨o', l'⟩, hy', hyl⟩ := List.mem_map.mp hu
      rw [List.mem_filter] at hy'
      obtain ⟨j', x', hj', hx', rfl⟩ := hmem o' l' hy'.1
      have hu' : o'.kind = .use := by simpa using hy'.2
      simp only [Loc.reg.injEq] at hyl
      subst hyl
      have hne : j ≠ j' := by rintro rfl; rw [hj] at hj'; cases hj'; rw [hd] at hu'; cases hu'
      have hov : Ov (opRange g o false) (opRange g o' false) := by
        rw [iv_def hd, E.ivU hj' hu']; simp [Ov, opSlot, hpos, pos]
      rcases hI.disj j o j' o' x' hj hj' hne hx hx' hov with ⟨hu, -⟩ | hr | hr
      · rw [hd] at hu; cases hu
      · have := E.ok.earlyDef o (E.mem hj) hd hpos; rw [hr] at this; cases this
      · obtain ⟨hk, -⟩ := E.ok.reuse j' o' j (tl hj') hr; rw [hk] at hu'; cases hu'
    · simp only [defConflicts, List.mem_append, not_or]
      refine ⟨fun hu => ?_, hcl⟩
      obtain ⟨y, hy, -⟩ := List.mem_map.mp hu
      exact hnolate y hy
  unfold CheckCtx.checkStatic
  simp only [ensure, hsz, beq_self_eq_true, ite_true, forM_ok' hop, hnodup, decide_true]
  rw [forM_ok' (fun y hy => by simp only [hconf y hy, ite_true]; rfl),
    forM_ok' (fun y hy => absurd (hnolate y hy) id)]
  rfl

end


section
variable {vc : VCode} {c : LinearScan.Ctx} {g : Nat} {os : Array Operand} {clob : List Reg}
  {st : Nat → Operand → Bool}

private theorem bind_ok' {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem inv_init : Inv c g os clob st
    { R := Array.replicate os.size none, taken := [], pre := [], post := [], useScr := [] } where
  size := Array.size_replicate
  cat j o x _ hx := by simp [Array.getElem?_replicate] at hx
  disj j o j' o' x _ _ _ hx := by simp [Array.getElem?_replicate] at hx
  pre m hm := by cases hm
  post m hm := by cases hm
  scr v r hm := by cases hm

/-- **What the passes compute**: a state meeting the invariant with every operand set. -/
private theorem inst_run {i : MInst} (E : Env vc c g os i.clobbers (c.store g i.isTerminator (keptIdx i os)))
    (hi : c.fn.insts[g]? = some i) {io : IOut} (h : c.inst g = .ok io) :
    ∃ S : IS, Inv c g os i.clobbers (c.store g i.isTerminator (keptIdx i os)) S ∧
      (∀ j, j < os.size → ∃ y, S.R[j]? = some (some y)) ∧
      io = { allocs := S.R.map fun r => .reg (r.getD .sp)
             pre := cleanMoves S.pre.reverse
             post := cleanMoves S.post.reverse } := by
  have hos' : c.fn.ops.getD g #[] = os := by rw [Array.getD_eq_getD_getElem?, E.hos]; rfl
  have hi' : c.fn.insts.getD g default = i := by rw [Array.getD_eq_getD_getElem?, hi]; rfl
  have hL : ∀ x ∈ os.toList.zipIdx, os[x.2]? = some x.1 := fun x hx => by
    rw [← Array.getElem?_toList]; exact List.mem_zipIdx_iff_getElem?.mp hx
  have hnd : (os.toList.zipIdx.map (·.2)).Nodup := by
    show (List.map Prod.snd _).Nodup
    rw [List.zipIdx_map_snd]; exact List.nodup_range'
  have hin : ∀ j o, os[j]? = some o → (o, j) ∈ os.toList.zipIdx := fun j o hj =>
    List.mem_zipIdx_iff_getElem?.mpr (by rw [Array.getElem?_toList]; exact hj)
  unfold Ctx.inst at h
  simp only [hos', hi'] at h
  obtain ⟨s1, h1, h⟩ := bind_ok' h
  obtain ⟨hI1, hu1, hfx1, hset1, -⟩ := fixed_pass E _ _ s1 hL hnd inv_init rfl
    (fun k y hy => by simp [Array.getElem?_replicate] at hy) h1
  obtain ⟨s2, h2, h⟩ := bind_ok' h
  have hcl1 : ∀ r ∈ i.clobbers, (r, pos g 3, pos g 3) ∈
      i.clobbers.map (fun r => (r, pos g 3, pos g 3)) ++ s1.taken :=
    fun r hr => List.mem_append_left _ (List.mem_map_of_mem hr)
  obtain ⟨hI2, -, hcl2, hset2, hm2⟩ := reuse_pass E _ _ s2 hL hnd
    (hI1.taken _ fun y hy => List.mem_append_right _ hy) hu1 hcl1
    (fun k y hy => .inl (hfx1 k y hy)) h2
  obtain ⟨s3, h3, h⟩ := bind_ok' h
  have hset : ∀ (k : Nat) (o : Operand), os[k]? = some o → ((∃ p, o.con = .fixed p) ∨ ∃ i, o.con = .reuse i) →
      ∃ y, s2.R[k]? = some (some y) := by
    rintro k o hk (⟨p, hp⟩ | ⟨ui, hr⟩)
    · obtain ⟨y, hy⟩ := hset1 (o, k) (hin k o hk) p hp
      exact ⟨y, hm2 k y hy⟩
    · exact hset2 (o, k) (hin k o hk) ui hr
  obtain ⟨hI3, hcl3, hu3, hm3⟩ := use_pass E _ s2 s3 hL hI2 hcl2 hset h3
  obtain ⟨S, h4, h⟩ := bind_ok' h
  obtain ⟨hI4, hall, -⟩ := def_pass E _ s3 S hL hI3 hcl3
    (fun k o hk ho => (hset k o hk ho).imp fun y hy => hm3 k y hy)
    (fun k o hk hu => hu3 (o, k) (hin k o hk) hu) h4
  refine ⟨S, hI4, fun j hj => hall (os[j], j) (hin j _ (Array.getElem?_eq_getElem hj)), ?_⟩
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact h.symm

end

/-- What `Ctx.inst` computes for global instruction `g` (`i`, operands `os`). -/
structure InstFacts (c : LinearScan.Ctx) (g : Nat) (i : MInst) (os : Array Operand) (io : IOut) : Prop where
  static : ∀ (cc : CheckCtx) (w : String), cc.checkStatic w os io.allocs i.clobbers = .ok ()
  size : io.allocs.size = os.size
  allocs : ∀ (j : Nat) (o : Operand), os[j]? = some o →
    ∃ x, io.allocs[j]? = some (.reg x) ∧ x.allocatable = true ∧ x.realClass? = some o.cls
  fixed : ∀ (j : Nat) (o : Operand) (p : Reg), os[j]? = some o → o.con = .fixed p → io.allocs[j]? = some (.reg p)
  pre : ∀ m ∈ io.pre, ∃ (j : Nat) (o : Operand), os[j]? = some o ∧ o.kind = .use ∧ m.1 = c.loc o.vreg ∧
    io.allocs[j]? = some m.2
  preNodup : (io.pre.map (·.2)).Nodup
  preSrc : ∀ m ∈ io.pre, ∀ m' ∈ io.pre, m.1 ≠ m'.2
  useIn : ∀ (j : Nat) (o : Operand), os[j]? = some o → o.kind = .use →
    (io.allocs[j]? = some (c.loc o.vreg) ∧ ∀ m ∈ io.pre, m.2 ≠ c.loc o.vreg) ∨
      ∃ l, io.allocs[j]? = some l ∧ (c.loc o.vreg, l) ∈ io.pre
  post : ∀ m ∈ io.post, ∃ (j : Nat) (o : Operand), os[j]? = some o ∧ o.kind = .def ∧
    c.store g i.isTerminator (keptIdx i os) j o = true ∧ io.allocs[j]? = some m.1 ∧
      m.2 = c.loc o.vreg
  postNodup : (io.post.map (·.2)).Nodup
  postSrc : ∀ m ∈ io.post, ∀ m' ∈ io.post, m.1 ≠ m'.2
  defOut : ∀ (j : Nat) (o : Operand), os[j]? = some o → o.kind = .def →
    c.store g i.isTerminator (keptIdx i os) j o = true →
    (io.allocs[j]? = some (c.loc o.vreg) ∧ ∀ m ∈ io.post, m.2 ≠ c.loc o.vreg) ∨
      ∃ l, io.allocs[j]? = some l ∧ (l, c.loc o.vreg) ∈ io.post
  frame : ∀ v, v < c.fn.nv → c.pl.covI v (pos g 0) (pos g 4) = true →
    (∀ o ∈ os.toList, o.kind = .def → o.vreg ≠ v) →
    (∀ m ∈ io.pre, m.2 ≠ c.loc v) ∧
    (∀ (j : Nat) (o : Operand) (l : Loc), os[j]? = some o → o.kind = .def → io.allocs[j]? = some l → l ≠ c.loc v) ∧
    (∀ m ∈ io.post, m.2 ≠ c.loc v)


section
variable {vc : VCode} {c : LinearScan.Ctx} {g : Nat} {os : Array Operand}

/-- **The facts** from the final state of the passes. -/
private theorem facts {i : MInst} (E : Env vc c g os i.clobbers (c.store g i.isTerminator (keptIdx i os)))
    {S : IS} (hI : Inv c g os i.clobbers (c.store g i.isTerminator (keptIdx i os)) S)
    (hall : ∀ j, j < os.size → ∃ y, S.R[j]? = some (some y)) :
    InstFacts c g i os { allocs := S.R.map fun r => .reg (r.getD .sp)
                         pre := cleanMoves S.pre.reverse
                         post := cleanMoves S.post.reverse } := by
  have getx : ∀ {j : Nat} {o : Operand}, os[j]? = some o → ∃ x, S.R[j]? = some (some x) ∧
      (S.R.map fun r => Loc.reg (r.getD .sp))[j]? = some (.reg x) := by
    intro j o hj
    obtain ⟨x, hx⟩ := hall j (Array.getElem?_eq_some_iff.mp hj).1
    exact ⟨x, hx, by rw [Array.getElem?_map, hx]; rfl⟩
  have alx : ∀ {j : Nat} {x : Reg}, S.R[j]? = some (some x) →
      (S.R.map fun r => Loc.reg (r.getD .sp))[j]? = some (.reg x) := fun hx => by
    rw [Array.getElem?_map, hx]; rfl
  -- no move after writes a stored def's location but its own move
  have noPost : ∀ {j : Nat} {o : Operand} {x : Reg}, os[j]? = some o → o.kind = .def →
      c.store g i.isTerminator (keptIdx i os) j o = true → S.R[j]? = some (some x) →
      c.loc o.vreg = .reg x → ∀ m ∈ cleanMoves S.post.reverse, m.2 ≠ c.loc o.vreg := by
    intro j o x hj hd hs hx hl m hm he
    rw [mem_clean, List.mem_reverse] at hm
    obtain ⟨j', o', x', hj', hd', hx', hv, rfl⟩ :=
      post_dst E hI hm.1 (E.nv o (E.mem hj)) (E.st j o hs) he
    have := E.def_inj hj' hj hd' hd hv; subst this
    rw [hj] at hj'; cases hj'; rw [hx] at hx'; cases hx'
    exact hm.2 hl.symm
  refine ⟨fun cc w => static_ok E hI hall cc w, by simp [hI.size], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro j o hj
    obtain ⟨x, hx, ha⟩ := getx hj
    exact ⟨x, ha, (hI.cat j o x hj hx).ok⟩
  · intro j o p hj hp
    obtain ⟨x, hx, ha⟩ := getx hj
    rw [ha, (hI.cat j o x hj hx).fix p hp]
  · intro m hm
    rw [mem_clean, List.mem_reverse] at hm
    obtain ⟨j, o, x, hj, hu, hx, rfl⟩ := hI.pre m hm.1
    exact ⟨j, o, hj, hu, rfl, alx hx⟩
  · refine clean_nodup fun m hm m' hm' _ _ he => ?_
    rw [List.mem_reverse] at hm hm'
    obtain ⟨j, o, x, hj, hu, hx, rfl⟩ := hI.pre m hm
    obtain ⟨j', o', x', hj', hu', hx', rfl⟩ := hI.pre m' hm'
    simp only [Loc.reg.injEq] at he
    subst he
    by_cases hjj : j = j'
    · subst hjj; rw [hj] at hj'; cases hj'; rfl
    · have hov : Ov (opRange g o false) (opRange g o' false) := by
        rw [E.ivU hj hu, E.ivU hj' hu']; simp [Ov, pos]
      rcases hI.disj j o j' o' x hj hj' hjj hx hx' hov with ⟨-, -, hv⟩ | hr | hr
      · rw [hv]
      · obtain ⟨hk, -⟩ := E.ok.reuse j o j' (tl hj) hr; rw [hk] at hu; cases hu
      · obtain ⟨hk, -⟩ := E.ok.reuse j' o' j (tl hj') hr; rw [hk] at hu'; cases hu'
  · intro m hm m' hm'
    have hm0 := hm
    rw [mem_clean, List.mem_reverse] at hm
    obtain ⟨j, o, x, hj, hu, hx, rfl⟩ := hI.pre m hm.1
    exact fun he => pre_dst E hI hm' (cov1 E hj hu) he.symm
  · intro j o hj hu
    obtain ⟨x, hx, ha⟩ := getx hj
    have hnp : ∀ m ∈ cleanMoves S.pre.reverse, m.2 ≠ c.loc o.vreg :=
      fun m hm => pre_dst E hI hm (cov1 E hj hu)
    rcases (hI.cat j o x hj hx).use hu with hl | hm
    · exact .inl ⟨by rw [ha, hl], hnp⟩
    · by_cases hl : c.loc o.vreg = .reg x
      · exact .inl ⟨by rw [ha, hl], hnp⟩
      · exact .inr ⟨_, ha, mem_clean.mpr ⟨List.mem_reverse.mpr hm, hl⟩⟩
  · intro m hm
    rw [mem_clean, List.mem_reverse] at hm
    obtain ⟨j, o, x, hj, hd, hs, hx, rfl⟩ := hI.post m hm.1
    exact ⟨j, o, hj, hd, hs, alx hx, rfl⟩
  · refine clean_nodup fun m hm m' hm' _ _ he => ?_
    rw [List.mem_reverse] at hm hm'
    obtain ⟨j, o, x, hj, hd, hs, hx, rfl⟩ := hI.post m hm
    obtain ⟨j', o', x', hj', hd', hs', hx', rfl⟩ := hI.post m' hm'
    have hv := loc_inj E (E.nv o (E.mem hj)) (E.nv o' (E.mem hj')) (E.st j o hs) (E.st j' o' hs') he
    have := E.def_inj hj hj' hd hd' hv; subst this
    rw [hj] at hj'; cases hj'; rw [hx] at hx'; cases hx'; rfl
  · intro m hm m' hm' he
    rw [mem_clean, List.mem_reverse] at hm hm'
    obtain ⟨j, o, x, hj, hd, hs, hx, rfl⟩ := hI.post m hm.1
    obtain ⟨j', o', x', hj', hd', hs', hx', rfl⟩ := hI.post m' hm'.1
    have := owner E hI hj hx (loc_reg.mp he.symm) (iv_def3 hd).1 (iv_def3 hd).2 (cov3 E hj' hd')
    rw [this] at he
    exact hm.2 he
  · intro j o hj hd hs
    obtain ⟨x, hx, ha⟩ := getx hj
    rcases (hI.cat j o x hj hx).dfn hd hs with hl | hm
    · exact .inl ⟨by rw [ha, hl], noPost hj hd hs hx hl⟩
    · by_cases hl : c.loc o.vreg = .reg x
      · exact .inl ⟨by rw [ha, hl], noPost hj hd hs hx hl⟩
      · exact .inr ⟨_, ha, mem_clean.mpr ⟨List.mem_reverse.mpr hm, Ne.symm hl⟩⟩
  · intro v hv hcov hnd
    have c1 := cov_of_covI hcov (by simp [pos]) (by simp [pos] : pos g 1 ≤ pos g 4)
    have c3 := cov_of_covI hcov (by simp [pos]) (by simp [pos] : pos g 3 ≤ pos g 4)
    have c4 := cov_of_covI hcov (by simp [pos]) (Nat.le_refl _)
    refine ⟨fun m hm => pre_dst E hI hm c1, fun j o l hj hd hl he => ?_, fun m hm he => ?_⟩
    · obtain ⟨x, hx, ha⟩ := getx hj
      rw [ha] at hl; cases hl
      have := owner E hI hj hx (loc_reg.mp he.symm) (iv_def3 hd).1 (iv_def3 hd).2 c3
      exact hnd o (E.mem hj) hd this.symm
    · rw [mem_clean, List.mem_reverse] at hm
      obtain ⟨j, o, x, hj, hd, -, hvo, -⟩ := post_dst E hI hm.1 hv c4 he
      exact hnd o (E.mem hj) hd hvo

end

/-- **The builder's instruction step** (module doc). -/
theorem inst_facts {vc : VCode} {fn : Fn} {pl : LinearScan.Plan} (hf : FnOk vc fn)
    (hpf : PlanFacts vc (LinearScan.Ctx.ofPlan fn pl)) {g : Nat} {i : MInst} {os : Array Operand}
    (hi : fn.insts[g]? = some i) (hos : fn.ops[g]? = some os) (hok : OpsOk os i.clobbers)
    (hcls : ∀ o ∈ os.toList, fn.clsOf o.vreg = o.cls) {io : IOut}
    (h : (LinearScan.Ctx.ofPlan fn pl).inst g = .ok io) : InstFacts (LinearScan.Ctx.ofPlan fn pl) g i os io := by
  have E : Env vc (LinearScan.Ctx.ofPlan fn pl) g os i.clobbers
      ((LinearScan.Ctx.ofPlan fn pl).store g i.isTerminator (keptIdx i os)) :=
    { pf := hpf, occ := rfl, hos := hos, ok := hok, cls := hcls, nv := hf.nv_ops g os hos
      clob := hpf.clob g i hi
      st := fun j o h => by simp only [Ctx.store, Bool.and_eq_true] at h; exact h.2 }
  obtain ⟨S, hI, hall, rfl⟩ := inst_run E hi h
  exact facts E hI hall

end Backend.Proof.LS
