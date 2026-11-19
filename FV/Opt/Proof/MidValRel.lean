import FV.Opt.Proof.MidValWalk
import FV.Opt.Proof.MidValFacts
import FV.Opt.Proof.MidValFloat
import FV.Opt.Proof.SemSimMU

/-!
# The simulation relation of the mid-end validator (#1119, module (5), part 3)

`Rel … bi k k' S fr fr' m`: `f`'s frame `fr` is before statement `k` of block `bi`, `g`'s frame
`fr'` before statement `k'` of the same block (both satisfy the run-time invariant `Opt.Inv`),
and the rest of the block walk of `checkCert` from there, with the facts `S`, succeeds and ends
well (`EndOk`). The values: every value of `f` available at `(bi, k)` holds its term's value
(`TV`, atoms read `fr`'s registers), every value of `g` available at `(bi, k')` holds its term's
value too, with a site no later than `(bi, k)` (it is computed from `f`'s values available
now); every fact of `S` holds in `fr` and memory `m` (`FactHolds`), its terms with sites no later
than `(bi, k)`. `MR` (some position) is the frame relation of `FunSimMU`.

Basic facts: the hypotheses `Hyp` give both functions' `Wf` and equal dominator trees;
values and facts whose sites are no later than `(bi, k)` do not change when `f` binds results
that are not available at `(bi, k)` (`TV_stable`, `FactHolds.stable`).
-/

namespace Opt.MidVal

open Clif

section
variable (f : Function) (cert : Cert) (syms : String → Option Nat)

/-- Term values in a frame of `f` (pure nodes read only the link-time symbols). -/
abbrev TV (fr : Frame) (t : Nat) : Option Val := tmVal f cert.tms fr (symMem syms) t

/-- A fact holds in the frame `fr` of `f` and memory `m`. -/
def FactHolds (fr : Frame) (m : Mem) : Fact → Prop
  | .mem a off ty k e v => ∃ av vv, TV f cert syms fr a = some av ∧ TV f cert syms fr v = some vv ∧
      MemHolds m (effAddr av off) ty k (e == some .big) vv
  | .eqn i none =>
    evalInst (tmFrame f cert.tms fr (symMem syms)) (symMem syms) i = .ok ([], symMem syms)
  | .eqn i (some t) => ∃ v, TV f cert syms fr t = some v ∧
    evalInst (tmFrame f cert.tms fr (symMem syms)) (symMem syms) i = .ok ([v], symMem syms)
  | .defd t => (TV f cert syms fr t).isSome

end

/-- The hypotheses of the simulation: both functions pass `Opt.check`, the certificate's facts
(`CertOk`), and a sound normaliser. -/
structure Hyp (f g : Function) (fi gi : Info) (cert : Cert) (norm : Norm) : Prop where
  hf : Opt.check f = .ok fi
  hg : Opt.check g = .ok gi
  ok : CertOk f g fi gi cert norm
  norm : NormSound norm

/-- The relation (module doc). -/
structure Rel (f g : Function) (fi gi : Info) (cert : Cert) (norm : Norm)
    (syms : String → Option Nat) (bi k k' : Nat) (S : List Fact) (fr fr' : Frame) (m : Mem) :
    Prop where
  walk : ∃ fb gb Send, f.blocks[bi]? = some fb ∧ g.blocks[bi]? = some gb ∧
    (ccOf fi gi cert norm).walk bi (fb.body.drop k) (gb.body.drop k') k k' S = some Send ∧
    EndOk (ccOf fi gi cert norm) bi fb gb Send
  invf : Inv f (wfData f fi) syms fr bi k
  invg : Inv g (wfData g gi) syms fr' bi k'
  slots : fr'.slots = fr.slots
  agreeF : ∀ x, Avail (wfData f fi) bi k x →
    TV f cert syms fr ((ccOf fi gi cert norm).ef x) = fr.regs x
  agreeG : ∀ y, Avail (wfData g gi) bi k' y →
    TV f cert syms fr ((ccOf fi gi cert norm).eg y) = fr'.regs y
  sitesG : ∀ y, Avail (wfData g gi) bi k' y →
    LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf ((ccOf fi gi cert norm).eg y)) (bi, k)
  facts : ∀ F ∈ S, FactHolds f cert syms fr m F
  factSites : ∀ F ∈ S, ∀ t ∈ F.terms, LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf t) (bi, k)

/-- The frame relation of `FunSimMU`: some position. -/
def MR (f g : Function) (fi gi : Info) (cert : Cert) (norm : Norm) (syms : String → Option Nat)
    (fr fr' : Frame) (m : Mem) : Prop :=
  ∃ bi k k' S, Rel f g fi gi cert norm syms bi k k' S fr fr' m

namespace Hyp

variable {f g : Function} {fi gi : Info} {cert : Cert} {norm : Norm}

theorem wff (H : Hyp f g fi gi cert norm) : Wf f (wfData f fi) := wf_of_check H.hf
theorem wfg (H : Hyp f g fi gi cert norm) : Wf g (wfData g gi) := wf_of_check H.hg

theorem idomF (_H : Hyp f g fi gi cert norm) : (wfData f fi).idom = fi.cfg.idom := rfl
theorem idomG (H : Hyp f g fi gi cert norm) : (wfData g gi).idom = fi.cfg.idom := H.ok.idom
theorem idomC (_H : Hyp f g fi gi cert norm) : (ccOf fi gi cert norm).idom = fi.cfg.idom := rfl

/-- The rank of `f`'s tree orders `g`'s tree too (they are equal). -/
theorem rankF (H : Hyp f g fi gi cert norm) :
    ∀ b c, fi.cfg.idom[b]?.join = some c → (wfData f fi).rank c < (wfData f fi).rank b :=
  H.wff.rank

theorem le_sound (H : Hyp f g fi gi cert norm) {a b : Nat × Nat}
    (h : (ccOf fi gi cert norm).le a b = true) : LeP fi.cfg.idom a b :=
  CC.le_sound h

theorem leP_trans (H : Hyp f g fi gi cert norm) {a b c : Nat × Nat} (h1 : LeP fi.cfg.idom a b)
    (h2 : LeP fi.cfg.idom b c) : LeP fi.cfg.idom a c :=
  h1.trans H.rankF h2

/-- The term of a value of `f` available at `(i, k)` has a site no later than `(i, k)`. -/
theorem siteF (H : Hyp f g fi gi cert norm) {i k : Nat} {x : ValueId}
    (hx : Avail (wfData f fi) i k x) :
    LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf ((ccOf fi gi cert norm).ef x)) (i, k) := by
  obtain ⟨s, hs, hle⟩ := leP_of_avail hx
  have hd := H.wff.sitesRev x s hs
  exact H.leP_trans (H.le_sound (H.ok.sitesF x s hd)) hle

/-- Stability of term values (`tmVal_congr` for the certificate's table). -/
theorem TV_stable (H : Hyp f g fi gi cert norm) {syms : String → Option Nat} {fr1 fr2 : Frame}
    (hg : fr2.func.globals = fr1.func.globals) (hx : fr2.func.externs = fr1.func.externs)
    (hs : fr2.slots = fr1.slots) {i k : Nat}
    (hr : ∀ v, Avail (wfData f fi) i k v → fr2.regs v = fr1.regs v) {t : Nat}
    (ht : LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf t) (i, k)) :
    TV f cert syms fr2 t = TV f cert syms fr1 t :=
  tmVal_congr H.wff (c := ccOf fi gi cert norm) rfl H.ok.tms hg hx hs hr t ht

end Hyp

/-- Facts whose terms have sites no later than `(i, k)` keep holding in a frame that agrees on
the values available there; memory facts in the same memory, the others in any. -/
theorem FactHolds.stable {f g : Function} {fi gi : Info} {cert : Cert} {norm : Norm}
    (H : Hyp f g fi gi cert norm) {syms : String → Option Nat} {fr1 fr2 : Frame} {m1 m2 : Mem}
    (hg : fr2.func.globals = fr1.func.globals) (hx : fr2.func.externs = fr1.func.externs)
    (hs : fr2.slots = fr1.slots) {i k : Nat}
    (hr : ∀ v, Avail (wfData f fi) i k v → fr2.regs v = fr1.regs v) {F : Fact}
    (hF : ∀ t ∈ F.terms, LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf t) (i, k))
    (hm : F.isMem = true → m2 = m1) (h : FactHolds f cert syms fr1 m1 F) :
    FactHolds f cert syms fr2 m2 F := by
  have hTV : ∀ t ∈ F.terms, TV f cert syms fr2 t = TV f cert syms fr1 t :=
    fun t ht => H.TV_stable hg hx hs hr (hF t ht)
  -- the term frames agree on the operands of an `eqn` fact
  have hfr : ∀ (i' : Inst), (∀ o ∈ operands i', o ∈ F.terms) →
      evalInst (tmFrame f cert.tms fr2 (symMem syms)) (symMem syms) i' =
        evalInst (tmFrame f cert.tms fr1 (symMem syms)) (symMem syms) i' := by
    intro i' hops
    exact evalInst_congr (by simp [tmFrame, hg]) (by simp [tmFrame, hx]) (by simp [tmFrame, hs])
      fun o ho => by simp only [tmFrame]; exact hTV o (hops o ho)
  cases F with
  | mem a off ty kd e v =>
    obtain ⟨av, vv, ha, hv, hh⟩ := h
    rw [hm rfl]
    exact ⟨av, vv, by rw [hTV a (by simp [Fact.terms]), ha], by rw [hTV v (by simp [Fact.terms]), hv], hh⟩
  | eqn i' r =>
    cases r with
    | none =>
      simp only [FactHolds] at h ⊢
      rw [hfr i' (fun o ho => by simp [Fact.terms, ho])]
      exact h
    | some t =>
      obtain ⟨v, hv, he⟩ := h
      refine ⟨v, by rw [hTV t (by simp [Fact.terms]), hv], ?_⟩
      rw [hfr i' (fun o ho => by simp [Fact.terms, ho])]
      exact he
  | defd t =>
    simp only [FactHolds] at h ⊢
    rw [hTV t (by simp [Fact.terms])]
    exact h

end Opt.MidVal
