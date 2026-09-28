import FV.Opt.Proof.DomInv
import FV.Opt.Validate

/-!
# The edit validator is sound: `editOk σ f g` ⇒ `g` simulates `f` (`Opt.editOk_sim`)

Used for GVN, DCE and LICM (`FV/Opt/Proof/Pipeline.lean`). Source and target frames are related
at corresponding positions of the same block (`Opt.ERel`): both satisfy the run-time invariant
`Opt.Inv` of their function, the rest of the bodies align (`EditCtx.align`), and every value
available in the source whose renaming `σ v` is defined in the target is available there and
holds the same value (`Opt.EAgree`).

Kept statements and terminators step in lock-step (renamed operands read the same values);
deleted statements are source-only steps (removable ones define only values the target never
defines; a pure `v = n` renamed to `σ v` finds, by the target's invariant, `σ v = σ n`, the
value of `n`); inserted statements are target-only steps that cannot fail (lemma (T)).
-/

namespace Opt

open Clif

/-- The alignment context of block `i`. -/
def ctxOf (σ : ValueId → ValueId) (g : Function) (Dg : WfData) (i : Nat) : EditCtx :=
  { σ, gdm := Dg.dm, gidom := Dg.idom, gblocks := g.blocks.toArray, bi := i }

/-- The facts of `editOk`. -/
structure EditFacts (σ : ValueId → ValueId) (f g : Function) (Df Dg : WfData) : Prop where
  wff : Wf f Df
  wfg : Wf g Dg
  name : g.name = f.name
  sig : g.sig = f.sig
  slots : g.slots = f.slots
  globals : g.globals = f.globals
  externs : g.externs = f.externs
  idom : Dg.idom = Df.idom
  len : g.blocks.length = f.blocks.length
  blocks : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → ∃ b' : Block, g.blocks[i]? = some b' ∧
    b'.id = b.id ∧ b'.params = b.params ∧ (∀ p ∈ b.params, σ p.1 = p.1) ∧
    b'.term = mapTerm σ b.term ∧ (ctxOf σ g Dg i).align b.body b'.body 0 = true
  subst : ∀ v d t, Df.dm v = some (d, t) → ∀ d' t', Dg.dm (σ v) = some (d', t') →
    Anc Df.idom d' d

theorem editOk_facts {σ : ValueId → ValueId} {f g : Function} {fi gi : Info}
    (hf : check f = .ok fi) (hg : check g = .ok gi) (h : editOk σ f g fi gi = true) :
    EditFacts σ f g (wfData f fi) (wfData g gi) := by
  simp only [editOk, sameHeader, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hn, hs⟩, hsl⟩, hgl⟩, hex⟩, hid⟩, hlen⟩, hbl⟩, hsub⟩ := h
  refine ⟨wf_of_check hf, wf_of_check hg, hn, hs, hsl, hgl, hex, hid, hlen, ?_, ?_⟩
  · intro i b hb
    have hi : i < g.blocks.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hb).1
    refine ⟨g.blocks[i], by simp [hi], ?_⟩
    have hz : ((b, g.blocks[i]), i) ∈ (f.blocks.zip g.blocks).zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?]
      simp [List.getElem?_zip_eq_some, hb, hi]
    have := hbl _ hz
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := this
    exact ⟨h1, h2, fun p hp => by simpa using h3 p hp, h4, h5⟩
  · intro v d t hv d' t' hv'
    have hm : (v, (d, t)) ∈ (defMap f).toList := by
      rw [Std.HashMap.mem_toList_iff_getElem?_eq_some]
      simpa [wfData, Std.HashMap.get?_eq_getElem?] using hv
    have := hsub _ hm
    simp only [wfData] at hv'
    simp only [hv'] at this
    have := ancB_sound this
    rw [hid] at this
    simpa [wfData] using this

/-! ## Spec of the alignment checks -/

theorem keepOk_spec {c : EditCtx} {s t : Stmt} (h : c.keepOk s t = true) :
    t = renStmt c.σ s ∧ ∀ r ∈ s.results, c.σ r = r := by
  simp only [EditCtx.keepOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1, h.2⟩

theorem pureAt_spec {σ g Dg i} {w : ValueId} {n : Inst} (h : (ctxOf σ g Dg i).pureAt w n = true) :
    PureDef g Dg w n := by
  simp only [EditCtx.pureAt, ctxOf] at h
  split at h
  · rename_i d j hd
    simp only [List.getElem?_toArray] at h
    split at h
    · rename_i b hb
      split at h
      · rename_i st hst
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        exact ⟨d, j, b, st, hd, hb, hst, h.1.1, h.1.2, h.2⟩
      · cases h
    · cases h
  · cases h

/-- What deleting a statement requires. -/
theorem delOk_spec {σ g Dg i} {s : Stmt} {k' : Nat} (h : (ctxOf σ g Dg i).delOk s k' = true) :
    (removable s.inst = true ∧ ∀ r ∈ s.results, Dg.dm (σ r) = none) ∨
      (isPure s.inst = true ∧ ∃ v, s.results = [v] ∧
        availB Dg.dm (ancB Dg.idom Dg.idom.size) i k' (σ v) = true ∧
        PureDef g Dg (σ v) (mapOperands σ s.inst)) := by
  simp only [EditCtx.delOk, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true,
    Option.isNone_iff_eq_none] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact .inl ⟨h1, h2⟩
  · refine .inr ⟨h1, ?_⟩
    split at h2
    · rename_i v hv
      simp only [Bool.and_eq_true] at h2
      exact ⟨v, hv, h2.1, pureAt_spec h2.2⟩
    · cases h2

theorem insOk_spec {t : Stmt} (h : insOk t = true) :
    isPure t.inst = true ∧ ∃ u, t.results = [u] ∧ ∀ ty gv, t.inst ≠ .symbolValue ty gv := by
  simp only [insOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, ?_⟩
  match hr : t.results, h2 with
  | [u], _ =>
    refine ⟨u, rfl, fun ty gv he => ?_⟩
    rw [he] at h3; cases h3

theorem termOperands_mapTerm (σ : ValueId → ValueId) (t : Terminator) :
    termOperands (mapTerm σ t) = (termOperands t).map σ := by
  cases t <;> simp [termOperands, mapTerm, mapBlockCall, List.map_flatMap, List.flatMap_map]

theorem termSuccs_mapTerm (σ : ValueId → ValueId) (t : Terminator) :
    termSuccs (mapTerm σ t) = termSuccs t := by
  cases t <;> simp [termSuccs, mapTerm, mapBlockCall]

/-! ## The relation -/

/-- Source values available at `(bi, k)` whose renaming is defined in the target are available at
the target position `(bi, k')` and hold the same value. -/
def EAgree (σ : ValueId → ValueId) (Df Dg : WfData) (fr fr' : Frame) (bi k k' : Nat) : Prop :=
  ∀ v, Avail Df bi k v → (Dg.dm (σ v)).isSome → Avail Dg bi k' (σ v) ∧ fr'.regs (σ v) = fr.regs v

/-- Frames at corresponding positions `k`/`k'` of block `bi`. -/
structure ERel (σ : ValueId → ValueId) (f g : Function) (Df Dg : WfData)
    (syms : String → Option Nat) (fr fr' : Frame) (bi k k' : Nat) : Prop where
  invf : Inv f Df syms fr bi k
  invg : Inv g Dg syms fr' bi k'
  agree : EAgree σ Df Dg fr fr' bi k k'
  align : ∀ b b', f.blocks[bi]? = some b → g.blocks[bi]? = some b' →
    (ctxOf σ g Dg bi).align (b.body.drop k) (b'.body.drop k') k' = true

theorem avail_isSome {D : WfData} {i k v} (h : Avail D i k v) : (D.dm v).isSome := by
  obtain ⟨d, t, hd, _⟩ := h
  simp [hd]

section
variable {σ : ValueId → ValueId} {f g : Function} {Df Dg : WfData} (hE : EditFacts σ f g Df Dg)
  {syms : String → Option Nat}
include hE

theorem ERel.blocks {fr fr' bi k k'} (h : ERel σ f g Df Dg syms fr fr' bi k k') :
    ∃ b b', f.blocks[bi]? = some b ∧ g.blocks[bi]? = some b' ∧ fr.body = b.body.drop k ∧
      fr'.body = b'.body.drop k' ∧ fr.term = b.term ∧ fr'.term = mapTerm σ b.term ∧
      b'.id = b.id ∧ b'.params = b.params := by
  obtain ⟨b, hb, h1, h2, _⟩ := h.invf.block
  obtain ⟨b', hb', h3, h4, _⟩ := h.invg.block
  obtain ⟨b'', hb'', hid, hpar, _, hterm, _⟩ := hE.blocks bi b hb
  rw [hb'] at hb''; cases hb''
  exact ⟨b, b', hb, hb', h1, h3, h2, by rw [h4, hterm], hid, hpar⟩

/-- Operands of a kept statement read the same values. -/
theorem ERel.ops {fr fr' bi k k' s ss ts} (h : ERel σ f g Df Dg syms fr fr' bi k k')
    (hs : fr.body = s :: ss) (ht : fr'.body = renStmt σ s :: ts) :
    ∀ x ∈ operands s.inst, fr'.regs (σ x) = fr.regs x := by
  intro x hx
  obtain ⟨b, b', hb, hb', h1, h2, -⟩ := h.blocks hE
  rw [h1] at hs; rw [h2] at ht
  obtain ⟨hsk, -, -⟩ := drop_eq_cons hs
  obtain ⟨htk, -, -⟩ := drop_eq_cons ht
  have hxf := hE.wff.uses bi b hb k s hsk x hx
  have hxg := hE.wfg.uses bi b' hb' k' _ htk (σ x) (by
    simp only [renStmt, operands_mapOperands]; exact List.mem_map_of_mem hx)
  exact (h.agree x hxf (avail_isSome hxg)).2

/-- Operands of the terminator read the same values. -/
theorem ERel.termOps {fr fr' bi k k'} (h : ERel σ f g Df Dg syms fr fr' bi k k')
    (hs : fr.body = []) (ht : fr'.body = []) :
    ∀ x ∈ termOperands fr.term, fr'.regs (σ x) = fr.regs x := by
  intro x hx
  obtain ⟨b, b', hb, hb', h1, h2, h3, h4, -⟩ := h.blocks hE
  have hk : k = b.body.length := by
    have := h.invf.block
    obtain ⟨b2, hb2, _, _, hk⟩ := this
    rw [hb] at hb2; cases hb2
    rw [h1] at hs
    have := congrArg List.length hs; simp at this; omega
  have hk' : k' = b'.body.length := by
    obtain ⟨b2, hb2, _, _, hk⟩ := h.invg.block
    rw [hb'] at hb2; cases hb2
    rw [h2] at ht
    have := congrArg List.length ht; simp at this; omega
  rw [h3] at hx
  have hxf := hE.wff.termUses bi b hb x hx
  obtain ⟨b'', hb'', -, -, -, hterm, -⟩ := hE.blocks bi b hb
  rw [hb'] at hb''; cases hb''
  have hxg := hE.wfg.termUses bi b' hb' (σ x) (by
    rw [hterm, termOperands_mapTerm]; exact List.mem_map_of_mem hx)
  subst hk hk'
  exact (h.agree x hxf (avail_isSome hxg)).2

/-- An inserted statement: the target steps alone. -/
theorem ERel.insert {fr fr' bi k k' m t ts} (h : ERel σ f g Df Dg syms fr fr' bi k k')
    (hm : m.symbols = syms) (ht : fr'.body = t :: ts) (hins : insOk t = true)
    (hal : (ctxOf σ g Dg bi).align (fr.body) ts (k' + 1) = true) :
    ∃ fr'', lstep fr' m = .next fr'' m ∧ ERel σ f g Df Dg syms fr fr'' bi k (k' + 1) ∧
      fr''.body = ts := by
  obtain ⟨b, b', hb, hb', h1, h2, -⟩ := h.blocks hE
  rw [h2] at ht
  obtain ⟨htk, hts, -⟩ := drop_eq_cons ht
  obtain ⟨hp, u, hu, hns⟩ := insOk_spec hins
  have hnc : ∀ fn args, t.inst ≠ .call fn args := by
    intro fn args he; rw [he] at hp; cases hp
  obtain ⟨a, ha⟩ := evalInst_total (f := g) (tm := Dg.tm) (fr := fr') (mem := m) hp
    (hE.wfg.pure bi b' hb' k' t htk hp) (by rw [h.invg.func])
    (fun x hx => h.invg.regs x (hE.wfg.uses bi b' hb' k' t htk x hx)) h.invg.slots
    (fun ty gv _ _ _ he => absurd he (hns ty gv))
  have hset : fr'.regs.setMany t.results [a] = some (fr'.regs.set u a) := by
    rw [hu]; rfl
  refine ⟨{ fr' with regs := fr'.regs.set u a, body := ts }, ?_, ⟨h.invf, ?_, ?_, ?_⟩, rfl⟩
  · rw [lstep_inst (h2.trans ht) hnc]
    simp only [ha, LRes.ofRes, hset]
  · refine Inv.results hE.wfg h.invg (h2.trans ht) (fun ts0 h0 => evalInst_types ha h0)
      (fun _ => ⟨a, rfl, ?_⟩) hset
    rw [evalNode_mem (m := m) hp (by rw [hm]; rfl)]
    obtain ⟨-, v, hv, hev⟩ := evalInst_pure hp ha
    simp only [List.cons.injEq, and_true] at hv
    rw [hv]; exact hev
  · intro v hv hrep
    obtain ⟨hav, heq⟩ := h.agree v hv hrep
    have hnr := avail_not_result hE.wfg hb' htk hav
    rw [hu] at hnr
    refine ⟨hav.mono (by omega), ?_⟩
    simp only [List.mem_singleton] at hnr
    simp only [Regs.set_other _ _ hnr, heq]
  · intro b0 b0' hb0 hb0'
    rw [hb] at hb0; cases hb0
    rw [hb'] at hb0'; cases hb0'
    rw [← h1, hts]; exact hal

end

end Opt
