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

@[simp] theorem ctxOf_σ (σ : ValueId → ValueId) (g : Function) (D : WfData) (i : Nat) :
    (ctxOf σ g D i).σ = σ := rfl

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
  slots : fr'.slots = fr.slots

theorem not_call_of_removable {i : Inst} (h : removable i = true) : ∀ fn args, i ≠ .call fn args := by
  intro fn args he; rw [he] at h; cases h

theorem mapOperands_not_call {σ : ValueId → ValueId} {i : Inst} (h : ∀ fn args, i ≠ .call fn args) :
    ∀ fn args, mapOperands σ i ≠ .call fn args := by
  intro fn args he
  cases i <;> simp [mapOperands] at he
  exact h _ _ rfl

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
  refine ⟨{ fr' with regs := fr'.regs.set u a, body := ts }, ?_, ⟨h.invf, ?_, ?_, ?_, h.slots⟩, rfl⟩
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

theorem ERel.alignNow {fr fr' bi k k'} (h : ERel σ f g Df Dg syms fr fr' bi k k') :
    (ctxOf σ g Dg bi).align fr.body fr'.body k' = true := by
  obtain ⟨b, b', hb, hb', h1, h2, -⟩ := h.blocks hE
  rw [h1, h2]; exact h.align b b' hb hb'

/-- Where the alignment stands once the target has executed its inserted statements. -/
def Settled (c : EditCtx) (ss ts : List Stmt) (k' : Nat) : Prop :=
  (ss = [] ∧ ts = []) ∨
  (∃ s ss' t ts', ss = s :: ss' ∧ ts = t :: ts' ∧ c.keepOk s t = true ∧
    c.align ss' ts' (k' + 1) = true) ∨
  (∃ s ss', ss = s :: ss' ∧ c.delOk s k' = true ∧ c.align ss' ts k' = true)

/-- The target executes its inserted statements. -/
theorem ERel.catchUp {fr fr' bi k k' m} (h : ERel σ f g Df Dg syms fr fr' bi k k')
    (hm : m.symbols = syms) :
    ∃ fr'' k'', LStar fr' m fr'' m ∧ ERel σ f g Df Dg syms fr fr'' bi k k'' ∧
      Settled (ctxOf σ g Dg bi) fr.body fr''.body k'' := by
  generalize hn : fr'.body.length = n
  induction n using Nat.strongRecOn generalizing fr' k' with
  | _ n ih =>
    have hal := h.alignNow hE
    cases hs : fr.body with
    | nil =>
      cases ht : fr'.body with
      | nil => exact ⟨fr', k', .refl _ _, h, by rw [ht]; exact .inl ⟨rfl, rfl⟩⟩
      | cons t ts =>
        rw [hs, ht, EditCtx.align.eq_2, Bool.and_eq_true] at hal
        obtain ⟨fr1, hl, h1, hb1⟩ := h.insert hE hm ht hal.1 (by rw [hs]; exact hal.2)
        obtain ⟨fr2, k2, hst, h2, hset⟩ := ih ts.length (by rw [← hn, ht]; simp) h1 (by rw [hb1])
        exact ⟨fr2, k2, .step hl hst, h2, by rw [hs] at hset; exact hset⟩
    | cons s ss =>
      cases ht : fr'.body with
      | nil =>
        rw [hs, ht, EditCtx.align.eq_3, Bool.and_eq_true] at hal
        exact ⟨fr', k', .refl _ _, h, by rw [ht]; exact .inr (.inr ⟨s, ss, rfl, hal.1, hal.2⟩)⟩
      | cons t ts =>
        rw [hs, ht, EditCtx.align.eq_4] at hal
        split at hal
        · exact ⟨fr', k', .refl _ _, h, by rw [ht]; exact .inr (.inl ⟨s, ss, t, ts, rfl, rfl, ‹_›, hal⟩)⟩
        · split at hal
          · exact ⟨fr', k', .refl _ _, h, by rw [ht]; exact .inr (.inr ⟨s, ss, rfl, ‹_›, hal⟩)⟩
          · rw [Bool.and_eq_true] at hal
            obtain ⟨fr1, hl, h1, hb1⟩ := h.insert hE hm ht hal.1 (by rw [hs]; exact hal.2)
            obtain ⟨fr2, k2, hst, h2, hset⟩ :=
              ih ts.length (by rw [← hn, ht]; simp) h1 (by rw [hb1])
            exact ⟨fr2, k2, .step hl hst, h2, by rw [hs] at hset; exact hset⟩

theorem ERel.globals {fr fr' bi k k'} (h : ERel σ f g Df Dg syms fr fr' bi k k') :
    fr'.func.globals = fr.func.globals := by
  rw [h.invf.func, h.invg.func, hE.globals]

/-- The results of a statement bound in both frames keep the agreement. -/
theorem agree_results {fr fr' bi k k' b b' s rs vals regs regs'}
    (h : EAgree σ Df Dg fr fr' bi k k') (hb : f.blocks[bi]? = some b)
    (hb' : g.blocks[bi]? = some b') (hs : b.body[k]? = some s)
    (ht : b'.body[k']? = some { results := s.results, inst := rs })
    (hσ : ∀ r ∈ s.results, σ r = r)
    (h1 : fr.regs.setMany s.results vals = some regs)
    (h2 : fr'.regs.setMany s.results vals = some regs') :
    EAgree σ Df Dg { fr with regs } { fr' with regs := regs' } bi (k + 1) (k' + 1) := by
  intro v hv hrep
  rcases avail_succ hE.wff hb hs hv with hr | hv'
  · rw [hσ v hr]
    refine ⟨⟨bi, k' + 1, site_result hE.wfg hb' ht hr, .inl ⟨rfl, Nat.le_refl _⟩⟩, ?_⟩
    exact (setMany_same h1 h2 v hr).symm
  · have hnr := avail_not_result hE.wff hb hs hv'
    obtain ⟨hav, heq⟩ := h v hv' hrep
    have hnr' := avail_not_result hE.wfg hb' ht hav
    refine ⟨hav.mono (by omega), ?_⟩
    simp only
    rw [((setMany_spec h2).2 _).1 hnr', ((setMany_spec h1).2 _).1 hnr, heq]

/-- A kept statement (not a call) steps in lock-step. -/
theorem ERel.keep {fr fr' bi k k' m s ss t ts} (h : ERel σ f g Df Dg syms fr fr' bi k k')
    (hm : m.symbols = syms) (hs : fr.body = s :: ss) (ht : fr'.body = t :: ts)
    (hk : (ctxOf σ g Dg bi).keepOk s t = true) (hal : (ctxOf σ g Dg bi).align ss ts (k' + 1) = true)
    (hnc : ∀ fn args, s.inst ≠ .call fn args) :
    (∀ fr1 m1, lstep fr m = .next fr1 m1 → ∃ fr1', lstep fr' m = .next fr1' m1 ∧
      ERel σ f g Df Dg syms fr1 fr1' bi (k + 1) (k' + 1)) ∧
    (∀ c, lstep fr m = .trap c → lstep fr' m = .trap c) := by
  obtain ⟨rfl, hσ⟩ := keepOk_spec hk
  simp only [ctxOf_σ] at hσ ht ⊢
  have hops := h.ops hE hs ht
  have hev := evalInst_rename (mem := m) (h.globals hE) h.slots hops
  obtain ⟨b, b', hb, hb', h1, h2, -⟩ := h.blocks hE
  have hs0 := hs; have ht0 := ht
  rw [h1] at hs; rw [h2] at ht
  obtain ⟨hsk, hss, -⟩ := drop_eq_cons hs
  obtain ⟨htk, hts, -⟩ := drop_eq_cons ht
  have hnc' := mapOperands_not_call (σ := σ) hnc
  rw [lstep_inst hs0 hnc, lstep_inst ht0 hnc']
  refine ⟨fun fr1 m1 hl => ?_, fun c hl => ?_⟩
  · cases he : evalInst fr m s.inst with
    | trap c => rw [he] at hl; cases hl
    | stuck msg => rw [he] at hl; cases hl
    | ok p =>
      obtain ⟨vals, m1'⟩ := p
      rw [he] at hl
      simp only [LRes.ofRes] at hl
      split at hl
      · rename_i regs hset
        cases hl
        have he' := Res.norm_eq_ok hev he
        obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := s.results) (vs := vals)
          (setMany_spec hset).1
        simp only [renStmt] at he' ⊢
        rw [he']
        simp only [LRes.ofRes, hset']
        refine ⟨_, rfl, ⟨?_, ?_, ?_, ?_, h.slots⟩⟩
        · exact Inv.results hE.wff h.invf hs0 (fun ts0 h0 => evalInst_types he h0)
            (fun hp => by
              obtain ⟨-, a, rfl, ha⟩ := evalInst_pure hp he
              exact ⟨a, rfl, by rw [evalNode_mem (m := m) hp (by rw [hm]; rfl)]; exact ha⟩) hset
        · refine Inv.results hE.wfg h.invg ht0 (fun ts0 h0 => evalInst_types he' h0)
            (fun hp => ?_) hset'
          obtain ⟨-, a, rfl, ha⟩ := evalInst_pure hp he'
          exact ⟨a, rfl, by rw [evalNode_mem (m := m) hp (by rw [hm]; rfl)]; exact ha⟩
        · exact agree_results hE h.agree hb hb' hsk htk hσ hset hset'
        · intro b0 b0' hb0 hb0'
          rw [hb] at hb0; cases hb0
          rw [hb'] at hb0'; cases hb0'
          rw [hss, hts]; exact hal
      · cases hl
  · cases he : evalInst fr m s.inst with
    | ok p => rw [he] at hl; obtain ⟨_, _⟩ := p; simp only [LRes.ofRes] at hl; split at hl <;> cases hl
    | stuck msg => rw [he] at hl; cases hl
    | trap c' =>
      rw [he] at hl; cases hl
      simp only [renStmt]
      rw [Res.norm_eq_trap hev he]; rfl

/-- A deleted statement: the source steps alone. -/
theorem ERel.delete {fr fr' bi k k' m s ss} (h : ERel σ f g Df Dg syms fr fr' bi k k')
    (hm : m.symbols = syms) (hs : fr.body = s :: ss) (hd : (ctxOf σ g Dg bi).delOk s k' = true)
    (hal : (ctxOf σ g Dg bi).align ss fr'.body k' = true) :
    (∀ fr1 m1, lstep fr m = .next fr1 m1 → m1 = m ∧
      ERel σ f g Df Dg syms fr1 fr' bi (k + 1) k') ∧
    (∀ c, lstep fr m ≠ .trap c) ∧ (∀ e vs rs rest, lstep fr m ≠ .call e vs rs rest) := by
  have hrem : removable s.inst = true := by
    rcases delOk_spec hd with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · simp [removable, h1]
  have hnc := not_call_of_removable hrem
  obtain ⟨b, b', hb, hb', h1, h2, -⟩ := h.blocks hE
  have hs0 := hs
  rw [h1] at hs
  obtain ⟨hsk, hss, -⟩ := drop_eq_cons hs
  rw [lstep_inst hs0 hnc]
  obtain ⟨hmem, hnt⟩ := evalInst_removable (fr := fr) (mem := m) hrem
  refine ⟨fun fr1 m1 hl => ?_, fun c hl => ?_, fun e vs rs rest hl => ?_⟩
  · cases he : evalInst fr m s.inst with
    | trap c => rw [he] at hl; cases hl
    | stuck msg => rw [he] at hl; cases hl
    | ok p =>
      obtain ⟨vals, m1'⟩ := p
      rw [he] at hl
      simp only [LRes.ofRes] at hl
      split at hl
      · rename_i regs hset
        cases hl
        refine ⟨hmem _ _ he, ⟨?_, h.invg, ?_, ?_, h.slots⟩⟩
        · exact Inv.results hE.wff h.invf hs0 (fun ts0 h0 => evalInst_types he h0)
            (fun hp => by
              obtain ⟨-, a, rfl, ha⟩ := evalInst_pure hp he
              exact ⟨a, rfl, by rw [evalNode_mem (m := m) hp (by rw [hm]; rfl)]; exact ha⟩) hset
        · intro v hv hrep
          rcases avail_succ hE.wff hb hsk hv with hr | hv'
          · rcases delOk_spec hd with ⟨-, hnone⟩ | ⟨hp, v0, hv0, hav, hpd⟩
            · rw [hnone v hr] at hrep; cases hrep
            · rw [hv0] at hr
              simp only [List.mem_singleton] at hr
              subst hr
              have hav' := availB_sound (W := Dg) hav
              refine ⟨hav', ?_⟩
              obtain ⟨-, a, rfl, ha⟩ := evalInst_pure hp he
              have hrv : regs v = some a := by
                rw [hv0] at hset
                simp only [Regs.setMany_cons, Regs.setMany_nil, Option.some.injEq] at hset
                subst hset; simp
              simp only
              rw [hrv, h.invg.pure _ _ hav' hpd, evalNode_rename (h.globals hE) h.slots ?_,
                evalNode_mem (m := m) hp (by rw [hm]; rfl), ha]
              intro x hx
              have hxf := hE.wff.uses bi b hb k s hsk x hx
              obtain ⟨d, j, b3, st, hd, hb3, hst, hr3, hn, _⟩ := hpd
              have hxg := hE.wfg.uses d b3 hb3 j st hst (σ x) (by
                rw [hn, operands_mapOperands]; exact List.mem_map_of_mem hx)
              exact (h.agree x hxf (avail_isSome hxg)).2
          · have hnr := avail_not_result hE.wff hb hsk hv'
            obtain ⟨hav, heq⟩ := h.agree v hv' hrep
            refine ⟨hav, ?_⟩
            simp only
            rw [((setMany_spec hset).2 _).1 hnr, heq]
        · intro b0 b0' hb0 hb0'
          rw [hb] at hb0; cases hb0
          rw [hb'] at hb0'; cases hb0'
          rw [hss, ← h2]; exact hal
      · cases hl
  · cases he : evalInst fr m s.inst with
    | ok p => rw [he] at hl; obtain ⟨_, _⟩ := p; simp only [LRes.ofRes] at hl; split at hl <;> cases hl
    | stuck msg => rw [he] at hl; cases hl
    | trap c' => exact hnt c' he
  · cases he : evalInst fr m s.inst with
    | ok p => rw [he] at hl; obtain ⟨_, _⟩ := p; simp only [LRes.ofRes] at hl; split at hl <;> cases hl
    | stuck msg => rw [he] at hl; cases hl
    | trap c' => rw [he] at hl; cases hl

end

end Opt
