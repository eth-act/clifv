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

theorem callArgs_rename {σ : ValueId → ValueId} {fr fr' : Frame} {fn : FnRef} {args : List ValueId}
    (hext : fr'.func.externs = fr.func.externs) (h : ∀ x ∈ args, fr'.regs (σ x) = fr.regs x) :
    (callArgs fr' fn (args.map σ)).norm = (callArgs fr fn args).norm := by
  simp only [callArgs, Function.extern?, hext, Res.norm_bind, Res.norm_ofOption, checkTys,
    Res.norm_check, Res.norm_pure, getMany_rename h]

theorem tailArgs_rename {σ : ValueId → ValueId} {fr fr' : Frame} {fn : FnRef} {args : List ValueId}
    (hext : fr'.func.externs = fr.func.externs) (hsig : fr'.func.sig = fr.func.sig)
    (h : ∀ x ∈ args, fr'.regs (σ x) = fr.regs x) :
    (tailArgs fr' fn (args.map σ)).norm = (tailArgs fr fn args).norm := by
  simp only [tailArgs, Function.extern?, hext, hsig, Res.norm_bind, Res.norm_ofOption, checkTys,
    Res.norm_check, Res.norm_pure, getMany_rename h]

theorem enterBlock_of {fr : Frame} {bc : BlockCall} {b : Block} {args : List Val} {regs : Regs}
    (hb : fr.func.block? bc.block = some b) (ha : fr.getMany bc.args = .ok args)
    (ht : args.map (·.ty) = b.params.map (·.2))
    (hr : fr.regs.setMany (b.params.map (·.1)) args = some regs) :
    enterBlock fr bc = .ok { fr with regs, body := b.body, term := b.term } := by
  simp only [enterBlock, hb, ha, checkTys, ht, hr, Res.ofOption_some, Res.ok_bind,
    beq_self_eq_true, Res.check_true]
  rfl

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

/-- The frame relation of the edit simulation. -/
def ER (σ : ValueId → ValueId) (f g : Function) (Df Dg : WfData) (syms : String → Option Nat)
    (fr fr' : Frame) : Prop :=
  ∃ bi k k', ERel σ f g Df Dg syms fr fr' bi k k'

/-- A kept call: same callee and arguments; the continuations are related. -/
theorem ERel.call {fr fr' bi k k' m s ss t ts ext vals rs rest}
    (h : ERel σ f g Df Dg syms fr fr' bi k k')
    (hm : m.symbols = syms) (hs : fr.body = s :: ss) (ht : fr'.body = t :: ts)
    (hk : (ctxOf σ g Dg bi).keepOk s t = true) (hal : (ctxOf σ g Dg bi).align ss ts (k' + 1) = true)
    (hl : lstep fr m = .call ext vals rs rest) :
    lstep fr' m = .call ext vals rs ts ∧ rest = ss ∧
      Cont (ER σ f g Df Dg syms) { fr with body := rest } rs { fr' with body := ts } rs
        (AbiParam.tys ext.sig.returns) := by
  obtain ⟨rfl, hσ⟩ := keepOk_spec hk
  simp only [ctxOf_σ] at hσ ht ⊢
  obtain ⟨b, b', hb, hb', h1, h2, -⟩ := h.blocks hE
  have hs0 := hs; have ht0 := ht
  rw [h1] at hs; rw [h2] at ht
  obtain ⟨hsk, hss, -⟩ := drop_eq_cons hs
  obtain ⟨htk, hts, -⟩ := drop_eq_cons ht
  obtain ⟨st, fn, args, hst, hc, hrs, hca⟩ := lstep_call_inv hl
  rw [hs0] at hst
  simp only [List.cons.injEq] at hst
  obtain ⟨h1s, h2s⟩ := hst
  subst h1s; subst h2s; subst hrs
  have hops := h.ops hE hs0 ht0
  have hca' := Res.norm_eq_ok (callArgs_rename (σ := σ) (fr := fr) (fr' := fr') (fn := fn)
    (by rw [h.invf.func, h.invg.func, hE.externs])
    (fun x hx => hops x (by rw [hc]; exact hx))) hca
  have htc : (renStmt σ s).inst = .call fn (args.map σ) := by simp [renStmt, hc, mapOperands]
  refine ⟨by rw [lstep_call ht0 htc, hca']; rfl, rfl, ?_⟩
  -- continuation
  intro vs regs hty hset
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := s.results) (vs := vs)
    (setMany_spec hset).1
  refine ⟨regs', hset', bi, k + 1, k' + 1, ?_, ?_, ?_, ?_, h.slots⟩
  · have hext : sigOf f fn = some ext.sig := by
      simp only [callArgs, Res.bind_eq_ok, Res.ofOption_eq_ok] at hca
      obtain ⟨e, he, _, _, _, _, hpe⟩ := hca
      simp only [Res.pure_eq_ok, Prod.mk.injEq] at hpe
      obtain ⟨rfl, -⟩ := hpe
      rw [h.invf.func] at he
      simp only [sigOf]
      rw [show f.externs.lookup fn = f.extern? fn from rfl, he]; rfl
    refine Inv.results (fr := fr) (st := s) (rest := ss) hE.wff h.invf hs0 (fun ts0 h0 => ?_)
      (fun hp => by rw [hc] at hp; cases hp) hset
    rw [hc, Inst.resultTypes, hext] at h0
    simp only [Option.map_some, Option.some.injEq] at h0
    rw [← h0, hty]; rfl
  · have hext : sigOf g fn = some ext.sig := by
      simp only [callArgs, Res.bind_eq_ok, Res.ofOption_eq_ok] at hca
      obtain ⟨e, he, _, _, _, _, hpe⟩ := hca
      simp only [Res.pure_eq_ok, Prod.mk.injEq] at hpe
      obtain ⟨rfl, -⟩ := hpe
      rw [h.invf.func] at he
      simp only [sigOf, hE.externs]
      rw [show f.externs.lookup fn = f.extern? fn from rfl, he]; rfl
    refine Inv.results (fr := fr') (st := renStmt σ s) (rest := ts) hE.wfg h.invg ht0
      (fun ts0 h0 => ?_) (fun hp => by rw [htc] at hp; cases hp) hset'
    rw [htc, Inst.resultTypes, hext] at h0
    simp only [Option.map_some, Option.some.injEq] at h0
    rw [← h0, hty]; rfl
  · exact agree_results hE h.agree hb hb' hsk htk hσ hset hset'
  · intro b0 b0' hb0 hb0'
    rw [hb] at hb0; cases hb0
    rw [hb'] at hb0'; cases hb0'
    rw [hss, hts]; exact hal

theorem block?_corr {id : BlockId} {j : Nat} {b b' : Block} (hf : f.block? id = some b)
    (hj : f.blocks[j]? = some b) (hj' : g.blocks[j]? = some b') : g.block? id = some b' := by
  obtain ⟨j0, hj0, hid⟩ := block?_index hE.wff hf
  have := idx_unique hE.wff hj0 hj rfl
  subst this
  rw [Function.block?, List.find?_eq_some_iff_getElem] at hf ⊢
  obtain ⟨hp, i, hi, hbi, hlt⟩ := hf
  have hij : i = j0 := idx_unique hE.wff (by simp [hi, hbi]) hj0 rfl
  subst hij
  obtain ⟨b'', hb'', hid', _⟩ := hE.blocks i b hj0
  rw [hj'] at hb''; cases hb''
  have hi' : i < g.blocks.length := (List.getElem?_eq_some_iff.1 hj').1
  refine ⟨by simpa [hid'] using hp, i, hi', by simpa [hi'] using hj', fun j2 hj2 => ?_⟩
  have hj2f : j2 < f.blocks.length := by omega
  obtain ⟨b2, hb2, hid2, _⟩ := hE.blocks j2 f.blocks[j2] (by simp [hj2f])
  have := hlt j2 hj2
  simp only [List.getElem?_eq_getElem (show j2 < g.blocks.length by omega), Option.some.injEq]
    at hb2
  rw [hb2, hid2]; exact this

theorem ERel.atEnd {fr fr' bi k k'} (h : ERel σ f g Df Dg syms fr fr' bi k k')
    (hs : fr.body = []) (ht : fr'.body = []) :
    ∃ b b', f.blocks[bi]? = some b ∧ g.blocks[bi]? = some b' ∧ k = b.body.length ∧
      k' = b'.body.length := by
  obtain ⟨b, hb, h1, _, hk⟩ := h.invf.block
  obtain ⟨b', hb', h2, _, hk'⟩ := h.invg.block
  rw [hs] at h1; rw [ht] at h2
  have e1 := congrArg List.length h1; have e2 := congrArg List.length h2
  simp at e1 e2
  exact ⟨b, b', hb, hb', by omega, by omega⟩

/-- Branching: both frames enter corresponding blocks. -/
theorem ERel.enter {fr fr' bi k k' bc fr1} (h : ERel σ f g Df Dg syms fr fr' bi k k')
    (hs : fr.body = []) (ht : fr'.body = []) (hbc : bc.block ∈ termSuccs fr.term)
    (hargs : ∀ x ∈ bc.args, fr'.regs (σ x) = fr.regs x) (he : enterBlock fr bc = .ok fr1) :
    ∃ fr1', enterBlock fr' (mapBlockCall σ bc) = .ok fr1' ∧ ER σ f g Df Dg syms fr1 fr1' := by
  obtain ⟨b, b', hb, hb', hk, hk'⟩ := h.atEnd hE hs ht
  subst hk hk'
  obtain ⟨j, b2, hj, hb2, hinv1⟩ := Inv.enter hE.wff h.invf hs hbc he
  obtain ⟨b2x, args, regs, hb2x, hga, hty, hset, rfl⟩ := enterBlock_ok he
  rw [h.invf.func, hb2] at hb2x; cases hb2x
  obtain ⟨b2', hj', hid2, hpar2, hσp, -, hal2⟩ := hE.blocks j b2 hj
  have hgb : fr'.func.block? bc.block = some b2' := by
    rw [h.invg.func]; exact block?_corr hE hb2 hj hj'
  have hga' := Res.norm_eq_ok (getMany_rename hargs) hga
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := b2'.params.map (·.1)) (vs := args)
    (by rw [hpar2]; exact (setMany_spec hset).1)
  have he' : enterBlock fr' (mapBlockCall σ bc) =
      .ok ⟨fr'.func, regs', fr'.slots, b2'.body, b2'.term⟩ :=
    enterBlock_of (bc := mapBlockCall σ bc) hgb hga' (by rw [hpar2]; exact hty) hset'
  refine ⟨_, he', ?_⟩
  have htsucc : (mapBlockCall σ bc).block ∈ termSuccs fr'.term := by
    obtain ⟨_, _, _, _, _, _, h3, h4, _, _⟩ := h.blocks hE
    rw [h4, termSuccs_mapTerm, ← h3]; exact hbc
  obtain ⟨jx, b3, hj3, hb3, hinv2⟩ := Inv.enter hE.wfg h.invg ht htsucc he'
  have : b3 = b2' := by
    rw [h.invg.func] at hgb; simp only [mapBlockCall] at hb3; rw [hgb] at hb3
    exact (Option.some.inj hb3).symm
  subst b3
  have : jx = j := idx_unique hE.wfg hj3 hj' rfl
  subst jx
  refine ⟨j, 0, 0, hinv1, hinv2, ?_, ?_, h.slots⟩
  · intro v hv hrep
    by_cases hdv : Df.dm v = some (j, 0)
    · obtain ⟨b4, p, hb4, hp, hpv⟩ := site_param' hE.wff hdv
      rw [hj] at hb4; cases hb4
      have hσv : σ v = v := by rw [← hpv]; exact hσp p hp
      rw [hσv]
      have hvm : v ∈ b2.params.map (·.1) := List.mem_map.2 ⟨p, hp, hpv⟩
      refine ⟨⟨j, 0, ?_, .inl ⟨rfl, Nat.le_refl _⟩⟩, ?_⟩
      · rw [← hpv]; exact site_param hE.wfg hj' (by rw [hpar2]; exact hp)
      · rw [hpar2] at hset'
        exact (setMany_same hset hset' v hvm).symm
    · have hbid : b2.id = bc.block := by obtain ⟨_, _, h0⟩ := block?_index hE.wff hb2; exact h0
      have hterm : fr.term = b.term := by
        obtain ⟨b0, _, hb0, _, _, _, h3, _⟩ := h.blocks hE
        rw [hb] at hb0; cases hb0; exact h3
      have hvp := avail_pred hE.wff hb hj (by rw [hbid, ← hterm]; exact hbc) hv hdv
      obtain ⟨hav, heq⟩ := h.agree v hvp hrep
      obtain ⟨⟨d', t'⟩, hd'⟩ := Option.isSome_iff_exists.1 hrep
      obtain ⟨d, t, hd, hva⟩ := hv
      rcases hva with ⟨hdj, ht0⟩ | ⟨hne, ha⟩
      · exact absurd (by rw [hd, hdj, show t = 0 by omega]) hdv
      have hanc := hE.subst v d t hd d' t' hd'
      have hne2 : d' ≠ j := fun he => hne (Anc.antisymm hE.wff.rank ha (he ▸ hanc))
      refine ⟨⟨d', t', hd', .inr ⟨hne2, by rw [hE.idom]; exact hanc.trans ha⟩⟩, ?_⟩
      have hn1 : σ v ∉ b2'.params.map (·.1) := by
        intro hm
        obtain ⟨p, hp, hpv⟩ := List.mem_map.1 hm
        have := site_param hE.wfg hj' hp
        rw [hpv, hd'] at this
        simp only [Option.some.injEq, Prod.mk.injEq] at this
        exact hne2 this.1
      have hn2 : v ∉ b2.params.map (·.1) := by
        intro hm
        obtain ⟨p, hp, hpv⟩ := List.mem_map.1 hm
        exact hdv (by rw [← hpv]; exact site_param hE.wff hj hp)
      simp only
      rw [((setMany_spec hset').2 _).1 hn1, ((setMany_spec hset).2 _).1 hn2, heq]
  · intro b0 b0' hb0 hb0'
    rw [hj] at hb0; cases hb0
    rw [hj'] at hb0'; cases hb0'
    simpa using hal2

/-- The terminators step in lock-step. -/
theorem ERel.term {fr fr' bi k k' m} (h : ERel σ f g Df Dg syms fr fr' bi k k')
    (hs : fr.body = []) (ht : fr'.body = []) :
    (∀ fr1 m1, lstep fr m = .next fr1 m1 → ∃ fr1', lstep fr' m = .next fr1' m1 ∧
      ER σ f g Df Dg syms fr1 fr1') ∧
    (∀ vals, lstep fr m = .ret vals → lstep fr' m = .ret vals) ∧
    (∀ ext vals, lstep fr m = .tail ext vals → lstep fr' m = .tail ext vals) ∧
    (∀ c, lstep fr m = .trap c → lstep fr' m = .trap c) := by
  have hops := h.termOps hE hs ht
  obtain ⟨_, _, _, _, _, _, h3, h4, _, _⟩ := h.blocks hE
  have hterm : fr'.term = mapTerm σ fr.term := by rw [h4, h3]
  have hget : ∀ x ∈ termOperands fr.term, ∀ a, fr.get x = .ok a → fr'.get (σ x) = .ok a := by
    intro x hx a ha
    simp only [Frame.get, hops x hx] at ha ⊢
    simpa [Res.ofOption_eq_ok] using ha
  rw [lstep_term hs, lstep_term ht, hterm]
  cases hT : fr.term with
  | jump d =>
    rw [hT] at hops hget
    simp only [mapTerm]
    refine ⟨fun fr1 m1 hl => ?_, fun _ hl => ?_, fun _ _ hl => ?_, fun c hl => ?_⟩ <;>
      cases he : enterBlock fr d <;> rw [he] at hl <;> simp only [LRes.ofRes] at hl <;>
      (try cases hl)
    · obtain ⟨fr1', he', hr⟩ := h.enter hE hs ht (by rw [hT]; simp [termSuccs])
        (fun x hx => hops x (by simpa [termOperands] using hx)) he
      exact ⟨fr1', by rw [he']; rfl, hr⟩
    · exact absurd he (enterBlock_not_trap _ _ _)
  | brif c t e =>
    rw [hT] at hops hget
    simp only [mapTerm]
    have hsel : ∀ cv : Val, (if Sem.truthy cv.bits then mapBlockCall σ t else mapBlockCall σ e) =
        mapBlockCall σ (if Sem.truthy cv.bits then t else e) := by intro cv; split <;> rfl
    have hgt : ∀ c', fr.get c ≠ .trap c' := fun c' => by simp [Frame.get_ne_trap]
    refine ⟨fun fr1 m1 hl => ?_, fun _ hl => ?_, fun _ _ hl => ?_, fun c' hl => ?_⟩
    all_goals cases hc : fr.get c with
      | trap c'' => exact absurd hc (hgt c'')
      | stuck _ => rw [hc] at hl; cases hl
      | ok cv =>
        rw [hc] at hl; simp only [LRes.ofRes] at hl
        cases he : enterBlock fr (if Sem.truthy cv.bits then t else e) with
        | trap c'' => exact absurd he (enterBlock_not_trap _ _ _)
        | stuck _ => rw [he] at hl; cases hl
        | ok fr1x =>
          rw [he] at hl; simp only [LRes.ofRes] at hl
          first
          | (cases hl; done)
          | (simp only [LRes.next.injEq] at hl
             obtain ⟨rfl, rfl⟩ := hl
             rw [hget c (by simp [termOperands]) cv hc]; simp only [LRes.ofRes]
             obtain ⟨fr1', he', hr⟩ := h.enter hE hs ht (by rw [hT]; split <;> simp [termSuccs])
               (fun x hx => hops x (by
                 simp only [termOperands, List.mem_cons, List.mem_append]
                 split at hx <;> simp [hx])) he
             rw [hsel, he']
             exact ⟨fr1', rfl, hr⟩)
  | brTable x d tbl =>
    rw [hT] at hops hget
    simp only [mapTerm]
    have hgt : ∀ c', fr.get x ≠ .trap c' := fun c' => by simp [Frame.get_ne_trap]
    refine ⟨fun fr1 m1 hl => ?_, fun _ hl => ?_, fun _ _ hl => ?_, fun c' hl => ?_⟩
    all_goals cases hc : fr.get x with
      | trap c'' => exact absurd hc (hgt c'')
      | stuck _ => rw [hc] at hl; cases hl
      | ok xv =>
        rw [hc] at hl; simp only [LRes.ofRes] at hl
        cases he : enterBlock fr (tbl[xv.toNat]?.getD d) with
        | trap c'' => exact absurd he (enterBlock_not_trap _ _ _)
        | stuck _ => rw [he] at hl; cases hl
        | ok fr1x =>
          rw [he] at hl; simp only [LRes.ofRes] at hl
          first
          | (cases hl; done)
          | (simp only [LRes.next.injEq] at hl
             obtain ⟨rfl, rfl⟩ := hl
             rw [hget x (by simp [termOperands]) xv hc]; simp only [LRes.ofRes]
             have hsel : (tbl.map (mapBlockCall σ))[xv.toNat]?.getD (mapBlockCall σ d) =
                 mapBlockCall σ (tbl[xv.toNat]?.getD d) := by
               rw [List.getElem?_map]; cases tbl[xv.toNat]? <;> rfl
             have hmem : tbl[xv.toNat]?.getD d = d ∨ tbl[xv.toNat]?.getD d ∈ tbl := by
               cases hq : tbl[xv.toNat]? with
               | none => exact .inl rfl
               | some q => exact .inr (List.mem_of_getElem? hq)
             obtain ⟨fr1', he', hr⟩ := h.enter hE hs ht (by
                 rw [hT]; simp only [termSuccs, List.mem_cons, List.mem_map]
                 rcases hmem with hm | hm
                 · exact .inl (by rw [hm])
                 · exact .inr ⟨_, hm, rfl⟩)
               (fun y hy => hops y (by
                 simp only [termOperands, List.mem_cons, List.mem_append, List.mem_flatMap]
                 rcases hmem with hm | hm
                 · rw [hm] at hy; exact .inl (.inr hy)
                 · exact .inr ⟨_, hm, hy⟩)) he
             rw [hsel, he']
             exact ⟨fr1', rfl, hr⟩)
  | ret xs =>
    rw [hT] at hops
    simp only [mapTerm]
    have hg := getMany_rename (fr := fr) (fr' := fr') (σ := σ) (xs := xs) (fun x hx => hops x hx)
    refine ⟨fun fr1 m1 hl => ?_, fun vals hl => ?_, fun _ _ hl => ?_, fun c' hl => ?_⟩
    all_goals cases hc : fr.getMany xs with
      | trap c'' => exact absurd hc (getMany_not_trap _ _ _)
      | stuck _ => rw [hc] at hl; cases hl
      | ok vs =>
        rw [hc] at hl; simp only [LRes.ofRes] at hl
        first
        | (cases hl; done)
        | (simp only [LRes.ret.injEq] at hl; subst hl; rw [Res.norm_eq_ok hg hc]; rfl)
  | returnCall fn args =>
    rw [hT] at hops
    simp only [mapTerm]
    have hg := tailArgs_rename (fr := fr) (fr' := fr') (σ := σ) (fn := fn) (args := args)
      (by rw [h.invf.func, h.invg.func, hE.externs]) (by rw [h.invf.func, h.invg.func, hE.sig])
      (fun x hx => hops x hx)
    refine ⟨fun fr1 m1 hl => ?_, fun vals hl => ?_, fun _ _ hl => ?_, fun c' hl => ?_⟩
    all_goals cases hc : tailArgs fr fn args with
      | trap c'' =>
        rw [hc] at hl
        first
        | (cases hl; done)
        | (cases hl; rw [Res.norm_eq_trap hg hc]; rfl)
      | stuck _ => rw [hc] at hl; cases hl
      | ok p =>
        obtain ⟨e, vs⟩ := p
        rw [hc] at hl; simp only [LRes.ofRes] at hl
        first
        | (cases hl; done)
        | (simp only [LRes.tail.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
           rw [Res.norm_eq_ok hg hc]; rfl)
  | trap c =>
    simp only [mapTerm]
    exact ⟨(fun _ _ hl => by cases hl), (fun _ hl => by cases hl), (fun _ _ hl => by cases hl),
      (fun _ hl => hl)⟩

/-- `ER` is a simulation. -/
theorem ER.isSim : IsSim syms (ER σ f g Df Dg syms) where
  frame := by
    rintro fr fr' ⟨bi, k, k', h⟩
    exact ⟨h.slots, by rw [h.invg.func, h.invf.func, hE.sig]⟩
  next := by
    rintro fr fr' m fr1 m1 ⟨bi, k, k', h⟩ hm hl
    obtain ⟨fr'', k'', hst, h2, hset⟩ := h.catchUp hE hm
    cases hs : fr.body with
    | nil =>
      rcases hset with ⟨-, ht⟩ | ⟨s, _, _, _, hss, _⟩ | ⟨s, _, hss, _⟩
      · obtain ⟨fr1', hl', hr⟩ := (h2.term hE (m := m) hs ht).1 fr1 m1 hl
        exact ⟨fr1', hst.trans (.single hl'), hr⟩
      all_goals rw [hs] at hss; cases hss
    | cons s ss =>
      rcases hset with ⟨hss, -⟩ | ⟨s', ss', t, ts, hss, ht, hk, hal⟩ | ⟨s', ss', hss, hd, hal⟩
      · rw [hs] at hss; cases hss
      · rw [hs] at hss; cases hss
        have hnc : ∀ fn args, s.inst ≠ .call fn args := by
          intro fn args hc
          exact (lstep_call_of_call hs hc).1 fr1 m1 hl
        obtain ⟨fr1', hl', hr⟩ := (h2.keep hE hm hs ht hk hal hnc).1 fr1 m1 hl
        exact ⟨fr1', hst.trans (.single hl'), bi, k + 1, k'' + 1, hr⟩
      · rw [hs] at hss; cases hss
        obtain ⟨rfl, hr⟩ := (h2.delete hE hm hs hd hal).1 fr1 m1 hl
        exact ⟨fr'', hst, bi, k + 1, k'', hr⟩
  call := by
    rintro fr fr' m ext vals rs rest ⟨bi, k, k', h⟩ hm hl
    obtain ⟨st, fn, args, hb, hc, hrs, _⟩ := lstep_call_inv hl
    obtain ⟨fr'', k'', hst, h2, hset⟩ := h.catchUp hE hm
    rw [hb] at hset
    rcases hset with ⟨hss, -⟩ | ⟨s', ss', t, ts, hss, ht, hk, hal⟩ | ⟨s', ss', hss, hd, hal⟩
    · cases hss
    · cases hss
      obtain ⟨hl', -, hk'⟩ := h2.call hE hm hb ht hk hal hl
      exact ⟨fr'', rs, ts, hst, hl', hk'⟩
    · cases hss
      exact absurd hl ((h2.delete hE hm hb hd hal).2.2 _ _ _ _)
  ret := by
    rintro fr fr' m vals ⟨bi, k, k', h⟩ hm hl
    have hs := lstep_ret_inv hl
    obtain ⟨fr'', k'', hst, h2, hset⟩ := h.catchUp hE hm
    rw [hs] at hset
    rcases hset with ⟨-, ht⟩ | ⟨s, _, _, _, hss, _⟩ | ⟨s, _, hss, _⟩
    · exact ⟨fr'', hst, (h2.term hE (m := m) hs ht).2.1 vals hl⟩
    all_goals cases hss
  tail := by
    rintro fr fr' m ext vals ⟨bi, k, k', h⟩ hm hl
    have hs := lstep_tail_inv hl
    obtain ⟨fr'', k'', hst, h2, hset⟩ := h.catchUp hE hm
    rw [hs] at hset
    rcases hset with ⟨-, ht⟩ | ⟨s, _, _, _, hss, _⟩ | ⟨s, _, hss, _⟩
    · exact ⟨fr'', hst, (h2.term hE (m := m) hs ht).2.2.1 ext vals hl⟩
    all_goals cases hss
  trap := by
    rintro fr fr' m c ⟨bi, k, k', h⟩ hm hl
    obtain ⟨fr'', k'', hst, h2, hset⟩ := h.catchUp hE hm
    cases hs : fr.body with
    | nil =>
      rcases hset with ⟨-, ht⟩ | ⟨s, _, _, _, hss, _⟩ | ⟨s, _, hss, _⟩
      · exact ⟨fr'', m, hst, (h2.term hE (m := m) hs ht).2.2.2 c hl⟩
      all_goals rw [hs] at hss; cases hss
    | cons s ss =>
      rcases hset with ⟨hss, -⟩ | ⟨s', ss', t, ts, hss, ht, hk, hal⟩ | ⟨s', ss', hss, hd, hal⟩
      · rw [hs] at hss; cases hss
      · rw [hs] at hss; cases hss
        have hnc : ∀ fn args, s.inst ≠ .call fn args := by
          intro fn args hc
          exact (lstep_call_of_call hs hc).2 c hl
        exact ⟨fr'', m, hst, (h2.keep hE hm hs ht hk hal hnc).2 c hl⟩
      · rw [hs] at hss; cases hss
        exact absurd hl ((h2.delete hE hm hs hd hal).2.1 c)

end

/-- **The edit validator is sound.** -/
theorem editOk_sim {σ : ValueId → ValueId} {f g : Function} {fi gi : Info}
    (hf : check f = .ok fi) (hg : check g = .ok gi) (h : editOk σ f g fi gi = true) :
    FunSim f g := by
  have hE := editOk_facts hf hg h
  refine ⟨hE.name, hE.sig, hE.slots, fun syms => ⟨_, ER.isSim hE, fun b hb => ?_⟩⟩
  have hb0 : f.blocks[0]? = some b := by
    simpa [Function.entry?, List.head?_eq_getElem?] using hb
  obtain ⟨b', hb0', hid, hpar, hσp, -, hal⟩ := hE.blocks 0 b hb0
  refine ⟨b', by simpa [Function.entry?, List.head?_eq_getElem?] using hb0', hpar,
    fun args regs slots hty hr hsl => ⟨0, 0, 0, Inv.entry hE.wff hb hty hr hsl, ?_, ?_, ?_, rfl⟩⟩
  · rw [← hpar] at hty hr
    exact Inv.entry hE.wfg (by simpa [Function.entry?, List.head?_eq_getElem?] using hb0') hty hr
      (by rw [hsl, hE.slots])
  · intro v hv hrep
    obtain ⟨b1, p, hb1, hp, hpv⟩ := site_param' hE.wff (avail_entry hE.wff hv)
    rw [hb0] at hb1; cases hb1
    have hσv : σ v = v := by rw [← hpv]; exact hσp p hp
    rw [hσv]
    refine ⟨⟨0, 0, ?_, .inl ⟨rfl, Nat.le_refl _⟩⟩, rfl⟩
    rw [← hpv]; exact site_param hE.wfg hb0' (by rw [hpar]; exact hp)
  · intro b0 b0' h0 h0'
    rw [hb0] at h0; cases h0
    rw [hb0'] at h0'; cases h0'
    simpa using hal

end Opt
