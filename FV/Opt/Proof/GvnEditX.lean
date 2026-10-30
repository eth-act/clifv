import FV.Opt.Proof.GvnEdit
import FV.Opt.Proof.SimWin

/-!
# The edit validator is sound, `call_indirect` and `try_call` included (`Opt.editOk_simX`)

`Opt.editOk_sim` (`FV/Opt/Proof/GvnEdit.lean`, GVN, DCE and LICM) with the obligations of
`IsSimX`: a well-formed function (`Opt.check`) has no `call_indirect` (its result types are
unknown to `check`), so only `try_call`/`try_call_indirect` terminators remain. They are kept
renamed (`mapTerm σ`); the target catches up to its terminator, makes the same call, and enters
the same normal-return successor with the same arguments: the renamed values, or the call's
results at each side's fresh value (`tryNormal_pair`), the windows being equal (`Win`).
-/

namespace Opt

open Clif

/-- Available values are defined, hence below the fresh value. -/
theorem avail_lt {f : Function} {W : WfData} (hW : Wf f W) {i k v : Nat} (h : Avail W i k v) :
    v < f.freshValue := by
  obtain ⟨d, t, hd, -⟩ := h
  obtain ⟨i', b, hb, hp⟩ := mem_defSites.1 (hW.sitesRev v (d, t) hd)
  have hbm : b ∈ f.blocks := List.mem_of_getElem? hb
  rcases hp with ⟨p, hp, hpv, -⟩ | ⟨j, st, hst, hv, -⟩
  · rw [← hpv]; exact (lt_freshValue hbm).1 p hp
  · exact (lt_freshValue hbm).2 st (List.mem_of_getElem? hst) v hv

/-- A well-formed function has no `call_indirect`. -/
theorem Wf.noCI {f : Function} {W : WfData} (hW : Wf f W) {i j : Nat} {b : Block} {st : Stmt}
    (hb : f.blocks[i]? = some b) (hs : b.body[j]? = some st) :
    ∀ sig c args, st.inst ≠ .callIndirect sig c args := by
  intro sig c args hi
  obtain ⟨ts, hts, -⟩ := hW.results i b hb j st hs
  rw [hi] at hts
  simp [Inst.resultTypes] at hts

/-- The invariant reads only registers below the fresh value. -/
theorem Inv.regs_congr {f : Function} {W : WfData} (hW : Wf f W) {syms : String → Option Nat}
    {fr : Frame} {bi k : Nat} (h : Inv f W syms fr bi k) {r : Regs}
    (hr : ∀ v < f.freshValue, r v = fr.regs v) : Inv f W syms { fr with regs := r } bi k where
  func := h.func
  block := h.block
  slots := h.slots
  regs v hv := by show ∃ a, r v = some a ∧ _; rw [hr v (avail_lt hW hv)]; exact h.regs v hv
  pure v n hv hp := by
    show r v = _
    rw [hr v (avail_lt hW hv), h.pure v n hv hp]
    obtain ⟨d, j, b, st, hd, hb, hst, -, hi, -⟩ := hp
    symm
    apply evalNode_congr (fr := fr) (fr' := { fr with regs := r }) rfl rfl rfl
    intro x hx
    rw [← hi] at hx
    exact hr x (avail_lt hW (hW.uses d b hb j st hst x hx))

theorem ciArgs_ok {fr : Frame} {sig : Nat} {callee : ValueId} {args : List ValueId}
    {d : Signature} {a : Nat} {vals : List Val} :
    ciArgs fr sig callee args = .ok (d, a, vals) ↔ ∃ cv cv64, fr.func.sigDecls.lookup sig = some d ∧
      fr.regs callee = some cv ∧ cv.as? .i64 = some cv64 ∧ a = cv64.toNat ∧
      fr.getMany args = .ok vals := by
  unfold ciArgs
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Frame.get, Res.pure_eq_ok, Prod.mk.injEq]
  constructor
  · rintro ⟨d', hd, cv, hcv, cv64, h64, vals', hv, rfl, rfl, rfl⟩
    exact ⟨cv, cv64, hd, hcv, h64, rfl, hv⟩
  · rintro ⟨cv, cv64, hd, hcv, h64, rfl, hv⟩
    exact ⟨d, hd, cv, hcv, cv64, h64, vals, hv, rfl, rfl, rfl⟩

/-- `ciArgs` of renamed operands. -/
theorem ciArgs_rename {σ : ValueId → ValueId} {fr fr' : Frame} {sig : Nat} {callee : ValueId}
    {args : List ValueId} {r : Signature × Nat × List Val}
    (hsd : fr'.func.sigDecls = fr.func.sigDecls) (h : ∀ x ∈ callee :: args, fr'.regs (σ x) = fr.regs x)
    (hc : ciArgs fr sig callee args = .ok r) : ciArgs fr' sig (σ callee) (args.map σ) = .ok r := by
  obtain ⟨d, a, vals⟩ := r
  obtain ⟨cv, cv64, hd, hcv, h64, rfl, hv⟩ := ciArgs_ok.1 hc
  refine ciArgs_ok.2 ⟨cv, cv64, by rw [hsd]; exact hd, by rw [h callee (by simp)]; exact hcv, h64, rfl,
    Res.norm_eq_ok (getMany_rename fun x hx => h x (by simp [hx])) hv⟩

section
variable {σ : ValueId → ValueId} {f g : Function} {Df Dg : WfData} (hE : EditFacts σ f g Df Dg)
  {syms : String → Option Nat}
include hE

/-- Registers from the fresh values on are not read. -/
theorem ERel.regs_congr {fr fr' : Frame} {bi k k' : Nat} (h : ERel σ f g Df Dg syms fr fr' bi k k')
    {r r' : Regs} (hr : ∀ v < f.freshValue, r v = fr.regs v)
    (hr' : ∀ v < g.freshValue, r' v = fr'.regs v) :
    ERel σ f g Df Dg syms { fr with regs := r } { fr' with regs := r' } bi k k' where
  invf := h.invf.regs_congr hE.wff hr
  invg := h.invg.regs_congr hE.wfg hr'
  agree v hv hrep := by
    obtain ⟨ha, he⟩ := h.agree v hv hrep
    refine ⟨ha, ?_⟩
    show r' (σ v) = r v
    rw [hr' _ (avail_lt hE.wfg ha), hr _ (avail_lt hE.wff hv)]
    exact he
  align := h.align
  slots := h.slots

/-- Branching to corresponding blocks with the same argument values. -/
theorem ERel.enterG {fr fr' : Frame} {bi k k' : Nat} {bc bc' : BlockCall} {fr1 : Frame}
    {vs : List Val} (h : ERel σ f g Df Dg syms fr fr' bi k k')
    (hs : fr.body = []) (ht : fr'.body = []) (hbc : bc.block ∈ termSuccs fr.term)
    (hblk : bc'.block = bc.block) (hga : fr.getMany bc.args = .ok vs)
    (hga' : fr'.getMany bc'.args = .ok vs) (he : enterBlock fr bc = .ok fr1) :
    ∃ fr1', enterBlock fr' bc' = .ok fr1' ∧ ER σ f g Df Dg syms fr1 fr1' := by
  obtain ⟨b, b', hb, hb', hk, hk'⟩ := h.atEnd hE hs ht
  subst hk hk'
  obtain ⟨j, b2, hj, hb2, hinv1⟩ := Inv.enter hE.wff h.invf hs hbc he
  obtain ⟨b2x, args, regs, hb2x, hga0, hty, hset, rfl⟩ := enterBlock_ok he
  rw [h.invf.func, hb2] at hb2x; cases hb2x
  rw [hga] at hga0; cases hga0
  obtain ⟨b2', hj', hid2, hpar2, hσp, -, hal2⟩ := hE.blocks j b2 hj
  have hgb : fr'.func.block? bc'.block = some b2' := by
    rw [h.invg.func, hblk]; exact block?_corr hE hb2 hj hj'
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := b2'.params.map (·.1)) (vs := vs)
    (by rw [hpar2]; exact (setMany_spec hset).1)
  have he' : enterBlock fr' bc' = .ok ⟨fr'.func, regs', fr'.slots, b2'.body, b2'.term⟩ :=
    enterBlock_of hgb hga' (by rw [hpar2]; exact hty) hset'
  refine ⟨_, he', ?_⟩
  have htsucc : bc'.block ∈ termSuccs fr'.term := by
    obtain ⟨_, _, _, _, _, _, h3, h4, _, _⟩ := h.blocks hE
    rw [h4, termSuccs_mapTerm, ← h3, hblk]; exact hbc
  obtain ⟨jx, b3, hj3, hb3, hinv2⟩ := Inv.enter hE.wfg h.invg ht htsucc he'
  have : b3 = b2' := by
    rw [h.invg.func] at hgb; rw [hgb] at hb3
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

/-- At the terminator: the target caught up, its terminator renamed, operands read alike. -/
theorem ER.atTerm {fr fr' : Frame} {m : Mem} {bi k k' : Nat}
    (h : ERel σ f g Df Dg syms fr fr' bi k k') (hm : m.symbols = syms) (hs : fr.body = []) :
    ∃ fr'' k'', LStar fr' m fr'' m ∧ ERel σ f g Df Dg syms fr fr'' bi k k'' ∧ fr''.body = [] ∧
      fr''.term = mapTerm σ fr.term ∧
      (∀ x ∈ termOperands fr.term, fr''.regs (σ x) = fr.regs x ∧ x < f.freshValue ∧
        σ x < g.freshValue) := by
  obtain ⟨fr'', k'', hst, h2, hset⟩ := h.catchUp hE hm
  rw [hs] at hset
  have ht0 : fr''.body = [] := by
    rcases hset with ⟨-, h⟩ | ⟨s, _, _, _, hss, _⟩ | ⟨s, _, hss, _⟩
    · exact h
    all_goals cases hss
  obtain ⟨b, b', hb, hb', h1, h2', h3, h4, -⟩ := h2.blocks hE
  refine ⟨fr'', k'', hst, h2, ht0, by rw [h4, h3], fun x hx => ⟨h2.termOps hE hs ht0 x hx, ?_, ?_⟩⟩
  · have hk : k = b.body.length := by
      obtain ⟨b2, hb2, _, _, hk⟩ := h2.invf.block
      rw [hb] at hb2; cases hb2
      rw [h1] at hs
      have := congrArg List.length hs; simp at this; omega
    rw [h3] at hx
    exact avail_lt hE.wff (hE.wff.termUses bi b hb x hx)
  · have hk' : k'' = b'.body.length := by
      obtain ⟨b2, hb2, _, _, hk⟩ := h2.invg.block
      rw [hb'] at hb2; cases hb2
      rw [h2'] at ht0
      have := congrArg List.length ht0; simp at this; omega
    obtain ⟨b'', hb'', -, -, -, hterm, -⟩ := hE.blocks bi b hb
    rw [hb'] at hb''; cases hb''
    rw [h3] at hx
    exact avail_lt hE.wfg (hE.wfg.termUses bi b' hb' (σ x) (by
      rw [hterm, termOperands_mapTerm]; exact List.mem_map_of_mem hx))

/-- The post-call frames of a `try_call`: binding the results at each side's fresh value and
entering the normal-return successors gives related frames. -/
theorem ER.tcont {fr fr'' : Frame} {bi k k'' : Nat} {n : Nat} {et : ExnTable} {bc bc' : BlockCall}
    {rtys : List Ty} (h : ERel σ f g Df Dg syms fr fr'' bi k k'') (hs : fr.body = [])
    (ht0 : fr''.body = []) (hsucc : bc.block ∈ termSuccs fr.term)
    (hvals : ∀ x ∈ et.normal.vals, fr''.regs (σ x) = fr.regs x ∧ x < f.freshValue ∧
      σ x < g.freshValue)
    (hw : Win fr fr'') (hbc : tryNormal et fr.func.freshValue = .ok bc)
    (hbc' : tryNormal (et.mapVals σ) fr''.func.freshValue = .ok bc') :
    TCont (ER σ f g Df Dg syms) fr (tryRets n fr.func.freshValue) bc fr''
      (tryRets n fr''.func.freshValue) bc' rtys := by
  have hf := h.invf.func
  have hg := h.invg.func
  intro vs regs _ hset
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr''.regs) (xs := tryRets n fr''.func.freshValue)
    (vs := vs) (by have := (setMany_spec hset).1; simp only [tryRets, List.length_map,
      List.length_range] at this ⊢; exact this)
  refine ⟨regs', hset', fun fr1 he1 => ?_⟩
  have hW := setMany_tryRets hset
  have hW' := setMany_tryRets hset'
  have hlo : ∀ v < f.freshValue, regs v = fr.regs v := by
    intro v hv
    refine ((setMany_spec hset).2 v).1 fun hm => ?_
    obtain ⟨j, -, he⟩ := List.mem_map.1 hm
    have he' : fr.func.freshValue + j = v := he
    rw [hf] at he'
    exact no_window' he' hv
  have hlo' : ∀ v < g.freshValue, regs' v = fr''.regs v := by
    intro v hv
    refine ((setMany_spec hset').2 v).1 fun hm => ?_
    obtain ⟨j, -, he⟩ := List.mem_map.1 hm
    have he' : fr''.func.freshValue + j = v := he
    rw [hg] at he'
    exact no_window' he' hv
  have hR := h.regs_congr hE hlo hlo'
  obtain ⟨b2, args2, regs2, -, hga2, -, -, -⟩ := enterBlock_ok he1
  obtain ⟨bc2, hbc2, hblk, hpw⟩ := tryNormal_pair σ (et := et) (et' := et.mapVals σ) rfl
    (b2 := fr''.func.freshValue) hbc
  rw [hbc'] at hbc2; cases hbc2
  have hga' : Frame.getMany { fr'' with regs := regs' } bc'.args = .ok args2 := by
    refine getMany_pw2 (A := { fr with regs }) (hpw.imp fun x y hxy => ?_) hga2
    simp only
    rcases hxy with ⟨v, hv, hx, hy⟩ | ⟨i, hx, hy⟩
    · rw [hx, hy]
      obtain ⟨h1, h2, h3⟩ := hvals v hv
      rw [hlo' _ h3, hlo _ h2, h1]
    · rw [hx, hy, hW i, hW' i]
      split
      · rfl
      · exact (hw i).symm
  exact hR.enterG hE hs ht0 hsucc hblk hga2 hga' he1

/-- `ER` with windows: the obligations of `IsSimW`. -/
theorem ER.isSimW (hsd : g.sigDecls = f.sigDecls) : IsSimW syms (ER σ f g Df Dg syms) where
  toIsSim := ER.isSim hE
  ci := by
    rintro fr fr' m st rest sig callee args d a vals ⟨bi, k, k', h⟩ - - - hm hb hi hca
    exfalso
    obtain ⟨b, hbi, h1, -, -⟩ := h.invf.block
    rw [h1] at hb
    obtain ⟨hk, -, -⟩ := drop_eq_cons hb
    exact hE.wff.noCI hbi hk sig callee args hi
  tc := by
    refine ⟨?_, ?_⟩
    · rintro fr fr' m fn args et n base bc ext vals ⟨bi, k, k', h⟩ hI hI' hw hm hb ht htc hca
      obtain ⟨fr'', k'', hst, h2, ht0, hterm, hops⟩ := ER.atTerm hE h hm hb
      rw [ht] at hterm hops
      have hf := h.invf.func
      have hg := h2.invg.func
      obtain ⟨e0, s0, he0, hs0, hc0, rfl, hbc, rfl⟩ := tcArgs_ok.1 htc
      obtain ⟨bc', hbc', -, -⟩ := tryNormal_pair σ (et := et) (et' := et.mapVals σ) rfl
        (b2 := fr''.func.freshValue) hbc
      have htc' : tcArgs fr'' fn (et.mapVals σ) =
          .ok (e0.sig.returns.length, fr''.func.freshValue, bc') := by
        refine tcArgs_ok.2 ⟨e0, s0, ?_, ?_, hc0, rfl, hbc', rfl⟩
        · rw [← he0]; simp only [Function.extern?, hg, hf, hE.externs]
        · rw [← hs0, hg, hf, hsd]; rfl
      have hca' : callArgs fr'' fn (args.map σ) = .ok (ext, vals) :=
        Res.norm_eq_ok (callArgs_rename (by rw [hg, hf, hE.externs])
          (fun x hx => (hops x (by simp [termOperands, hx])).1)) hca
      have hw' : Win fr fr'' := by
        obtain ⟨-, hf2, hw2⟩ := LStar.win hI' hst
        intro i; rw [hf2, hw2 i]; exact hw i
      refine ⟨fr'', fn, args.map σ, et.mapVals σ, _, bc', hst, ht0, hterm, htc', hca', ?_⟩
      exact ER.tcont hE h2 hb ht0 (by rw [ht]; exact normal_succ hbc)
        (fun x hx => hops x (normal_vals_sub x hx)) hw' hbc hbc'
    · rintro fr fr' m callee args et n base bc d a vals ⟨bi, k, k', h⟩ hI hI' hw hm hb ht htc hca
      obtain ⟨fr'', k'', hst, h2, ht0, hterm, hops⟩ := ER.atTerm hE h hm hb
      rw [ht] at hterm hops
      have hf := h.invf.func
      have hg := h2.invg.func
      obtain ⟨s0, hs0, rfl, hbc, rfl⟩ := ticArgs_ok.1 htc
      obtain ⟨bc', hbc', -, -⟩ := tryNormal_pair σ (et := et) (et' := et.mapVals σ) rfl
        (b2 := fr''.func.freshValue) hbc
      have htc' : ticArgs fr'' (et.mapVals σ) =
          .ok (s0.returns.length, fr''.func.freshValue, bc') :=
        ticArgs_ok.2 ⟨s0, by rw [← hs0, hg, hf, hsd]; rfl, rfl, hbc', rfl⟩
      have hca' : ciArgs fr'' (et.mapVals σ).sig (σ callee) (args.map σ) = .ok (d, a, vals) :=
        ciArgs_rename (by rw [hg, hf, hsd])
          (fun x hx => (hops x (by
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · simp [termOperands]
            · simp [termOperands, hx])).1) hca
      have hw' : Win fr fr'' := by
        obtain ⟨-, hf2, hw2⟩ := LStar.win hI' hst
        intro i; rw [hf2, hw2 i]; exact hw i
      refine ⟨fr'', σ callee, args.map σ, et.mapVals σ, _, bc', hst, ht0, hterm, htc', hca', ?_⟩
      exact ER.tcont hE h2 hb ht0 (by rw [ht]; exact normal_succ hbc)
        (fun x hx => hops x (normal_vals_sub' x hx)) hw' hbc hbc'

end

/-- **The edit validator is sound**, `call_indirect` and `try_call` included (for outputs
keeping the signature declarations). -/
theorem editOk_simX {σ : ValueId → ValueId} {f g : Function} {fi gi : Info}
    (hf : check f = .ok fi) (hg : check g = .ok gi) (h : editOk σ f g fi gi = true)
    (hsd : g.sigDecls = f.sigDecls) : FunSimX f g := by
  have hE := editOk_facts hf hg h
  refine FunSimX.ofW hE.name hE.sig hE.slots hE.externs fun syms =>
    ⟨_, ER.isSimW hE hsd, fun b hb => ?_⟩
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
