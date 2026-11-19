import FV.Opt.Proof.MidValRel

/-!
# `g` runs its checked pure prefix (#1119, module (5), slice B)

`gPre_run : Hyp f g fi gi cert norm → GPreRun f g fi gi cert norm` (`GPreRun` in
`FV/Opt/Proof/MidValRel.lean`): the statements `CC.gPre` accepts before `g`'s next skeleton
statement are `nop`s and checked pure statements (`gPre_spec`). Each is one local step of `g`
that keeps memory (`gStep`):

* a `nop` binds nothing;
* a pure statement `y = i` binds the value of its term `t` (`PureOk`): `t` is the node of the
  operands' terms (`tmVal_mapOperands`, operands available in `g`, `agreeG`) or the
  normaliser's term (`NormSound`, `evalNode_rename`), so its value is `evalNode` of `i` in `g`'s
  frame; that value exists by totality (`evalInst_pureK_total`) or, for a `partialK` node, by
  the `defd` fact of `S`; a `pureK` node reads memory only through the link-time symbols
  (`evalNode_pureK_syms`), so the step evaluates `i` in the current memory to it.

The new value's term has a site no later than `f`'s position (`PureOk.site`); `Inv` follows from
`Inv.results`.
-/

namespace Opt.MidVal

open Clif

/-- A `pureK` node reads memory only through the link-time symbols. -/
theorem evalNode_pureK_syms {fr : Frame} {m m' : Mem} {i : Inst} (hp : pureK i = true)
    (hs : m'.symbols = m.symbols) : evalNode fr m' i = evalNode fr m i := by
  cases hq : partialK i
  · exact evalNode_pureK_mem hp hq
  · cases i <;> simp only [partialK] at hq <;> (try cases hq) <;>
      simp only [evalNode_eq_val1, evalInst, val1_bind, val1_pure, hs]
    all_goals (repeat' (first | split | simp only [val1_bind, val1_pure]))
    all_goals simp_all [val1_bind, val1_pure, val1_ok, Res.ofOption]

/-- A `pureK` node with a value evaluates to it and keeps memory. -/
theorem evalInst_of_evalNode {fr : Frame} {m : Mem} {i : Inst} {v : Val} (hp : pureK i = true)
    (h : evalNode fr m i = some v) : evalInst fr m i = .ok ([v], m) := by
  rw [evalNode_eq_val1] at h
  rcases hr : evalInst fr m i with ⟨vs, mm⟩ | c | msg
  · rw [hr] at h
    rw [pureK_mem hp hr]
    rcases vs with _ | ⟨w, _ | ⟨w2, vs⟩⟩
    · simp [val1] at h
    · simp only [val1, Option.some.injEq] at h
      subst h
      rfl
    · simp [val1] at h
  · rw [hr] at h; cases h
  · rw [hr] at h; cases h

theorem avail_succ {W : WfData} {bi k : Nat} {v : ValueId} (h : Avail W bi (k + 1) v) :
    W.dm v = some (bi, k + 1) ∨ Avail W bi k v := by
  obtain ⟨d, t, hv, hva⟩ := h
  rcases hva with ⟨hd, ht⟩ | h2
  · subst hd
    rcases Nat.lt_or_ge t (k + 1) with h | h
    · exact .inr ⟨d, t, hv, .inl ⟨rfl, by omega⟩⟩
    · exact .inl (by rw [hv, show t = k + 1 by omega])
  · exact .inr ⟨d, t, hv, .inr h2⟩

section
variable {f g : Function} {fi gi : Info} {cert : Cert} {norm : Norm}

/-- The results of `g`'s statement `st` (in the body at `k'`) are as many as the values it
evaluates to. -/
theorem results_len (H : Hyp f g fi gi cert norm) {syms : String → Option Nat} {bi k' : Nat}
    {fr' : Frame} {m mm : Mem} {st : Stmt} {rest : List Stmt} {vals : List Val}
    (hinv : Inv g (wfData g gi) syms fr' bi k') (hb : fr'.body = st :: rest)
    (hev : evalInst fr' m st.inst = .ok (vals, mm)) : st.results.length = vals.length := by
  obtain ⟨gb, hgb, hbody, -, -⟩ := hinv.block
  rw [hbody] at hb
  obtain ⟨hst, -, -⟩ := drop_eq_cons hb
  obtain ⟨ts, hts, htl, -⟩ := H.wfg.results bi gb hgb k' st hst
  rw [← htl, ← evalInst_types hev hts, List.length_map]

/-- One statement of `g` that evaluates to `vals` without changing memory, where each result's
term holds the value bound to it and has a site no later than `(bi, k)`. -/
theorem gStep (H : Hyp f g fi gi cert norm) {syms : String → Option Nat} {bi k k' : Nat}
    {fr fr' : Frame} {m : Mem} {st : Stmt} {rest : List Stmt} {vals : List Val}
    (hinv : Inv g (wfData g gi) syms fr' bi k')
    (hb : fr'.body = st :: rest) (hc : ∀ fn args, st.inst ≠ .call fn args)
    (hev : evalInst fr' m st.inst = .ok (vals, m))
    (hpure : isPure st.inst = true → ∃ a, vals = [a] ∧ evalNode fr' (symMem syms) st.inst = some a)
    (hagree : ∀ y, Avail (wfData g gi) bi k' y →
      TV f cert syms fr ((ccOf fi gi cert norm).eg y) = fr'.regs y)
    (hsites : ∀ y, Avail (wfData g gi) bi k' y →
      LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf ((ccOf fi gi cert norm).eg y)) (bi, k))
    (hres : ∀ (n : Nat) (r : ValueId), st.results[n]? = some r →
      TV f cert syms fr ((ccOf fi gi cert norm).eg r) = vals[n]? ∧
      LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf ((ccOf fi gi cert norm).eg r)) (bi, k)) :
    ∃ fr1, lstep fr' m = .next fr1 m ∧ fr1.body = rest ∧ fr1.term = fr'.term ∧
      fr1.slots = fr'.slots ∧ fr1.func = fr'.func ∧
      Inv g (wfData g gi) syms fr1 bi (k' + 1) ∧
      (∀ y, Avail (wfData g gi) bi (k' + 1) y →
        TV f cert syms fr ((ccOf fi gi cert norm).eg y) = fr1.regs y) ∧
      (∀ y, Avail (wfData g gi) bi (k' + 1) y →
        LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf ((ccOf fi gi cert norm).eg y)) (bi, k)) := by
  have hW := H.wfg
  obtain ⟨gb, hgb, hbody, -, -⟩ := hinv.block
  have hb' := hb
  rw [hbody] at hb'
  obtain ⟨hst, -, -⟩ := drop_eq_cons hb'
  obtain ⟨regs, hset⟩ := setMany_len (r := fr'.regs) (results_len H hinv hb hev)
  obtain ⟨-, hsm⟩ := setMany_spec hset
  have hstep : lstep fr' m = .next { fr' with regs, body := rest } m := by
    rw [lstep_inst hb hc, hev]
    simp only [LRes.ofRes_ok, hset]
  -- values available before the statement are not its results
  have hnot : ∀ y, Avail (wfData g gi) bi k' y → y ∉ st.results := by
    intro y ⟨d, t, hy, hya⟩ hr
    rw [hW.site_result hgb hst hr] at hy
    simp only [Option.some.injEq, Prod.mk.injEq] at hy
    obtain ⟨rfl, rfl⟩ := hy
    rcases hya with ⟨_, ht⟩ | ⟨hne, _⟩
    · omega
    · exact hne rfl
  -- values defined right after the statement are its results
  have hin : ∀ y, (wfData g gi).dm y = some (bi, k' + 1) → y ∈ st.results := by
    intro y hy
    obtain ⟨b', st', hb2, hst', hr'⟩ := hW.site_stmt hy
    rw [hgb] at hb2; cases hb2
    rw [hst] at hst'; cases hst'
    exact hr'
  refine ⟨_, hstep, rfl, rfl, rfl, rfl,
    hW.inv_results hinv hb (fun ts hts => evalInst_types hev hts) hpure hset,
    fun y hy => ?_, fun y hy => ?_⟩
  · show _ = regs y
    rcases avail_succ hy with hd | hy'
    · obtain ⟨n, hn, hrv⟩ := (hsm y).2 (hin y hd)
      rw [(hres n y hn).1, hrv]
    · rw [(hsm y).1 (hnot y hy'), hagree y hy']
  · rcases avail_succ hy with hd | hy'
    · obtain ⟨n, hn, -⟩ := (hsm y).2 (hin y hd)
      exact (hres n y hn).2
    · exact hsites y hy'

/-- One statement of `g`'s checked pure prefix (`GPreStmt`). -/
theorem gStmt (H : Hyp f g fi gi cert norm) {syms : String → Option Nat} {bi k k' : Nat}
    {S : List Fact} {fr fr' : Frame} {m : Mem} {st : Stmt} {rest : List Stmt}
    (hm : m.symbols = syms)
    (hinvf : Inv f (wfData f fi) syms fr bi k)
    (hinv : Inv g (wfData g gi) syms fr' bi k')
    (hsl : fr'.slots = fr.slots)
    (hagree : ∀ y, Avail (wfData g gi) bi k' y →
      TV f cert syms fr ((ccOf fi gi cert norm).eg y) = fr'.regs y)
    (hsites : ∀ y, Avail (wfData g gi) bi k' y →
      LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf ((ccOf fi gi cert norm).eg y)) (bi, k))
    (hdefd : ∀ t, Fact.defd t ∈ S → (TV f cert syms fr t).isSome)
    (hb : fr'.body = st :: rest) (hgs : GPreStmt (ccOf fi gi cert norm) (bi, k) S st) :
    ∃ fr1, lstep fr' m = .next fr1 m ∧ fr1.body = rest ∧ fr1.term = fr'.term ∧
      fr1.slots = fr'.slots ∧ fr1.func = fr'.func ∧
      Inv g (wfData g gi) syms fr1 bi (k' + 1) ∧
      (∀ y, Avail (wfData g gi) bi (k' + 1) y →
        TV f cert syms fr ((ccOf fi gi cert norm).eg y) = fr1.regs y) ∧
      (∀ y, Avail (wfData g gi) bi (k' + 1) y →
        LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf ((ccOf fi gi cert norm).eg y)) (bi, k)) := by
  rcases hgs with hn | ⟨-, hp, t, hpo, hpart⟩
  · -- `nop`: nothing is bound
    have hev : evalInst fr' m st.inst = .ok ([], m) := by rw [hn]; rfl
    have hlen := results_len H hinv hb hev
    refine gStep H hinv hb (fun fn args h => by rw [hn] at h; cases h) hev
      (fun h => by rw [hn] at h; simp [isPure] at h) hagree hsites fun n r hr => ?_
    have := (List.getElem?_eq_some_iff.1 hr).1
    simp only [List.length_nil] at hlen
    omega
  · -- a pure statement: its term's value
    have hW := H.wfg
    obtain ⟨gb, hgb, hbody, -, -⟩ := hinv.block
    have hb' := hb
    rw [hbody] at hb'
    obtain ⟨hst, -, -⟩ := drop_eq_cons hb'
    have hops : ∀ x ∈ operands st.inst, Avail (wfData g gi) bi k' x :=
      hW.uses bi gb hgb k' st hst
    have hgl : fr.func.globals = fr'.func.globals := by
      rw [hinvf.func, hinv.func]; exact H.ok.globals.symm
    have hex : fr.func.externs = fr'.func.externs := by
      rw [hinvf.func, hinv.func]; exact H.ok.externs.symm
    have hTV : TV f cert syms fr t = evalNode fr' (symMem syms) st.inst := by
      rcases hpo.node with hnode | ⟨hsome, hnorm⟩
      · have hnode' : cert.tms[t]? = some (.node (mapOperands (ccOf fi gi cert norm).eg st.inst)) :=
          hnode
        have hok := CC.tmsOk_get (c := ccOf fi gi cert norm) H.ok.tms hnode'
        exact tmVal_mapOperands hnode'
          (fun x hx => (CC.tmOk_node hok _ (by
            rw [operands_mapOperands]; exact List.mem_map_of_mem hx)).1)
          hgl hex hsl.symm (fun x hx => hagree x (hops x hx))
      · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hsome
        rw [hx] at hnorm
        have hx' : norm cert.tms (mapOperands (ccOf fi gi cert norm).eg st.inst) = some x := hx
        have ht : cert.tms[t]? = some x := hnorm.symm
        show tmVal f cert.tms fr (symMem syms) t = _
        rw [H.norm _ _ x hx' f fr (symMem syms) t ht]
        exact evalNode_rename hgl hex hsl.symm (fun x hx => hagree x (hops x hx))
    have hval : ∃ v, evalNode fr' (symMem syms) st.inst = some v ∧
        evalInst fr' m st.inst = .ok ([v], m) := by
      cases hq : partialK st.inst
      · obtain ⟨v, hv⟩ := evalInst_pureK_totalM (f := g) (tm := (wfData g gi).tm) hp hq
          (hW.pure bi gb hgb k' st hst) hpo.typed (by rw [hinv.func])
          (fun x hx => hinv.regs x (hops x hx)) hinv.slots
        refine ⟨v, ?_, hv⟩
        rw [evalNode_pureK_syms (m := m) hp (by rw [hm]; rfl), evalNode_eq_val1, hv]
        rfl
      · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hdefd t (hpart hq))
        rw [hTV] at hv
        refine ⟨v, hv, evalInst_of_evalNode hp ?_⟩
        rw [evalNode_pureK_syms (m := symMem syms) hp hm]
        exact hv
    obtain ⟨v, hv1, hv2⟩ := hval
    refine gStep H hinv hb (pureK_not_call hp) hv2 (fun _ => ⟨v, rfl, hv1⟩) hagree hsites
      fun n r hr => ?_
    have hn0 : n = 0 := by
      have := (List.getElem?_eq_some_iff.1 hr).1
      rw [hpo.res] at this
      omega
    subst hn0
    rw [hpo.term r (List.mem_of_getElem? hr)]
    exact ⟨by rw [hTV, hv1]; rfl, H.le_sound hpo.site⟩

/-- A run of checked prefix statements. -/
theorem gPre_run_list (H : Hyp f g fi gi cert norm) {syms : String → Option Nat} {bi k : Nat}
    {S : List Fact} {fr : Frame} {m : Mem} (hm : m.symbols = syms)
    (hinvf : Inv f (wfData f fi) syms fr bi k)
    (hdefd : ∀ t, Fact.defd t ∈ S → (TV f cert syms fr t).isSome) (rest : List Stmt) :
    ∀ (pre : List Stmt) (fr' : Frame) (k' : Nat),
      Inv g (wfData g gi) syms fr' bi k' → fr'.slots = fr.slots →
      (∀ y, Avail (wfData g gi) bi k' y →
        TV f cert syms fr ((ccOf fi gi cert norm).eg y) = fr'.regs y) →
      (∀ y, Avail (wfData g gi) bi k' y →
        LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf ((ccOf fi gi cert norm).eg y)) (bi, k)) →
      fr'.body = pre ++ rest → (∀ st ∈ pre, GPreStmt (ccOf fi gi cert norm) (bi, k) S st) →
      ∃ fr'', LStar fr' m fr'' m ∧ fr''.body = rest ∧ fr''.term = fr'.term ∧
        fr''.slots = fr'.slots ∧ fr''.func = fr'.func ∧
        Inv g (wfData g gi) syms fr'' bi (k' + pre.length) ∧
        (∀ y, Avail (wfData g gi) bi (k' + pre.length) y →
          TV f cert syms fr ((ccOf fi gi cert norm).eg y) = fr''.regs y) ∧
        (∀ y, Avail (wfData g gi) bi (k' + pre.length) y →
          LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf ((ccOf fi gi cert norm).eg y)) (bi, k))
  | [], fr', k', hinv, _, ha, hs, hb, _ =>
    ⟨fr', .refl _ _, by simpa using hb, rfl, rfl, rfl, hinv, ha, hs⟩
  | st :: pre, fr', k', hinv, hsl, ha, hs, hb, hpre => by
    obtain ⟨fr1, hstep, hb1, ht1, hsl1, hf1, hinv1, ha1, hs1⟩ :=
      gStmt H hm hinvf hinv hsl ha hs hdefd (by rw [hb]; rfl) (hpre st (by simp))
    obtain ⟨fr'', hstar, hb2, ht2, hsl2, hf2, hinv2, ha2, hs2⟩ :=
      gPre_run_list H hm hinvf hdefd rest pre fr1 (k' + 1) hinv1 (by rw [hsl1, hsl]) ha1 hs1 hb1
        (fun s hs' => hpre s (by simp [hs']))
    have hk : k' + 1 + pre.length = k' + (st :: pre).length := by simp; omega
    rw [hk] at hinv2 ha2 hs2
    exact ⟨fr'', .step hstep hstar, hb2, by rw [ht2, ht1], by rw [hsl2, hsl1], by rw [hf2, hf1],
      hinv2, ha2, hs2⟩

/-- **`g` runs its checked pure prefix** (`GPreRun`, module doc). -/
theorem gPre_run (H : Hyp f g fi gi cert norm) : GPreRun f g fi gi cert norm := by
  intro syms bi k k' k'' S fr fr' m rest hm hinvf hinv hsl ha hs hdefd hg
  obtain ⟨pre, hgs, hk, hpre, -⟩ := gPre_spec fr'.body k' rest k'' hg
  subst hk
  exact gPre_run_list H hm hinvf hdefd rest pre fr' k' hinv hsl ha hs hgs hpre

end

end Opt.MidVal
