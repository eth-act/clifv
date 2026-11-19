import FV.Opt.Proof.MidValRel

/-!
# The mid-end validator: a matched skeleton statement (#1119, module (5), slice D)

`rel_matched`: from `Rel … bi k k' S fr fr' m`, a skeleton statement `st` of `f` that the walk
matched with `g`'s next skeleton statement `t` (`Matched`). `g` first runs its checked pure
prefix (`GPreRun`), reaching `t` (`matched_ctx`); then both execute the same instruction on equal
operand values: through the term frame both evaluations are the evaluation of the common term
instruction `mapOperands c.ef st.inst = mapOperands c.eg t.inst` (`MCtx.eval`, `MCtx.call`), so
they have the same results, memory and trap (up to `stuck` messages). The results are the atoms
`res bi k j` on both sides, so after binding the same values every value of both functions keeps
its term's value (`rel_bind`).

The facts after the statement (`afterKeep`, `facts_next`): the old facts keep holding (a writer
removes the memory facts, every other instruction keeps memory: `evalInst_mem_of_not_writer`), a
load adds its location (`holds_of_evalInst_load`), a store its location (`holds_of_evalInst_store`),
an idempotent trapping instruction its evaluation (`evalInst_mergeK`, `evalInst_rename`). After a
call (`ContM`) the memory is arbitrary, and only the non-memory facts are left (`kill`).
A `call_indirect` never occurs in a function `Opt.check` accepts (`no_callIndirect`: it has no
result types without signature declarations).
-/

namespace Opt.MidVal

open Clif

/-! ## Instruction kinds through operand renaming -/

theorem mapOperands_eq_call {σ : ValueId → ValueId} {i : Inst} {fn : FnRef} {args : List ValueId}
    (h : mapOperands σ i = .call fn args) : ∃ a, i = .call fn a ∧ args = a.map σ := by
  cases i <;> simp [mapOperands] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, rfl, rfl⟩

theorem not_call_of_mapOperands {σ τ : ValueId → ValueId} {i j : Inst}
    (h : mapOperands σ i = mapOperands τ j) (hc : ∀ fn args, i ≠ .call fn args) :
    ∀ fn args, j ≠ .call fn args := by
  rintro fn args rfl
  obtain ⟨a, rfl, -⟩ := mapOperands_eq_call h
  exact hc fn a rfl

theorem mergeK_mapOperands (σ : ValueId → ValueId) (i : Inst) :
    mergeK (mapOperands σ i) = mergeK i := by
  cases i <;> rfl

theorem writerK_mapOperands (σ : ValueId → ValueId) (i : Inst) :
    writerK (mapOperands σ i) = writerK i := by
  cases i <;> rfl

theorem isPure_of_pureK {i : Inst} (h : pureK i = false) : isPure i = false := by
  simp only [pureK, Bool.or_eq_false_iff] at h
  exact h.1

/-- An idempotent trapping instruction has at most one result. -/
theorem resultTypes_mergeK_len {i : Inst} (hk : mergeK i = true) {s : FnRef → Option Signature}
    {d : Nat → Option Signature} {ts : List Ty} (h : i.resultTypes s d = some ts) : ts.length ≤ 1 := by
  cases i <;> simp [mergeK] at hk
  case float op ty args =>
    rcases hk with rfl | rfl <;>
      (simp only [Inst.resultTypes, Option.some.injEq] at h; subst h; simp)
  all_goals (simp only [Inst.resultTypes, Option.some.injEq] at h; subst h; simp)

/-- Instructions other than the writers keep memory. -/
theorem evalInst_mem_of_not_writer {fr : Frame} {m m1 : Mem} {i : Inst} {vs : List Val}
    (hw : writerK i = false) (h : evalInst fr m i = .ok (vs, m1)) : m1 = m := by
  by_cases hr : removable i = true
  · exact (evalInst_removable hr).1 _ _ h
  by_cases hp : pureK i = true
  · exact pureK_mem hp h
  by_cases hk : mergeK i = true
  · exact ((evalInst_mergeK hk).1 _ _ h).1
  cases i
  case load op ty fl p off =>
    cases hpv : fr.get p with
    | ok pv => exact (holds_of_evalInst_load h hpv).1
    | trap c => simp only [evalInst, hpv, Res.trap_bind, reduceCtorEq] at h
    | stuck s => simp only [evalInst, hpv, Res.stuck_bind, reduceCtorEq] at h
  case selectSpectreGuard ty c x y =>
    simp only [evalInst, Res.bind_eq_ok, Res.pure_eq_ok, Prod.mk.injEq] at h
    obtain ⟨_, _, _, _, _, _, _, h⟩ := h
    exact h.symm
  case float op ty args =>
    exfalso
    cases op <;> simp [pureK, mergeK, isPure] at hp hk
  all_goals simp [writerK, removable, isPure, pureK, mergeK] at hw hr hp hk

/-- The cases of a fact after a matched statement. -/
theorem mem_afterKeep {i : Inst} {r : Option Nat} {S : List Fact} {F : Fact}
    (h : F ∈ afterKeep i r S) :
    (mergeK i = true ∧ F = .eqn i r) ∨ memFact? r i = some F ∨
      (F ∈ S ∧ (writerK i = true → F.isMem = false)) := by
  have hS : ∀ F, F ∈ (if writerK i then kill S else S) →
      F ∈ S ∧ (writerK i = true → F.isMem = false) := by
    intro F hF
    by_cases hw : writerK i = true
    · simp only [hw, ↓reduceIte] at hF
      simp only [kill, List.mem_filter, Bool.not_eq_true'] at hF
      exact ⟨hF.1, fun _ => hF.2⟩
    · simp only [hw, Bool.false_eq_true, ↓reduceIte] at hF
      exact ⟨hF, fun h' => absurd h' hw⟩
  by_cases hk : mergeK i = true
  · cases hm : memFact? r i with
    | none =>
      simp only [afterKeep, hm, hk, ite_true, List.mem_cons] at h
      rcases h with rfl | h
      · exact .inl ⟨hk, rfl⟩
      · exact .inr (.inr (hS F h))
    | some F' =>
      simp only [afterKeep, hm, hk, ite_true, List.mem_cons] at h
      rcases h with rfl | rfl | h
      · exact .inl ⟨hk, rfl⟩
      · exact .inr (.inl rfl)
      · exact .inr (.inr (hS F h))
  · have hk' : mergeK i = false := by simpa using hk
    cases hm : memFact? r i with
    | none =>
      simp only [afterKeep, hm, hk', Bool.false_eq_true, ite_false] at h
      exact .inr (.inr (hS F h))
    | some F' =>
      simp only [afterKeep, hm, hk', Bool.false_eq_true, ite_false, List.mem_cons] at h
      rcases h with rfl | h
      · exact .inr (.inl rfl)
      · exact .inr (.inr (hS F h))

theorem memFact?_mapOperands {σ : ValueId → ValueId} {r : Option Nat} {i : Inst} {F : Fact}
    (h : memFact? r (mapOperands σ i) = some F) :
    (∃ op ty fl p off v, i = .load op ty fl p off ∧ r = some v ∧
      F = .mem (σ p) off ty (loadKind op) fl.endianness v) ∨
    (∃ op ty fl x p off, i = .store op ty fl x p off ∧
      F = .mem (σ p) off ty (storeKind op) fl.endianness (σ x)) := by
  cases i <;> simp [mapOperands, memFact?] at h
  · obtain ⟨v, rfl, rfl⟩ := h
    exact .inl ⟨_, _, _, _, _, v, rfl, rfl, rfl⟩
  · subst h
    exact .inr ⟨_, _, _, _, _, _, rfl, rfl⟩

/-! ## Results and their atoms -/

/-- With `resOk`, the value bound to result `j` is `vals[j]` (no other result shares its id). -/
theorem resVal {c : CC} {env : ValueId → Nat} {rs : List ValueId} {bi k : Nat}
    (hr : c.resOk env rs bi k = true) {r0 regs : Regs} {vals : List Val}
    (hset : r0.setMany rs vals = some regs) :
    ∀ (j : Nat) (x : ValueId), rs[j]? = some x → regs x = vals[j]? := by
  intro j x hj
  obtain ⟨n, hn, hx⟩ := ((setMany_spec hset).2 x).2 (List.mem_of_getElem? hj)
  have h1 := resOk_spec hr j x hj
  rw [resOk_spec hr n x hn] at h1
  simp only [Option.some.injEq, Tm.res.injEq, true_and] at h1
  rw [← h1]
  exact hx

/-- The value of a result atom `res bi k j`: the register of result `j` of statement `k`. -/
theorem TV_res {f : Function} {cert : Cert} {syms : String → Option Nat} {fr0 : Frame} {u : Nat}
    {bi k j : Nat} {fb : Block} {st : Stmt} {x : ValueId}
    (htm : cert.tms[u]? = some (.res bi k j)) (hfb : f.blocks[bi]? = some fb)
    (hst : fb.body[k]? = some st) (hx : st.results[j]? = some x) :
    TV f cert syms fr0 u = fr0.regs x := by
  show tmVal f cert.tms fr0 (symMem syms) u = _
  rw [tmVal_atom htm (fun _ h => by cases h)]
  simp [atomVal, hfb, hst, hx]

/-- A `call_indirect` has no result types without signature declarations, so `Opt.check`
rejects it. -/
theorem no_callIndirect {f : Function} {W : WfData} (hW : Wf f W) {bi k : Nat} {fb : Block}
    {st : Stmt} (hfb : f.blocks[bi]? = some fb) (hst : fb.body[k]? = some st) {sig : Nat}
    {callee : ValueId} {args : List ValueId} (h : st.inst = .callIndirect sig callee args) : False := by
  obtain ⟨ts, hts, -⟩ := hW.results bi fb hfb k st hst
  rw [h] at hts
  simp [Inst.resultTypes] at hts

theorem callArgs_ren {σ : ValueId → ValueId} {fr fr' : Frame} {fn : FnRef} {args : List ValueId}
    (hext : fr'.func.externs = fr.func.externs) (h : ∀ x ∈ args, fr'.regs (σ x) = fr.regs x) :
    (callArgs fr' fn (args.map σ)).norm = (callArgs fr fn args).norm := by
  simp only [callArgs, Function.extern?, hext, Res.norm_bind, Res.norm_ofOption, checkTys,
    Res.norm_check, Res.norm_pure, getMany_rename h]

section
variable {f g : Function} {fi gi : Info} {cert : Cert} {norm : Norm}

/-! ## `g` at its matched statement -/

/-- What holds once `g` has run its pure prefix up to the statement `t` matched with `f`'s `st`
(statement `k` of `f`'s block `fb`, `k''` of `g`'s `gb`). -/
structure MCtx (f g : Function) (fi gi : Info) (cert : Cert) (norm : Norm)
    (syms : String → Option Nat) (bi k k'' : Nat) (fr fr2 : Frame) (st t : Stmt)
    (rest ts : List Stmt) (fb gb : Block) : Prop where
  hfb : f.blocks[bi]? = some fb
  hgb : g.blocks[bi]? = some gb
  stk : fb.body[k]? = some st
  tk : gb.body[k'']? = some t
  dropF : fb.body.drop (k + 1) = rest
  dropG : gb.body.drop (k'' + 1) = ts
  bodyF : fr.body = st :: rest
  bodyG : fr2.body = t :: ts
  funcF : fr.func = f
  funcG : fr2.func = g
  slots : fr2.slots = fr.slots
  invg : Inv g (wfData g gi) syms fr2 bi k''
  agreeG : ∀ y, Avail (wfData g gi) bi k'' y →
    TV f cert syms fr ((ccOf fi gi cert norm).eg y) = fr2.regs y
  sitesG : ∀ y, Avail (wfData g gi) bi k'' y →
    LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf ((ccOf fi gi cert norm).eg y)) (bi, k)
  pureG : pureK t.inst = false

theorem matched_ctx (hrun : GPreRun f g fi gi cert norm)
    {syms : String → Option Nat} {bi k k' : Nat} {S : List Fact} {fr fr' : Frame} {m : Mem}
    {st : Stmt} {rest : List Stmt} {t : Stmt} {ts : List Stmt} {k'' : Nat}
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m) (hm : m.symbols = syms)
    (hb : fr.body = st :: rest)
    (hM : Matched (ccOf fi gi cert norm) bi st fr'.body k k' S t ts k'') :
    ∃ fr2 fb gb, LStar fr' m fr2 m ∧
      MCtx f g fi gi cert norm syms bi k k'' fr fr2 st t rest ts fb gb := by
  obtain ⟨fr2, hst, hbody, -, hsl, -, hinv, hag, hsg⟩ :=
    hrun hm hR.invf hR.invg hR.slots hR.agreeG hR.sitesG (fun t ht => hR.facts _ ht) hM.pre
  obtain ⟨fb, hfb, hfbody, -, -⟩ := hR.invf.block
  obtain ⟨gb, hgb, hgbody, -, -⟩ := hinv.block
  have hb' := hb
  have hbody' := hbody
  rw [hfbody] at hb'
  rw [hgbody] at hbody'
  obtain ⟨hstk, hdf, -⟩ := drop_eq_cons hb'
  obtain ⟨htk, hdg, -⟩ := drop_eq_cons hbody'
  obtain ⟨pre, -, -, -, hsk⟩ := gPre_spec _ _ _ _ hM.pre
  exact ⟨fr2, fb, gb, hst, hfb, hgb, hstk, htk, hdf, hdg, hb, hbody, hR.invf.func, hinv.func,
    hsl.trans hR.slots, hinv, hag, hsg, (show t.inst ≠ .nop ∧ pureK t.inst = false from hsk).2⟩

variable {syms : String → Option Nat} {bi k k' k'' : Nat} {S : List Fact} {fr fr' fr2 : Frame}
  {m : Mem} {st t : Stmt} {rest ts : List Stmt} {fb gb : Block}

/-- Both statements evaluate alike (the common term instruction, `evalInst_rename`). -/
theorem MCtx.eval (H : Hyp f g fi gi cert norm)
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m)
    (hC : MCtx f g fi gi cert norm syms bi k k'' fr fr2 st t rest ts fb gb)
    (hops : mapOperands (ccOf fi gi cert norm).ef st.inst = mapOperands (ccOf fi gi cert norm).eg t.inst)
    (mem : Mem) :
    (evalInst fr2 mem t.inst).norm = (evalInst fr mem st.inst).norm := by
  have h1 := evalInst_rename (σ := (ccOf fi gi cert norm).ef) (fr := fr)
    (fr' := tmFrame f cert.tms fr (symMem syms)) (mem := mem) rfl rfl rfl
    (fun x hx => hR.agreeF x (H.wff.uses bi fb hC.hfb k st hC.stk x hx))
  have h2 := evalInst_rename (σ := (ccOf fi gi cert norm).eg) (fr := fr2)
    (fr' := tmFrame f cert.tms fr (symMem syms)) (mem := mem)
    (by show fr.func.globals = fr2.func.globals; rw [hC.funcF, hC.funcG, H.ok.globals])
    (by show fr.func.externs = fr2.func.externs; rw [hC.funcF, hC.funcG, H.ok.externs])
    (by show fr.slots = fr2.slots; exact hC.slots.symm)
    (fun y hy => hC.agreeG y (H.wfg.uses bi gb hC.hgb k'' t hC.tk y hy))
  rw [← h2, ← hops, h1]

/-- A matched call: the same callee, and the arguments evaluate alike. -/
theorem MCtx.call (H : Hyp f g fi gi cert norm)
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m)
    (hC : MCtx f g fi gi cert norm syms bi k k'' fr fr2 st t rest ts fb gb)
    (hops : mapOperands (ccOf fi gi cert norm).ef st.inst = mapOperands (ccOf fi gi cert norm).eg t.inst)
    {fn : FnRef} {args : List ValueId} (hc : st.inst = .call fn args) :
    ∃ a, t.inst = .call fn a ∧ (callArgs fr2 fn a).norm = (callArgs fr fn args).norm := by
  rw [hc] at hops
  obtain ⟨a, hta, hmap⟩ := mapOperands_eq_call hops.symm
  refine ⟨a, hta, ?_⟩
  have h1 := callArgs_ren (σ := (ccOf fi gi cert norm).ef) (fr := fr)
    (fr' := tmFrame f cert.tms fr (symMem syms)) (fn := fn) (args := args) rfl
    (fun x hx => hR.agreeF x (H.wff.uses bi fb hC.hfb k st hC.stk x (by rw [hc]; exact hx)))
  have h2 := callArgs_ren (σ := (ccOf fi gi cert norm).eg) (fr := fr2)
    (fr' := tmFrame f cert.tms fr (symMem syms)) (fn := fn) (args := a)
    (by show fr.func.externs = fr2.func.externs; rw [hC.funcF, hC.funcG, H.ok.externs])
    (fun y hy => hC.agreeG y (H.wfg.uses bi gb hC.hgb k'' t hC.tk y (by rw [hta]; exact hy)))
  rw [← h2, ← hmap, h1]

/-! ## The relation after binding the results -/

/-- Binding the same values to the results of both statements gives the relation at the next
positions, for any facts `S'` that hold there with sites up to `(bi, k + 1)`. -/
theorem rel_bind (H : Hyp f g fi gi cert norm) {S' Send : List Fact} {m1 : Mem} {vals : List Val}
    {regs regs' : Regs}
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m)
    (hC : MCtx f g fi gi cert norm syms bi k k'' fr fr2 st t rest ts fb gb)
    (hpF : pureK st.inst = false) (hlen : st.results.length = t.results.length)
    (hrF : (ccOf fi gi cert norm).resOk (ccOf fi gi cert norm).ef st.results bi k = true)
    (hrG : (ccOf fi gi cert norm).resOk (ccOf fi gi cert norm).eg t.results bi k = true)
    (hwk : (ccOf fi gi cert norm).walk bi rest ts (k + 1) (k'' + 1) S' = some Send)
    (hend : EndOk (ccOf fi gi cert norm) bi fb gb Send)
    (htyF : ∀ ts0, st.inst.resultTypes (sigOf f) (fun _ => none) = some ts0 →
      vals.map (·.ty) = ts0)
    (htyG : ∀ ts0, t.inst.resultTypes (sigOf g) (fun _ => none) = some ts0 →
      vals.map (·.ty) = ts0)
    (hset : fr.regs.setMany st.results vals = some regs)
    (hset' : fr2.regs.setMany t.results vals = some regs')
    (hF : ∀ F ∈ S', FactHolds f cert syms { fr with regs, body := rest } m1 F)
    (hFs : ∀ F ∈ S', ∀ u ∈ F.terms,
      LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf u) (bi, k + 1)) :
    Rel f g fi gi cert norm syms bi (k + 1) (k'' + 1) S' { fr with regs, body := rest }
      { fr2 with regs := regs', body := ts } m1 := by
  have hipF : isPure st.inst = false := isPure_of_pureK hpF
  have hipG : isPure t.inst = false := isPure_of_pureK hC.pureG
  have hreg : ∀ v, Avail (wfData f fi) bi k v → regs v = fr.regs v := fun v hv =>
    ((setMany_spec hset).2 v).1 (avail_not_result H.wff hC.hfb hC.stk hv)
  have hreg' : ∀ v, Avail (wfData g gi) bi k'' v → regs' v = fr2.regs v := fun v hv =>
    ((setMany_spec hset').2 v).1 (avail_not_result H.wfg hC.hgb hC.tk hv)
  have hTV : ∀ u, LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf u) (bi, k) →
      TV f cert syms { fr with regs, body := rest } u = TV f cert syms fr u :=
    fun u hu => H.TV_stable (fr1 := fr) (fr2 := { fr with regs, body := rest }) rfl rfl rfl hreg hu
  refine ⟨⟨fb, gb, Send, hC.hfb, hC.hgb, by rw [hC.dropF, hC.dropG]; exact hwk, hend⟩,
    Inv.results H.wff hR.invf hC.bodyF htyF (fun h => absurd h (by simp [hipF])) hset,
    Inv.results H.wfg hC.invg hC.bodyG htyG (fun h => absurd h (by simp [hipG])) hset',
    hC.slots, ?_, ?_, ?_, hF, hFs⟩
  · intro x hx
    rcases avail_succ H.wff hC.hfb hC.stk hx with hr | hx'
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hr
      exact TV_res (resOk_spec hrF j x hj) hC.hfb hC.stk hj
    · show TV f cert syms _ _ = regs x
      rw [hTV _ (H.siteF hx'), hR.agreeF x hx', hreg x hx']
  · intro y hy
    rcases avail_succ H.wfg hC.hgb hC.tk hy with hr | hy'
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hr
      have hjl : j < st.results.length := by
        rw [hlen]; exact (List.getElem?_eq_some_iff.1 hj).1
      obtain ⟨x, hx⟩ : ∃ x, st.results[j]? = some x := ⟨_, List.getElem?_eq_getElem hjl⟩
      rw [TV_res (cert := cert) (resOk_spec hrG j y hj) hC.hfb hC.stk hx]
      show regs x = regs' y
      rw [resVal hrF hset j x hx, resVal hrG hset' j y hj]
    · show TV f cert syms _ _ = regs' y
      rw [hTV _ (hC.sitesG y hy'), hC.agreeG y hy', hreg' y hy']
  · intro y hy
    rcases avail_succ H.wfg hC.hgb hC.tk hy with hr | hy'
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hr
      have hs := CC.tmOk_atom (s := (bi, k + 1))
        (CC.tmsOk_get H.ok.tms (resOk_spec hrG j y hj)) rfl
      rw [hs]
      exact LeP.refl _ _
    · exact (hC.sitesG y hy').mono (Nat.le_succ k)

/-! ## The facts after a statement that is not a call -/

theorem facts_next (H : Hyp f g fi gi cert norm) {m1 : Mem} {vals : List Val} {regs : Regs}
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m)
    (hfb : f.blocks[bi]? = some fb) (hstk : fb.body[k]? = some st)
    (hrF : (ccOf fi gi cert norm).resOk (ccOf fi gi cert norm).ef st.results bi k = true)
    (he : evalInst fr m st.inst = .ok (vals, m1))
    (hset : fr.regs.setMany st.results vals = some regs) :
    ∀ F ∈ afterKeep (mapOperands (ccOf fi gi cert norm).ef st.inst)
        (st.results.head?.map (ccOf fi gi cert norm).ef) S,
      FactHolds f cert syms { fr with regs, body := rest } m1 F ∧
        ∀ u ∈ F.terms, LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf u) (bi, k + 1) := by
  have hreg : ∀ v, Avail (wfData f fi) bi k v → regs v = fr.regs v := fun v hv =>
    ((setMany_spec hset).2 v).1 (avail_not_result H.wff hfb hstk hv)
  have hTV : ∀ u, LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf u) (bi, k) →
      TV f cert syms { fr with regs, body := rest } u = TV f cert syms fr u :=
    fun u hu => H.TV_stable (fr1 := fr) (fr2 := { fr with regs, body := rest }) rfl rfl rfl hreg hu
  have hops := H.wff.uses bi fb hfb k st hstk
  have hopTV : ∀ x ∈ operands st.inst,
      TV f cert syms { fr with regs, body := rest } ((ccOf fi gi cert norm).ef x) = fr.regs x :=
    fun x hx => by rw [hTV _ (H.siteF (hops x hx))]; exact hR.agreeF x (hops x hx)
  have hopSite : ∀ x ∈ operands st.inst,
      LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf ((ccOf fi gi cert norm).ef x)) (bi, k + 1) :=
    fun x hx => (H.siteF (hops x hx)).mono (Nat.le_succ k)
  have hresSite : ∀ x ∈ st.results,
      LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf ((ccOf fi gi cert norm).ef x)) (bi, k + 1) :=
    fun x hx => H.siteF ⟨bi, k + 1, site_result H.wff hfb hstk hx, .inl ⟨rfl, Nat.le_refl _⟩⟩
  have hresTV : ∀ (j : Nat) (x : ValueId), st.results[j]? = some x →
      TV f cert syms { fr with regs, body := rest } ((ccOf fi gi cert norm).ef x) = vals[j]? :=
    fun j x hj => by
      rw [TV_res (cert := cert) (resOk_spec hrF j x hj) hfb hstk hj]; exact resVal hrF hset j x hj
  have hget : ∀ x ∈ operands st.inst, ∃ v, fr.get x = .ok v ∧ fr.regs x = some v := by
    intro x hx
    obtain ⟨a, ha, -⟩ := hR.invf.regs x (hops x hx)
    exact ⟨a, by simp [Frame.get, ha], ha⟩
  intro F hF
  rcases mem_afterKeep hF with ⟨hk, rfl⟩ | hmf | ⟨hS, hw⟩
  · -- an idempotent trapping instruction: its evaluation
    have hk' : mergeK st.inst = true := by rwa [mergeK_mapOperands] at hk
    obtain ⟨-, hall⟩ := (evalInst_mergeK hk').1 vals m1 he
    have hren := evalInst_rename (σ := (ccOf fi gi cert norm).ef) (fr := fr)
      (fr' := tmFrame f cert.tms { fr with regs, body := rest } (symMem syms))
      (mem := symMem syms) rfl rfl rfl hopTV
    have hE := Res.norm_eq_ok hren (hall (symMem syms))
    obtain ⟨ts0, hts0, hl0, -⟩ := H.wff.results bi fb hfb k st hstk
    have hle := resultTypes_mergeK_len hk' hts0
    have hlv := (setMany_spec hset).1
    refine ⟨?_, ?_⟩
    · cases hres : st.results with
      | nil =>
        rw [hres] at hlv
        have hv0 : vals = [] := List.eq_nil_of_length_eq_zero hlv.symm
        subst hv0
        exact hE
      | cons x xs =>
        rw [hres] at hlv hl0
        cases xs with
        | cons _ _ => simp only [List.length_cons] at hl0; omega
        | nil =>
          obtain ⟨v, rfl⟩ : ∃ v, vals = [v] := by
            rcases vals with _ | ⟨v, _ | ⟨w, ws⟩⟩
            · simp at hlv
            · exact ⟨v, rfl⟩
            · simp at hlv
          exact ⟨v, by rw [hresTV 0 x (by simp [hres])]; rfl, hE⟩
    · intro u hu
      simp only [Fact.terms, List.mem_append, operands_mapOperands, List.mem_map] at hu
      rcases hu with ⟨x, hx, rfl⟩ | hu
      · exact hopSite x hx
      · cases hres : st.results with
        | nil => rw [hres] at hu; simp at hu
        | cons x xs =>
          rw [hres] at hu
          simp only [List.head?_cons, Option.map_some, Option.toList_some,
            List.mem_singleton] at hu
          subst hu
          exact hresSite x (by rw [hres]; exact List.mem_cons_self ..)
  · rcases memFact?_mapOperands hmf with ⟨op, ty, fl, p, off, v, hi, hr, rfl⟩ |
      ⟨op, ty, fl, x, p, off, hi, rfl⟩
    · -- a load: its location holds its result
      have hp : p ∈ operands st.inst := by rw [hi]; simp [operands]
      obtain ⟨pv, hgp, hpv⟩ := hget p hp
      rw [hi] at he
      obtain ⟨hm1, v', hvs, hh⟩ := holds_of_evalInst_load he hgp
      cases hres : st.results with
      | nil => rw [hres] at hr; cases hr
      | cons x xs =>
        rw [hres] at hr
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hr
        subst hr
        have h0 : st.results[0]? = some x := by simp [hres]
        refine ⟨⟨pv, v', by rw [hopTV p hp, hpv], by rw [hresTV 0 x h0, hvs]; rfl,
          by rw [hm1]; exact hh⟩, ?_⟩
        intro u hu
        simp only [Fact.terms, List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact hopSite p hp
        · exact hresSite x (by rw [hres]; exact List.mem_cons_self ..)
    · -- a store: its location holds the stored value
      have hx : x ∈ operands st.inst := by rw [hi]; simp [operands]
      have hp : p ∈ operands st.inst := by rw [hi]; simp [operands]
      obtain ⟨xv, hgx, hxv⟩ := hget x hx
      obtain ⟨pv, hgp, hpv⟩ := hget p hp
      rw [hi] at he
      obtain ⟨-, hh⟩ := holds_of_evalInst_store he hgx hgp
      refine ⟨⟨pv, xv, by rw [hopTV p hp, hpv], by rw [hopTV x hx, hxv], hh⟩, ?_⟩
      intro u hu
      simp only [Fact.terms, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact hopSite p hp
      · exact hopSite x hx
  · -- an old fact: a memory fact survives only instructions that keep memory
    refine ⟨FactHolds.stable (fr1 := fr) (fr2 := { fr with regs, body := rest }) (m1 := m)
      (m2 := m1) H rfl rfl rfl hreg (hR.factSites F hS)
      (fun hmem => ?_) (hR.facts F hS),
      fun u hu => (hR.factSites F hS u hu).mono (Nat.le_succ k)⟩
    by_cases hwk : writerK st.inst = true
    · exact absurd hmem (by simp [hw (by rw [writerK_mapOperands]; exact hwk)])
    · exact evalInst_mem_of_not_writer (by simpa using hwk) he

/-! ## The four conjuncts -/

/-- A non-call statement steps to the relation. -/
theorem matched_next (H : Hyp f g fi gi cert norm) {Send : List Fact} {fr1 : Frame} {m1 : Mem}
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m)
    (hC : MCtx f g fi gi cert norm syms bi k k'' fr fr2 st t rest ts fb gb)
    (hp : pureK st.inst = false)
    (hM : Matched (ccOf fi gi cert norm) bi st fr'.body k k' S t ts k'')
    (hcF : ∀ fn args, st.inst ≠ .call fn args)
    (hwk : (ccOf fi gi cert norm).walk bi rest ts (k + 1) (k'' + 1)
      (afterKeep (mapOperands (ccOf fi gi cert norm).ef st.inst)
        (st.results.head?.map (ccOf fi gi cert norm).ef) S) = some Send)
    (hend : EndOk (ccOf fi gi cert norm) bi fb gb Send)
    (hl : lstep fr m = .next fr1 m1) :
    ∃ fr1', LStar fr2 m fr1' m1 ∧ MR f g fi gi cert norm syms fr1 fr1' m1 := by
  have hcG := not_call_of_mapOperands hM.ops hcF
  have htr := MCtx.eval H hR hC hM.ops m
  rw [lstep_inst hC.bodyF hcF] at hl
  cases he : evalInst fr m st.inst with
  | trap c => rw [he] at hl; cases hl
  | stuck s => rw [he] at hl; cases hl
  | ok p =>
    obtain ⟨vals, m1'⟩ := p
    rw [he] at hl
    simp only [LRes.ofRes] at hl
    split at hl
    · rename_i regs hset
      cases hl
      have he' := Res.norm_eq_ok htr he
      obtain ⟨regs', hset'⟩ := setMany_len (r := fr2.regs) (xs := t.results) (vs := vals)
        (hM.len.symm.trans (setMany_spec hset).1)
      have hF := facts_next H hR hC.hfb hC.stk hM.resF he hset (rest := rest)
      refine ⟨{ fr2 with regs := regs', body := ts }, LStar.single ?_, bi, k + 1, k'' + 1, _,
        rel_bind (fr := fr) (fr2 := fr2) (rest := rest) (ts := ts) H hR hC hp hM.len hM.resF
          hM.resG hwk hend (fun _ h0 => evalInst_types he h0)
          (fun _ h0 => evalInst_types he' h0) hset hset' (fun F h => (hF F h).1)
          (fun F h => (hF F h).2)⟩
      rw [lstep_inst hC.bodyG hcG, he']
      simp only [LRes.ofRes, hset']
    · cases hl

/-- A trap of `f`'s statement is a trap of `g`'s. -/
theorem matched_trap (H : Hyp f g fi gi cert norm)
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m)
    (hC : MCtx f g fi gi cert norm syms bi k k'' fr fr2 st t rest ts fb gb)
    (hops : mapOperands (ccOf fi gi cert norm).ef st.inst = mapOperands (ccOf fi gi cert norm).eg t.inst)
    {c' : TrapCode} (hl : lstep fr m = .trap c') : lstep fr2 m = .trap c' := by
  by_cases hc : ∃ fn args, st.inst = .call fn args
  · obtain ⟨fn, args, hc⟩ := hc
    obtain ⟨a, hta, hn⟩ := MCtx.call H hR hC hops hc
    rw [lstep_call hC.bodyF hc] at hl
    rw [lstep_call hC.bodyG hta]
    cases hca : callArgs fr fn args with
    | ok p => obtain ⟨e, v⟩ := p; rw [hca] at hl; cases hl
    | stuck s => rw [hca] at hl; cases hl
    | trap c0 =>
      rw [hca] at hl
      cases hl
      rw [Res.norm_eq_trap hn hca]
      rfl
  · have hcF : ∀ fn args, st.inst ≠ .call fn args := fun fn args h => hc ⟨fn, args, h⟩
    have hcG := not_call_of_mapOperands hops hcF
    rw [lstep_inst hC.bodyF hcF] at hl
    rw [lstep_inst hC.bodyG hcG]
    cases he : evalInst fr m st.inst with
    | ok p =>
      obtain ⟨vals, m1⟩ := p
      rw [he] at hl
      simp only [LRes.ofRes] at hl
      split at hl <;> cases hl
    | stuck s => rw [he] at hl; cases hl
    | trap c0 =>
      rw [he] at hl
      cases hl
      rw [Res.norm_eq_trap (MCtx.eval H hR hC hops m) he]
      rfl

/-- A call of `f` is the same call of `g`; after it returns (any memory with the symbols), the
results are bound alike and the non-memory facts still hold. -/
theorem matched_call (H : Hyp f g fi gi cert norm) {Send : List Fact} {ext : ExtFunc}
    {vals : List Val} {rs : List ValueId} {rest' : List Stmt}
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m)
    (hC : MCtx f g fi gi cert norm syms bi k k'' fr fr2 st t rest ts fb gb)
    (hp : pureK st.inst = false)
    (hM : Matched (ccOf fi gi cert norm) bi st fr'.body k k' S t ts k'')
    (hwk : (ccOf fi gi cert norm).walk bi rest ts (k + 1) (k'' + 1)
      (afterKeep (mapOperands (ccOf fi gi cert norm).ef st.inst)
        (st.results.head?.map (ccOf fi gi cert norm).ef) S) = some Send)
    (hend : EndOk (ccOf fi gi cert norm) bi fb gb Send)
    (hl : lstep fr m = .call ext vals rs rest') :
    rs = st.results ∧ rest' = rest ∧ lstep fr2 m = .call ext vals t.results ts ∧
      ContM syms (MR f g fi gi cert norm syms) { fr with body := rest } st.results
        { fr2 with body := ts } t.results (AbiParam.tys ext.sig.returns) := by
  obtain ⟨st0, fn, args, hst, hc, hrs, hca⟩ := lstep_call_inv hl
  rw [hC.bodyF] at hst
  simp only [List.cons.injEq] at hst
  obtain ⟨h1, h2⟩ := hst
  subst h1 h2 hrs
  obtain ⟨a, hta, hn⟩ := MCtx.call H hR hC hM.ops hc
  have hca' : callArgs fr2 fn a = .ok (ext, vals) := Res.norm_eq_ok hn hca
  have hext : sigOf f fn = some ext.sig := by
    have hca0 := hca
    simp only [callArgs, Res.bind_eq_ok, Res.ofOption_eq_ok] at hca0
    obtain ⟨e, he, _, _, _, _, hpe⟩ := hca0
    simp only [Res.pure_eq_ok, Prod.mk.injEq] at hpe
    obtain ⟨rfl, -⟩ := hpe
    rw [hC.funcF] at he
    simp only [sigOf]
    rw [show f.externs.lookup fn = f.extern? fn from rfl, he]
    rfl
  have hextG : sigOf g fn = some ext.sig := by
    rw [sigOf, H.ok.externs]
    exact hext
  refine ⟨rfl, rfl, by rw [lstep_call hC.bodyG hta, hca']; rfl, ?_⟩
  intro vs regs m' hty _ hset
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr2.regs) (xs := t.results) (vs := vs)
    (hM.len.symm.trans (setMany_spec hset).1)
  have hreg : ∀ v, Avail (wfData f fi) bi k v → regs v = fr.regs v := fun v hv =>
    ((setMany_spec hset).2 v).1 (avail_not_result H.wff hC.hfb hC.stk hv)
  refine ⟨regs', hset', bi, k + 1, k'' + 1, _,
    rel_bind (fr := fr) (fr2 := fr2) (rest := rest) (ts := ts) H hR hC hp hM.len hM.resF hM.resG
      hwk hend (fun ts0 h0 => ?_) (fun ts0 h0 => ?_)
      hset hset' (fun F hF => ?_) (fun F hF => ?_)⟩
  · rw [hc, Inst.resultTypes, hext] at h0
    simp only [Option.map_some, Option.some.injEq] at h0
    rw [← h0, hty]
    rfl
  · rw [hta, Inst.resultTypes, hextG] at h0
    simp only [Option.map_some, Option.some.injEq] at h0
    rw [← h0, hty]
    rfl
  · rcases mem_afterKeep hF with ⟨hk, -⟩ | hmf | ⟨hS, hw⟩
    · rw [hc] at hk; simp [mergeK, mapOperands] at hk
    · rw [hc] at hmf; simp [memFact?, mapOperands] at hmf
    · have hnm : F.isMem = false := hw (by rw [hc]; rfl)
      exact FactHolds.stable (fr1 := fr) (fr2 := { fr with regs, body := rest }) (m1 := m)
        (m2 := m') H rfl rfl rfl hreg (hR.factSites F hS)
        (fun h => absurd h (by simp [hnm])) (hR.facts F hS)
  · intro u hu
    rcases mem_afterKeep hF with ⟨hk, -⟩ | hmf | ⟨hS, -⟩
    · rw [hc] at hk; simp [mergeK, mapOperands] at hk
    · rw [hc] at hmf; simp [memFact?, mapOperands] at hmf
    · exact (hR.factSites F hS u hu).mono (Nat.le_succ k)

end

/-! ## The matched statement -/

theorem rel_matched {f g : Function} {fi gi : Info} {cert : Cert} {norm : Norm}
    (H : Hyp f g fi gi cert norm) (hrun : GPreRun f g fi gi cert norm)
    {syms : String → Option Nat} {bi k k' : Nat} {S : List Fact} {fr fr' : Frame} {m : Mem}
    {st : Stmt} {rest : List Stmt} {t : Stmt} {ts : List Stmt} {k'' : Nat}
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m) (hm : m.symbols = syms)
    (hb : fr.body = st :: rest)
    (hn : st.inst ≠ .nop) (hp : pureK st.inst = false)
    (hM : Matched (ccOf fi gi cert norm) bi st fr'.body k k' S t ts k'')
    (hw : ∃ fb gb Send, f.blocks[bi]? = some fb ∧ g.blocks[bi]? = some gb ∧
      (ccOf fi gi cert norm).walk bi rest ts (k + 1) (k'' + 1)
        (afterKeep (mapOperands (ccOf fi gi cert norm).ef st.inst)
          (st.results.head?.map (ccOf fi gi cert norm).ef) S) = some Send ∧
      EndOk (ccOf fi gi cert norm) bi fb gb Send) :
    (∀ fr1 m1, lstep fr m = .next fr1 m1 →
      ∃ fr1', LStar fr' m fr1' m1 ∧ MR f g fi gi cert norm syms fr1 fr1' m1) ∧
    (∀ c', lstep fr m = .trap c' → ∃ fr2 m2, LStar fr' m fr2 m2 ∧ lstep fr2 m2 = .trap c') ∧
    (∀ ext vals rs rest', lstep fr m = .call ext vals rs rest' →
      ∃ fr2 rs' rest'', LStar fr' m fr2 m ∧ lstep fr2 m = .call ext vals rs' rest'' ∧
        ContM syms (MR f g fi gi cert norm syms) { fr with body := rest' } rs { fr2 with body := rest'' } rs'
          (AbiParam.tys ext.sig.returns)) ∧
    (∀ sig callee args d a vals, st.inst = .callIndirect sig callee args →
      ciArgs fr sig callee args = .ok (d, a, vals) →
      ∃ fr2 st' rest'' sig' callee' args', LStar fr' m fr2 m ∧ fr2.body = st' :: rest'' ∧
        st'.inst = .callIndirect sig' callee' args' ∧ ciArgs fr2 sig' callee' args' = .ok (d, a, vals) ∧
        ContM syms (MR f g fi gi cert norm syms) { fr with body := rest } st.results
          { fr2 with body := rest'' } st'.results (AbiParam.tys d.returns)) := by
  obtain ⟨fr2, fb, gb, hpre, hC⟩ := matched_ctx hrun hR hm hb hM
  obtain ⟨fb', gb', Send, hfb', hgb', hwk, hend⟩ := hw
  obtain rfl := Option.some.inj (hC.hfb.symm.trans hfb')
  obtain rfl := Option.some.inj (hC.hgb.symm.trans hgb')
  refine ⟨fun fr1 m1 hl => ?_, fun c' hl => ⟨fr2, m, hpre, matched_trap H hR hC hM.ops hl⟩,
    fun ext vals rs rest' hl => ?_, fun sig callee args d a vals hi _ => ?_⟩
  · by_cases hc : ∃ fn args, st.inst = .call fn args
    · obtain ⟨fn, args, hc⟩ := hc
      rw [lstep_call hb hc] at hl
      cases hca : callArgs fr fn args with
      | ok p => obtain ⟨e, v⟩ := p; rw [hca] at hl; cases hl
      | trap c => rw [hca] at hl; cases hl
      | stuck s => rw [hca] at hl; cases hl
    · obtain ⟨fr1', h1, h2⟩ := matched_next H hR hC hp hM (fun fn args h => hc ⟨fn, args, h⟩)
        hwk hend hl
      exact ⟨fr1', hpre.trans h1, h2⟩
  · obtain ⟨rfl, rfl, h1, h2⟩ := matched_call H hR hC hp hM hwk hend hl
    exact ⟨fr2, t.results, ts, hpre, h1, h2⟩
  · exact (no_callIndirect H.wff hC.hfb hC.stk hi).elim

end Opt.MidVal
