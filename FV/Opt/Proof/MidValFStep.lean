import FV.Opt.Proof.MidValRel

/-!
# The mid-end validator's simulation: steps of `f` alone (#1119, slice C)

Steps of `f` that `g` does not mirror, from `Rel … bi k k' S fr fr' m` (`FV/Opt/Proof/MidValRel.lean`):

* `rel_nop`: a `nop` (no result, memory kept);
* `rel_pure`: a pure statement checked by `pureOk` (`walk_pure_spec`): it evaluates (totality,
  `evalInst_pureK_total`) or, for a `partialK` node, is `stuck`; its result holds its term's value
  (`PureOk.node`: the node of its operands' terms, or the normaliser's term); a `partialK` node adds
  the fact `defd t`;
* `rel_remove`: a skeleton statement the walk removed (`removeOk_spec`): a load of a location held
  by a memory fact (`evalInst_load_of_holds`), a `notrap` load (its term is the atom `poison bi k`
  of its own result; `evalInst_load_notrap`), a store of the value a location holds
  (`evalInst_store_idem`), an idempotent trapping instruction equal to an evaluated one (`eqn` fact,
  `tmVal_mapOperands_inst`, `evalInst_mergeK`). Each keeps memory and never traps.

All three use `FStep.rel_after`: `f` binds the statement's results (not available at `(bi, k)`), so
the values and facts with sites no later than `(bi, k)` keep their values (`Hyp.TV_stable`,
`FactHolds.stable`), and `Inv.results` gives `f`'s invariant one statement later.
-/

namespace Opt.MidVal

open Clif

variable {f g : Function} {fi gi : Info} {cert : Cert} {norm : Norm}

namespace FStep

/-! ## Instructions -/

theorem evalNode_of_ok {fr : Frame} {m m' : Mem} {i : Inst} {v : Val}
    (h : evalInst fr m i = .ok ([v], m')) : evalNode fr m i = some v := by
  simp only [evalNode, h]

/-- A `pureK` node reads memory only through the link-time symbols. -/
theorem evalNode_pureK_syms {fr : Frame} {m m' : Mem} {i : Inst} (hp : pureK i = true)
    (hs : m'.symbols = m.symbols) : evalNode fr m' i = evalNode fr m i := by
  by_cases hi : isPure i = true
  · exact evalNode_mem hi hs
  · cases hpart : partialK i
    · exact evalNode_pureK_mem hp hpart
    · cases i <;> simp [pureK, isPure, partialK] at hp hi hpart
      all_goals simp only [evalNode_eq_val1, evalInst, val1_bind, val1_pure, hs]
      all_goals (repeat' (first | split | simp only [val1_bind, val1_pure, val1_ok]))
      all_goals simp_all [val1_bind, val1_pure, val1_ok, Res.ofOption]

/-- A partial node (`symbol_value`, `func_addr`, `tls_value`) never traps. -/
theorem partialK_notrap {fr : Frame} {m : Mem} {i : Inst} (hp : partialK i = true) (c : TrapCode) :
    evalInst fr m i ≠ .trap c := by
  cases i <;> simp only [partialK, Bool.false_eq_true] at hp
  case symbolValue ty gv => exact (evalInst_removable (by simp [removable, isPure])).2 c
  case funcAddr ty fn =>
    intro h
    simp [evalInst] at h
  case tlsValue ty gv =>
    intro h
    simp only [evalInst, Res.bind_eq_trap, Res.ofOption_ne_trap, false_or] at h
    obtain ⟨g, -, h⟩ := h
    split at h <;> simp at h

/-- A partial node evaluates to one value keeping memory, or is `stuck`. -/
theorem evalInst_partialK {fr : Frame} {m : Mem} {i : Inst} (hp : partialK i = true) :
    (∃ v, evalInst fr m i = .ok ([v], m)) ∨ ∃ msg, evalInst fr m i = .stuck msg := by
  have hk : pureK i = true := by cases i <;> simp_all [partialK, pureK, isPure]
  have ht : ∃ ty, i.resultTypes (fun _ => none) (fun _ => none) = some [ty] := by
    cases i <;> simp_all [partialK, Inst.resultTypes]
  obtain ⟨ty, ht⟩ := ht
  rcases h : evalInst fr m i with ⟨vs, m'⟩ | c | msg
  · have hm := pureK_mem hk h
    have hv := evalInst_types h ht
    subst hm
    rcases vs with _ | ⟨v, _ | ⟨w, vs⟩⟩
    · simp at hv
    · exact .inl ⟨v, rfl⟩
    · simp at hv
  · exact absurd h (partialK_notrap hp c)
  · exact .inr ⟨msg, rfl⟩

theorem mapOperands_eq_load {σ : ValueId → ValueId} {i : Inst} {op : LoadOp} {ty : Ty}
    {fl : MemFlags} {p : ValueId} {off : Int} (h : mapOperands σ i = .load op ty fl p off) :
    ∃ p0, i = .load op ty fl p0 off ∧ σ p0 = p := by
  cases i <;> simp only [mapOperands, reduceCtorEq, Inst.load.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  exact ⟨_, rfl, rfl⟩

theorem mapOperands_eq_store {σ : ValueId → ValueId} {i : Inst} {op : StoreOp} {ty : Ty}
    {fl : MemFlags} {x p : ValueId} {off : Int} (h : mapOperands σ i = .store op ty fl x p off) :
    ∃ x0 p0, i = .store op ty fl x0 p0 off ∧ σ x0 = x ∧ σ p0 = p := by
  cases i <;> simp only [mapOperands, reduceCtorEq, Inst.store.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  exact ⟨_, _, rfl, rfl, rfl⟩

theorem mergeK_mapOperands (σ : ValueId → ValueId) (i : Inst) :
    mergeK (mapOperands σ i) = mergeK i := by
  cases i <;> rfl

theorem isPure_of_mergeK {i : Inst} (h : mergeK i = true) : isPure i = false := by
  cases i <;> simp_all [mergeK, isPure]

theorem notCall_of_mergeK {i : Inst} (h : mergeK i = true) : ∀ fn args, i ≠ .call fn args := by
  rintro fn args rfl
  simp [mergeK] at h

theorem setMany_single {r regs : Regs} {x : ValueId} {v : Val}
    (h : r.setMany [x] [v] = some regs) : regs x = some v := by
  simp only [Regs.setMany_cons, Regs.setMany_nil, Option.some.injEq] at h
  subst h
  simp

/-! ## `f` binds the results of one statement -/

section
variable {syms : String → Option Nat} {bi k k' : Nat} {S : List Fact} {fr fr' : Frame} {m : Mem}
  {st : Stmt} {rest : List Stmt}

/-- The statement `f` executes is statement `k` of block `bi`. -/
theorem stmt_at (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m)
    (hb : fr.body = st :: rest) :
    ∃ b, f.blocks[bi]? = some b ∧ b.body[k]? = some st ∧ b.body.drop (k + 1) = rest := by
  obtain ⟨b, hbi, hbody, -, -⟩ := hR.invf.block
  rw [hbody] at hb
  obtain ⟨hst, hrest, -⟩ := drop_eq_cons hb
  exact ⟨b, hbi, hst, hrest⟩

/-- `Rel`'s walk on the frames' bodies. -/
theorem walk_frames (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m) :
    ∃ fb gb Send, f.blocks[bi]? = some fb ∧ g.blocks[bi]? = some gb ∧
      (ccOf fi gi cert norm).walk bi fr.body fr'.body k k' S = some Send ∧
      EndOk (ccOf fi gi cert norm) bi fb gb Send := by
  obtain ⟨fb, gb, Send, hfb, hgb, hw, he⟩ := hR.walk
  obtain ⟨b, hb, hbody, -⟩ := hR.invf.block
  obtain ⟨b', hb', hbody', -⟩ := hR.invg.block
  have e1 : fb = b := Option.some.inj (hfb.symm.trans hb)
  have e2 : gb = b' := Option.some.inj (hgb.symm.trans hb')
  subst e1 e2
  exact ⟨fb, gb, Send, hfb, hgb, by rw [hbody, hbody']; exact hw, he⟩

/-- Values available at `(bi, k)` are not results of statement `k`. -/
theorem regs_afterD (H : HypD f g fi gi cert norm) {vals : List Val} {regs : Regs}
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m) (hb : fr.body = st :: rest)
    (hset : fr.regs.setMany st.results vals = some regs) :
    ∀ v, Avail (wfData f fi) bi k v → regs v = fr.regs v := by
  obtain ⟨b, hbi, hst, -⟩ := stmt_at hR hb
  exact fun v hv => ((setMany_spec hset).2 v).1 (H.wff.avail_not_result hbi hst hv)

/-- Values available at `(bi, k)` are not results of statement `k`. -/
theorem regs_afterT (H : HypT f g fi gi cert norm) {vals : List Val} {regs : Regs}
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m) (hb : fr.body = st :: rest)
    (hset : fr.regs.setMany st.results vals = some regs) :
    ∀ v, Avail (wfData f fi) bi k v → regs v = fr.regs v := by
  exact regs_afterD H.toD hR hb hset

/-- Values available at `(bi, k)` are not results of statement `k`. -/
theorem regs_after (H : Hyp f g fi gi cert norm) {vals : List Val} {regs : Regs}
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m) (hb : fr.body = st :: rest)
    (hset : fr.regs.setMany st.results vals = some regs) :
    ∀ v, Avail (wfData f fi) bi k v → regs v = fr.regs v := by
  exact regs_afterT H.toT hR hb hset

/-- Terms with sites no later than `(bi, k)` keep their values. -/
theorem TV_afterD (H : HypD f g fi gi cert norm) {vals : List Val} {regs : Regs}
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m) (hb : fr.body = st :: rest)
    (hset : fr.regs.setMany st.results vals = some regs) {t : Nat}
    (ht : LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf t) (bi, k)) :
    TV f cert syms { fr with regs, body := rest } t = TV f cert syms fr t :=
  H.TV_stable (fr1 := fr) (fr2 := { fr with regs, body := rest }) rfl rfl rfl
    (regs_afterD H hR hb hset) ht

/-- Terms with sites no later than `(bi, k)` keep their values. -/
theorem TV_afterT (H : HypT f g fi gi cert norm) {vals : List Val} {regs : Regs}
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m) (hb : fr.body = st :: rest)
    (hset : fr.regs.setMany st.results vals = some regs) {t : Nat}
    (ht : LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf t) (bi, k)) :
    TV f cert syms { fr with regs, body := rest } t = TV f cert syms fr t :=
  TV_afterD H.toD hR hb hset ht

/-- Terms with sites no later than `(bi, k)` keep their values. -/
theorem TV_after (H : Hyp f g fi gi cert norm) {vals : List Val} {regs : Regs}
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m) (hb : fr.body = st :: rest)
    (hset : fr.regs.setMany st.results vals = some regs) {t : Nat}
    (ht : LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf t) (bi, k)) :
    TV f cert syms { fr with regs, body := rest } t = TV f cert syms fr t :=
  TV_afterT H.toT hR hb hset ht

/-- **`f` alone executes statement `k`** (binding `vals` to its results, memory kept): the
relation one statement later, with facts `S'` that are old facts or hold, with sites no later
than `(bi, k + 1)`, in the new frame. -/
theorem rel_afterD (H : HypD f g fi gi cert norm) {S' : List Fact} {vals : List Val} {regs : Regs}
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m) (hb : fr.body = st :: rest)
    (hty : ∀ ts, st.inst.resultTypes (sigOf f) (sigDeclOf f) = some ts → vals.map (·.ty) = ts)
    (hpure : isPure st.inst = true → ∃ a, vals = [a] ∧ evalNode fr (symMem syms) st.inst = some a)
    (hset : fr.regs.setMany st.results vals = some regs)
    (hw : ∃ fb gb Send, f.blocks[bi]? = some fb ∧ g.blocks[bi]? = some gb ∧
      (ccOf fi gi cert norm).walk bi rest fr'.body (k + 1) k' S' = some Send ∧
      EndOk (ccOf fi gi cert norm) bi fb gb Send)
    (hres : ∀ r ∈ st.results,
      TV f cert syms { fr with regs, body := rest } ((ccOf fi gi cert norm).ef r) = regs r)
    (hS : ∀ F ∈ S', F ∈ S ∨ (FactHolds f cert syms { fr with regs, body := rest } m F ∧
      ∀ t ∈ F.terms, LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf t) (bi, k + 1))) :
    Rel f g fi gi cert norm syms bi (k + 1) k' S' { fr with regs, body := rest } fr' m := by
  obtain ⟨b, hbi, hst, hrest⟩ := stmt_at hR hb
  have hregs := regs_afterD H hR hb hset
  refine ⟨?_, H.wff.inv_results hR.invf hb hty hpure hset, hR.invg, hR.slots, fun x hx => ?_,
    fun y hy => ?_, fun y hy => (hR.sitesG y hy).mono (Nat.le_succ k), fun F hF => ?_,
    fun F hF => ?_⟩
  · obtain ⟨fb, gb, Send, hfb, hgb, hwk, he⟩ := hw
    obtain ⟨b', hb'', hbody', -⟩ := hR.invg.block
    have e1 : fb = b := Option.some.inj (hfb.symm.trans hbi)
    have e2 : gb = b' := Option.some.inj (hgb.symm.trans hb'')
    subst e1 e2
    refine ⟨fb, gb, Send, hfb, hgb, ?_, he⟩
    rw [hrest, ← hbody']
    exact hwk
  · rcases H.wff.avail_succ hbi hst hx with hr | hx'
    · exact hres x hr
    · rw [TV_afterD H hR hb hset (H.siteF hx'), hR.agreeF x hx']
      exact (hregs x hx').symm
  · rw [TV_afterD H hR hb hset (hR.sitesG y hy)]
    exact hR.agreeG y hy
  · rcases hS F hF with h | ⟨h, -⟩
    · exact FactHolds.stableD H (fr1 := fr) (fr2 := { fr with regs, body := rest }) rfl rfl rfl
        hregs (hR.factSites F h) (fun _ => rfl) (hR.facts F h)
    · exact h
  · rcases hS F hF with h | ⟨-, h⟩
    · exact fun t ht => (hR.factSites F h t ht).mono (Nat.le_succ k)
    · exact h

/-- **`f` alone executes statement `k`** (binding `vals` to its results, memory kept): the
relation one statement later, with facts `S'` that are old facts or hold, with sites no later
than `(bi, k + 1)`, in the new frame. -/
theorem rel_afterT (H : HypT f g fi gi cert norm) {S' : List Fact} {vals : List Val} {regs : Regs}
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m) (hb : fr.body = st :: rest)
    (hty : ∀ ts, st.inst.resultTypes (sigOf f) (sigDeclOf f) = some ts → vals.map (·.ty) = ts)
    (hpure : isPure st.inst = true → ∃ a, vals = [a] ∧ evalNode fr (symMem syms) st.inst = some a)
    (hset : fr.regs.setMany st.results vals = some regs)
    (hw : ∃ fb gb Send, f.blocks[bi]? = some fb ∧ g.blocks[bi]? = some gb ∧
      (ccOf fi gi cert norm).walk bi rest fr'.body (k + 1) k' S' = some Send ∧
      EndOk (ccOf fi gi cert norm) bi fb gb Send)
    (hres : ∀ r ∈ st.results,
      TV f cert syms { fr with regs, body := rest } ((ccOf fi gi cert norm).ef r) = regs r)
    (hS : ∀ F ∈ S', F ∈ S ∨ (FactHolds f cert syms { fr with regs, body := rest } m F ∧
      ∀ t ∈ F.terms, LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf t) (bi, k + 1))) :
    Rel f g fi gi cert norm syms bi (k + 1) k' S' { fr with regs, body := rest } fr' m := by
  exact rel_afterD H.toD hR hb hty hpure hset hw hres hS

/-- **`f` alone executes statement `k`** (binding `vals` to its results, memory kept): the
relation one statement later, with facts `S'` that are old facts or hold, with sites no later
than `(bi, k + 1)`, in the new frame. -/
theorem rel_after (H : Hyp f g fi gi cert norm) {S' : List Fact} {vals : List Val} {regs : Regs}
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m) (hb : fr.body = st :: rest)
    (hty : ∀ ts, st.inst.resultTypes (sigOf f) (sigDeclOf f) = some ts → vals.map (·.ty) = ts)
    (hpure : isPure st.inst = true → ∃ a, vals = [a] ∧ evalNode fr (symMem syms) st.inst = some a)
    (hset : fr.regs.setMany st.results vals = some regs)
    (hw : ∃ fb gb Send, f.blocks[bi]? = some fb ∧ g.blocks[bi]? = some gb ∧
      (ccOf fi gi cert norm).walk bi rest fr'.body (k + 1) k' S' = some Send ∧
      EndOk (ccOf fi gi cert norm) bi fb gb Send)
    (hres : ∀ r ∈ st.results,
      TV f cert syms { fr with regs, body := rest } ((ccOf fi gi cert norm).ef r) = regs r)
    (hS : ∀ F ∈ S', F ∈ S ∨ (FactHolds f cert syms { fr with regs, body := rest } m F ∧
      ∀ t ∈ F.terms, LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf t) (bi, k + 1))) :
    Rel f g fi gi cert norm syms bi (k + 1) k' S' { fr with regs, body := rest } fr' m := by
  exact rel_afterT H.toT hR hb hty hpure hset hw hres hS

/-- The term of a checked pure statement of `f` has the statement's value in a frame whose
registers hold its operands' term values and in which the atoms below its normalised node are
typed (`AtomsTyped`). -/
theorem TV_pureOkT (H : HypT f g fi gi cert norm) {bound : Nat × Nat} {t : Nat} {fr1 fr0 : Frame}
    (hP : PureOk (ccOf fi gi cert norm) (ccOf fi gi cert norm).ef (ccOf fi gi cert norm).fty st
      bound t)
    (hg : fr1.func.globals = fr0.func.globals) (hx : fr1.func.externs = fr0.func.externs)
    (hs : fr1.slots = fr0.slots)
    (hr : ∀ x ∈ operands st.inst, TV f cert syms fr1 ((ccOf fi gi cert norm).ef x) = fr0.regs x)
    (hA : AtomsTyped f cert.tms fr1 (symMem syms) (mapOperands (ccOf fi gi cert norm).ef st.inst)) :
    TV f cert syms fr1 t = evalNode fr0 (symMem syms) st.inst := by
  rcases hP.node with hn | ⟨hsome, heq⟩
  · have hn' : cert.tms[t]? = some (.node (mapOperands (ccOf fi gi cert norm).ef st.inst)) := hn
    refine tmVal_mapOperands hn' (fun x hxm => ?_) hg hx hs hr
    have hok := CC.tmOk_node (CC.tmsOk_get H.ok.tms hn') ((ccOf fi gi cert norm).ef x)
      (by rw [operands_mapOperands]; exact List.mem_map.2 ⟨x, hxm, rfl⟩)
    exact hok.1
  · obtain ⟨tx, htx⟩ := Option.isSome_iff_exists.1 hsome
    have ht : cert.tms[t]? = some tx := heq.symm.trans htx
    exact (H.norm _ _ tx htx fr1 (symMem syms) t ht hA).trans (evalNode_rename hg hx hs hr)

/-- The term of a checked pure statement of `f` has the statement's value in a frame whose
registers hold its operands' term values. -/
theorem TV_pureOk (H : Hyp f g fi gi cert norm) {bound : Nat × Nat} {t : Nat} {fr1 fr0 : Frame}
    (hP : PureOk (ccOf fi gi cert norm) (ccOf fi gi cert norm).ef (ccOf fi gi cert norm).fty st
      bound t)
    (hg : fr1.func.globals = fr0.func.globals) (hx : fr1.func.externs = fr0.func.externs)
    (hs : fr1.slots = fr0.slots)
    (hr : ∀ x ∈ operands st.inst, TV f cert syms fr1 ((ccOf fi gi cert norm).ef x) = fr0.regs x) :
    TV f cert syms fr1 t = evalNode fr0 (symMem syms) st.inst := by
  rcases hP.node with hn | ⟨hsome, heq⟩
  · have hn' : cert.tms[t]? = some (.node (mapOperands (ccOf fi gi cert norm).ef st.inst)) := hn
    refine tmVal_mapOperands hn' (fun x hxm => ?_) hg hx hs hr
    have hok := CC.tmOk_node (CC.tmsOk_get H.ok.tms hn') ((ccOf fi gi cert norm).ef x)
      (by rw [operands_mapOperands]; exact List.mem_map.2 ⟨x, hxm, rfl⟩)
    exact hok.1
  · obtain ⟨tx, htx⟩ := Option.isSome_iff_exists.1 hsome
    have ht : cert.tms[t]? = some tx := heq.symm.trans htx
    exact (H.norm _ _ tx htx f fr1 (symMem syms) t ht).trans (evalNode_rename hg hx hs hr)

/-- The term of a checked pure statement of `f` has the statement's value in a frame whose
registers hold its operands' term values, in which the atoms below its normalised node are typed
(`AtomsTyped`) and its operands have values (`NormSoundD`). -/
theorem TV_pureOkD (H : HypD f g fi gi cert norm) {bound : Nat × Nat} {t : Nat} {fr1 fr0 : Frame}
    (hP : PureOk (ccOf fi gi cert norm) (ccOf fi gi cert norm).ef (ccOf fi gi cert norm).fty st
      bound t)
    (hg : fr1.func.globals = fr0.func.globals) (hx : fr1.func.externs = fr0.func.externs)
    (hs : fr1.slots = fr0.slots)
    (hr : ∀ x ∈ operands st.inst, TV f cert syms fr1 ((ccOf fi gi cert norm).ef x) = fr0.regs x)
    (hA : AtomsTyped f cert.tms fr1 (symMem syms) (mapOperands (ccOf fi gi cert norm).ef st.inst))
    (hd : ∀ x ∈ operands st.inst, (fr0.regs x).isSome) :
    TV f cert syms fr1 t = evalNode fr0 (symMem syms) st.inst := by
  rcases hP.node with hn | ⟨hsome, heq⟩
  · have hn' : cert.tms[t]? = some (.node (mapOperands (ccOf fi gi cert norm).ef st.inst)) := hn
    refine tmVal_mapOperands hn' (fun x hxm => ?_) hg hx hs hr
    have hok := CC.tmOk_node (CC.tmsOk_get H.ok.tms hn') ((ccOf fi gi cert norm).ef x)
      (by rw [operands_mapOperands]; exact List.mem_map.2 ⟨x, hxm, rfl⟩)
    exact hok.1
  · obtain ⟨tx, htx⟩ := Option.isSome_iff_exists.1 hsome
    have ht : cert.tms[t]? = some tx := heq.symm.trans htx
    refine (H.norm _ _ tx htx fr1 (symMem syms) t ht hA fun o ho => ?_).trans
      (evalNode_rename hg hx hs hr)
    rw [operands_mapOperands] at ho
    obtain ⟨x, hx', rfl⟩ := List.mem_map.1 ho
    show (TV f cert syms fr1 ((ccOf fi gi cert norm).ef x)).isSome = true
    rw [hr x hx']
    exact hd x hx'

end

end FStep

open FStep

/-! ## The three steps -/

section
variable {syms : String → Option Nat} {bi k k' : Nat} {S : List Fact} {fr fr' : Frame} {m : Mem}
  {st : Stmt} {rest : List Stmt}

/-- **A `nop` of `f`.** -/
theorem rel_nopD (H : HypD f g fi gi cert norm)
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m)
    (hb : fr.body = st :: rest) (hn : st.inst = .nop) :
    lstep fr m = .next { fr with body := rest } m ∧
      Rel f g fi gi cert norm syms bi (k + 1) k' S { fr with body := rest } fr' m := by
  obtain ⟨b, hbi, hst, -⟩ := stmt_at hR hb
  have h0 : (Inst.nop).resultTypes (sigOf f) (sigDeclOf f) = some [] := rfl
  have hres : st.results = [] := by
    obtain ⟨ts, hts, hlen, -⟩ := H.wff.results bi b hbi k st hst
    rw [hn, h0] at hts
    cases hts
    exact List.eq_nil_of_length_eq_zero hlen.symm
  refine ⟨?_, ?_⟩
  · rw [lstep_inst hb (fun fn args h => by rw [hn] at h; cases h), hn, hres]
    rfl
  · obtain ⟨fb, gb, Send, hfb, hgb, hw, he⟩ := walk_frames hR
    rw [hb, walk_nop hn] at hw
    exact rel_afterD H (vals := []) (regs := fr.regs) hR hb
      (fun ts hts => by rw [hn, h0] at hts; cases hts; rfl)
      (fun h => by rw [hn] at h; cases h)
      (by rw [hres]; rfl) ⟨fb, gb, Send, hfb, hgb, hw, he⟩
      (fun r hr => by rw [hres] at hr; cases hr)
      (fun F hF => .inl hF)

/-- **A `nop` of `f`.** -/
theorem rel_nopT (H : HypT f g fi gi cert norm)
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m)
    (hb : fr.body = st :: rest) (hn : st.inst = .nop) :
    lstep fr m = .next { fr with body := rest } m ∧
      Rel f g fi gi cert norm syms bi (k + 1) k' S { fr with body := rest } fr' m := by
  exact rel_nopD H.toD hR hb hn

/-- **A `nop` of `f`.** -/
theorem rel_nop (H : Hyp f g fi gi cert norm)
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m)
    (hb : fr.body = st :: rest) (hn : st.inst = .nop) :
    lstep fr m = .next { fr with body := rest } m ∧
      Rel f g fi gi cert norm syms bi (k + 1) k' S { fr with body := rest } fr' m := by
  exact rel_nopT H.toT hR hb hn

/-- **A pure statement of `f`.** -/
theorem rel_pureD (H : HypD f g fi gi cert norm)
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m)
    (hm : m.symbols = syms) (hb : fr.body = st :: rest) (hn : st.inst ≠ .nop)
    (hp : pureK st.inst = true) :
    (∃ fr1 S', lstep fr m = .next fr1 m ∧ Rel f g fi gi cert norm syms bi (k + 1) k' S' fr1 fr' m) ∨
      ∃ msg, lstep fr m = .stuck msg := by
  obtain ⟨b, hbi, hst, -⟩ := stmt_at hR hb
  obtain ⟨fb, gb, Send, hfb, hgb, hw, he⟩ := walk_frames hR
  rw [hb] at hw
  obtain ⟨t, hP, hw⟩ := walk_pure_spec hn hp hw
  obtain ⟨r, hr⟩ : ∃ r, st.results = [r] := by
    have h1 := hP.res
    rcases hrs : st.results with _ | ⟨r, _ | ⟨r', rs⟩⟩
    · rw [hrs] at h1; simp at h1
    · exact ⟨r, rfl⟩
    · rw [hrs] at h1; simp at h1
  have hrt : (ccOf fi gi cert norm).ef r = t := hP.term r (by rw [hr]; simp)
  have hlstep := lstep_inst (mem := m) hb (pureK_not_call hp)
  have hav : ∀ x ∈ operands st.inst, Avail (wfData f fi) bi k x := H.wff.uses bi b hbi k st hst
  have hev : (∃ v, evalInst fr m st.inst = .ok ([v], m)) ∨
      ∃ msg, evalInst fr m st.inst = .stuck msg := by
    cases hpart : partialK st.inst
    · exact .inl (evalInst_pureK_totalM hp hpart (H.wff.pure bi b hbi k st hst) hP.typed
        (by rw [hR.invf.func]) (fun x hx => hR.invf.regs x (hav x hx)) hR.invf.slots)
    · exact evalInst_partialK hpart
  rcases hev with ⟨v, hv⟩ | ⟨msg, hmsg⟩
  · have hset : fr.regs.setMany st.results [v] = some (fr.regs.set r v) := by rw [hr]; rfl
    have hnode : evalNode fr (symMem syms) st.inst = some v :=
      (evalNode_pureK_syms hp hm.symm).trans (evalNode_of_ok hv)
    have htv : TV f cert syms { fr with regs := fr.regs.set r v, body := rest } t = some v := by
      rw [TV_pureOkD H hP (fr1 := { fr with regs := fr.regs.set r v, body := rest }) (fr0 := fr)
        rfl rfl rfl (fun x hx => by
        rw [TV_afterD H hR hb hset (H.siteF (hav x hx))]
        exact hR.agreeF x (hav x hx))
        (H.atomsTyped (bi := bi) (k := k)
          (fun w hw => by
            obtain ⟨a, ha, hta⟩ := hR.invf.regs w hw
            exact ⟨a, (regs_afterD H hR hb hset w hw).trans ha, hta⟩)
          (fun o ho => by
            rw [operands_mapOperands] at ho
            obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ho
            exact H.siteF (hav x hx)))
        (fun x hx => by
          obtain ⟨a, ha, -⟩ := hR.invf.regs x (hav x hx)
          rw [ha]; rfl), hnode]
    left
    refine ⟨{ fr with regs := fr.regs.set r v, body := rest },
      if partialK st.inst then .defd t :: S else S, ?_, ?_⟩
    · simp only [hlstep, hv, LRes.ofRes_ok, hset]
    · refine rel_afterD H hR hb (fun ts hts => evalInst_types hv hts)
        (fun _ => ⟨v, rfl, hnode⟩) hset ⟨fb, gb, Send, hfb, hgb, hw, he⟩ (fun r' hr' => ?_)
        (fun F hF => ?_)
      · rw [hr, List.mem_singleton] at hr'
        subst hr'
        rw [hrt, htv]
        simp
      · by_cases hpart : partialK st.inst = true
        · simp only [hpart, ↓reduceIte] at hF
          rcases List.mem_cons.1 hF with rfl | hF
          · refine .inr ⟨?_, fun t' ht' => ?_⟩
            · simp only [FactHolds, htv, Option.isSome_some]
            · simp only [Fact.terms, List.mem_singleton] at ht'
              subst ht'
              exact H.le_sound hP.site
          · exact .inl hF
        · simp only [hpart, Bool.false_eq_true, ↓reduceIte] at hF
          exact .inl hF
  · right
    exact ⟨msg, by rw [hlstep, hmsg]; rfl⟩

/-- **A pure statement of `f`.** -/
theorem rel_pureT (H : HypT f g fi gi cert norm)
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m)
    (hm : m.symbols = syms) (hb : fr.body = st :: rest) (hn : st.inst ≠ .nop)
    (hp : pureK st.inst = true) :
    (∃ fr1 S', lstep fr m = .next fr1 m ∧ Rel f g fi gi cert norm syms bi (k + 1) k' S' fr1 fr' m) ∨
      ∃ msg, lstep fr m = .stuck msg := by
  exact rel_pureD H.toD hR hm hb hn hp

/-- **A pure statement of `f`.** -/
theorem rel_pure (H : Hyp f g fi gi cert norm)
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m)
    (hm : m.symbols = syms) (hb : fr.body = st :: rest) (hn : st.inst ≠ .nop)
    (hp : pureK st.inst = true) :
    (∃ fr1 S', lstep fr m = .next fr1 m ∧ Rel f g fi gi cert norm syms bi (k + 1) k' S' fr1 fr' m) ∨
      ∃ msg, lstep fr m = .stuck msg := by
  exact rel_pureT H.toT hR hm hb hn hp

/-- **A skeleton statement of `f` the walk removed.** -/
theorem rel_removeD (H : HypD f g fi gi cert norm)
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m)
    (hm : m.symbols = syms) (hb : fr.body = st :: rest) (hn : st.inst ≠ .nop)
    (hp : pureK st.inst = false)
    (hrm : (ccOf fi gi cert norm).removeOk bi k st S
      (mapOperands (ccOf fi gi cert norm).ef st.inst) = true)
    (hw : ∃ fb gb Send, f.blocks[bi]? = some fb ∧ g.blocks[bi]? = some gb ∧
      (ccOf fi gi cert norm).walk bi rest fr'.body (k + 1) k' S = some Send ∧
      EndOk (ccOf fi gi cert norm) bi fb gb Send) :
    (∃ fr1, lstep fr m = .next fr1 m ∧ Rel f g fi gi cert norm syms bi (k + 1) k' S fr1 fr' m) ∨
      ∃ msg, lstep fr m = .stuck msg := by
  obtain ⟨b, hbi, hst, -⟩ := stmt_at hR hb
  have hav : ∀ x ∈ operands st.inst, Avail (wfData f fi) bi k x := H.wff.uses bi b hbi k st hst
  have hget : ∀ x ∈ operands st.inst, ∀ a,
      TV f cert syms fr ((ccOf fi gi cert norm).ef x) = some a → fr.get x = .ok a := by
    intro x hx a ha
    rw [hR.agreeF x (hav x hx)] at ha
    simp [Frame.get, ha]
  obtain ⟨ts, hts, hlen, -⟩ := H.wff.results bi b hbi k st hst
  -- the common end: the statement evaluated without changing memory
  have fin : ∀ vals, (∀ fn args, st.inst ≠ .call fn args) →
      evalInst fr m st.inst = .ok (vals, m) → isPure st.inst = false →
      (∀ regs, fr.regs.setMany st.results vals = some regs → ∀ r ∈ st.results,
        TV f cert syms { fr with regs, body := rest } ((ccOf fi gi cert norm).ef r) = regs r) →
      (∃ fr1, lstep fr m = .next fr1 m ∧
        Rel f g fi gi cert norm syms bi (k + 1) k' S fr1 fr' m) ∨
        ∃ msg, lstep fr m = .stuck msg := by
    intro vals hnc hev hnp hres
    have hl : st.results.length = vals.length := by
      rw [← hlen, ← evalInst_types hev hts, List.length_map]
    obtain ⟨regs, hset⟩ := setMany_len (r := fr.regs) hl
    refine .inl ⟨{ fr with regs, body := rest }, ?_, rel_afterD H hR hb
      (fun ts' h' => evalInst_types hev h') (fun h => by rw [hnp] at h; cases h) hset hw
      (hres regs hset) (fun F hF => .inl hF)⟩
    simp only [lstep_inst hb hnc, hev, LRes.ofRes_ok, hset]
  have stuck : (∀ fn args, st.inst ≠ .call fn args) → ∀ msg,
      evalInst fr m st.inst = .stuck msg →
      (∃ fr1, lstep fr m = .next fr1 m ∧
        Rel f g fi gi cert norm syms bi (k + 1) k' S fr1 fr' m) ∨
        ∃ msg, lstep fr m = .stuck msg := fun hnc msg h =>
    .inr ⟨msg, by rw [lstep_inst hb hnc, h]; rfl⟩
  -- the result of a removed statement whose term's value is known
  have known : ∀ r v regs, st.results = [r] →
      TV f cert syms fr ((ccOf fi gi cert norm).ef r) = some v →
      LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf ((ccOf fi gi cert norm).ef r)) (bi, k) →
      fr.regs.setMany st.results [v] = some regs → ∀ r' ∈ st.results,
        TV f cert syms { fr with regs, body := rest } ((ccOf fi gi cert norm).ef r') = regs r' := by
    intro r v regs hr hv hle hset r' hr'
    rw [hr, List.mem_singleton] at hr'
    subst hr'
    rw [TV_afterD H hR hb hset hle, hv]
    rw [hr] at hset
    exact (setMany_single hset).symm
  rcases removeOk_spec hrm with
    ⟨op, ty, fl, p, off, r, hi, hr, hfact | ⟨htc, hpo⟩⟩ |
    ⟨op, ty, fl, x, p, off, hi, hfact⟩ | ⟨hk, ⟨r, hr, hfact⟩ | ⟨hr, hfact⟩⟩
  · -- a load of a location held by a memory fact
    obtain ⟨p0, hi0, hp0⟩ := mapOperands_eq_load hi
    have hnc : ∀ fn args, st.inst ≠ .call fn args := fun fn args h => by rw [hi0] at h; cases h
    obtain ⟨av, vv, ha, hvv, hh⟩ := hR.facts _ hfact
    rw [← hp0] at ha
    have hg := hget p0 (by rw [hi0]; simp [operands]) av ha
    rcases evalInst_load_of_holds hg hh with h | ⟨msg, h⟩
    · rw [← hi0] at h
      exact fin [vv] hnc h (by rw [hi0]; rfl) fun regs hset =>
        known r vv regs hr hvv (hR.factSites _ hfact _ (by simp [Fact.terms])) hset
    · rw [← hi0] at h
      exact stuck hnc msg h
  · -- a `notrap` load: its result is the atom `poison bi k`
    obtain ⟨p0, hi0, -⟩ := mapOperands_eq_load hi
    have hnc : ∀ fn args, st.inst ≠ .call fn args := fun fn args h => by rw [hi0] at h; cases h
    obtain ⟨pv, hpv, -⟩ := hR.invf.regs p0 (hav p0 (by rw [hi0]; simp [operands]))
    have hg : fr.get p0 = .ok pv := by simp [Frame.get, hpv]
    rcases h : evalInst fr m st.inst with ⟨vals, m'⟩ | c | msg
    · rw [hi0] at h
      obtain ⟨rfl, v, rfl, -⟩ := holds_of_evalInst_load h hg
      rw [← hi0] at h
      refine fin [v] hnc h (by rw [hi0]; rfl) fun regs hset r' hr' => ?_
      rw [hr, List.mem_singleton] at hr'
      subst hr'
      have hpo' : cert.tms[(ccOf fi gi cert norm).ef r']? = some (.poison bi k) := hpo
      have hat : atomVal f (.poison bi k) = some r' := by simp [atomVal, hbi, hst, hr]
      rw [show TV f cert syms { fr with regs, body := rest } ((ccOf fi gi cert norm).ef r') =
          (atomVal f (.poison bi k)).bind ({ fr with regs, body := rest } : Frame).regs from
          tmVal_atom hpo' (fun _ h => by cases h), hat]
      rfl
    · rw [hi0] at h
      exact absurd h (evalInst_load_notrap htc c)
    · exact stuck hnc msg h
  · -- a store of the value its location holds
    obtain ⟨x0, p0, hi0, hx0, hp0⟩ := mapOperands_eq_store hi
    have hnc : ∀ fn args, st.inst ≠ .call fn args := fun fn args h => by rw [hi0] at h; cases h
    obtain ⟨av, xv, ha, hxv, hh⟩ := hR.facts _ hfact
    rw [← hp0] at ha
    rw [← hx0] at hxv
    have hgp := hget p0 (by rw [hi0]; simp [operands]) av ha
    have hgx := hget x0 (by rw [hi0]; simp [operands]) xv hxv
    have hres0 : st.results = [] := by
      have h0 : st.inst.resultTypes (sigOf f) (sigDeclOf f) = some [] := by rw [hi0]; rfl
      rw [h0] at hts
      cases hts
      exact List.eq_nil_of_length_eq_zero hlen.symm
    rcases evalInst_store_idem hgx hgp hh with h | ⟨msg, h⟩
    · rw [← hi0] at h
      exact fin [] hnc h (by rw [hi0]; rfl) fun regs _ r' hr' => by rw [hres0] at hr'; cases hr'
    · rw [← hi0] at h
      exact stuck hnc msg h
  · -- an idempotent trapping instruction with one result, equal to an evaluated one
    have hk' : mergeK st.inst = true := by rwa [mergeK_mapOperands] at hk
    have hnc := notCall_of_mergeK hk'
    obtain ⟨v, hv, he⟩ := hR.facts _ hfact
    have hnorm := tmVal_mapOperands_inst (f := f) (tms := cert.tms) (fr := fr) (fr0 := fr)
      (mem := symMem syms) (σ := (ccOf fi gi cert norm).ef) (i := st.inst) rfl rfl rfl
      (fun x hx => hR.agreeF x (hav x hx))
    have hsym := Res.norm_eq_ok hnorm.symm he
    have hm' := ((evalInst_mergeK hk').1 _ _ hsym).2 m
    exact fin [v] hnc hm' (isPure_of_mergeK hk') fun regs hset =>
      known r v regs hr hv (hR.factSites _ hfact _ (by simp [Fact.terms])) hset
  · -- an idempotent trapping instruction without results, equal to an evaluated one
    have hk' : mergeK st.inst = true := by rwa [mergeK_mapOperands] at hk
    have hnc := notCall_of_mergeK hk'
    have he : evalInst (tmFrame f cert.tms fr (symMem syms)) (symMem syms)
        (mapOperands (ccOf fi gi cert norm).ef st.inst) = .ok ([], symMem syms) := hR.facts _ hfact
    have hnorm := tmVal_mapOperands_inst (f := f) (tms := cert.tms) (fr := fr) (fr0 := fr)
      (mem := symMem syms) (σ := (ccOf fi gi cert norm).ef) (i := st.inst) rfl rfl rfl
      (fun x hx => hR.agreeF x (hav x hx))
    have hsym := Res.norm_eq_ok hnorm.symm he
    have hm' := ((evalInst_mergeK hk').1 _ _ hsym).2 m
    exact fin [] hnc hm' (isPure_of_mergeK hk') fun regs _ r' hr' => by rw [hr] at hr'; cases hr'

/-- **A skeleton statement of `f` the walk removed.** -/
theorem rel_removeT (H : HypT f g fi gi cert norm)
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m)
    (hm : m.symbols = syms) (hb : fr.body = st :: rest) (hn : st.inst ≠ .nop)
    (hp : pureK st.inst = false)
    (hrm : (ccOf fi gi cert norm).removeOk bi k st S
      (mapOperands (ccOf fi gi cert norm).ef st.inst) = true)
    (hw : ∃ fb gb Send, f.blocks[bi]? = some fb ∧ g.blocks[bi]? = some gb ∧
      (ccOf fi gi cert norm).walk bi rest fr'.body (k + 1) k' S = some Send ∧
      EndOk (ccOf fi gi cert norm) bi fb gb Send) :
    (∃ fr1, lstep fr m = .next fr1 m ∧ Rel f g fi gi cert norm syms bi (k + 1) k' S fr1 fr' m) ∨
      ∃ msg, lstep fr m = .stuck msg := by
  exact rel_removeD H.toD hR hm hb hn hp hrm hw

/-- **A skeleton statement of `f` the walk removed.** -/
theorem rel_remove (H : Hyp f g fi gi cert norm)
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m)
    (hm : m.symbols = syms) (hb : fr.body = st :: rest) (hn : st.inst ≠ .nop)
    (hp : pureK st.inst = false)
    (hrm : (ccOf fi gi cert norm).removeOk bi k st S
      (mapOperands (ccOf fi gi cert norm).ef st.inst) = true)
    (hw : ∃ fb gb Send, f.blocks[bi]? = some fb ∧ g.blocks[bi]? = some gb ∧
      (ccOf fi gi cert norm).walk bi rest fr'.body (k + 1) k' S = some Send ∧
      EndOk (ccOf fi gi cert norm) bi fb gb Send) :
    (∃ fr1, lstep fr m = .next fr1 m ∧ Rel f g fi gi cert norm syms bi (k + 1) k' S fr1 fr' m) ∨
      ∃ msg, lstep fr m = .stuck msg := by
  exact rel_removeT H.toT hR hm hb hn hp hrm hw

end

end Opt.MidVal
