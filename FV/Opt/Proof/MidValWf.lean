import FV.Opt.MidVal
import FV.Opt.Proof.SimWin

/-!
# The facts of the validator's well-formedness check `Opt.MidVal.wfCheck` (#1119)

`WfM f W`: the facts of `Opt.Wf` (`FV/Opt/Proof/Dom.lean`) with the two differences of `wfCheck`
(`FV/Opt/MidVal.lean`): result types of a `call_indirect` from the function's signature
declarations (`sigDeclOf`), and the `bitcast` typing of `Clif.evalInst` (`pureTypedM`).
`wfM_of_wfCheck` is `Opt.wf_of_check` for `wfCheck`. The lemmas of `FV/Opt/Proof/DomInv.lean` and
`FV/Opt/Proof/GvnEditX.lean` the validator's proof uses are restated for `WfM` (their proofs read
only the fields `WfM` shares with `Wf`, except `inv_results`, whose result types come from the
signature declarations): `WfM.site_result`, …, `WfM.inv_results`, `WfM.inv_entry`,
`WfM.inv_enter`, `WfM.inv_regs_congr`. `Opt.Wf` and its lemmas are unchanged.
-/

namespace Opt.MidVal

open Clif

/-- The facts of `wfCertM` (module doc). -/
structure WfM (f : Function) (W : WfData) : Prop where
  ids : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → W.index b.id = some i
  sites : ∀ v s, (v, s) ∈ defSites f → W.dm v = some s
  sitesRev : ∀ v s, W.dm v = some s → (v, s) ∈ defSites f
  root : W.idom[0]?.join = none
  rank : ∀ b c, W.idom[b]?.join = some c → W.rank c < W.rank b
  params : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → ∀ p ∈ b.params, W.tm p.1 = some p.2
  uses : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → ∀ (j : Nat) (st : Stmt), b.body[j]? = some st →
    ∀ v ∈ operands st.inst, Avail W i j v
  results : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → ∀ (j : Nat) (st : Stmt), b.body[j]? = some st →
    ∃ ts, st.inst.resultTypes (sigOf f) (sigDeclOf f) = some ts ∧ ts.length = st.results.length ∧
      ∀ (n : Nat) r, st.results[n]? = some r → W.tm r = ts[n]?
  pure : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → ∀ (j : Nat) (st : Stmt), b.body[j]? = some st →
    isPure st.inst = true → pureTypedM W.tm f st.inst = true
  termUses : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → ∀ v ∈ termOperands b.term, Avail W i b.body.length v
  edges : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → ∀ id ∈ termSuccs b.term, ∃ j, ∃ b' : Block, W.index id = some j ∧
    f.blocks[j]? = some b' ∧ b'.id = id ∧ ∀ c, W.idom[j]?.join = some c → Anc W.idom c i

theorem wfCertM_sound {f : Function} {info : Info} (h : wfCertM f info.cfg info.types = true) :
    WfM f (wfData f info) := by
  simp only [wfCertM, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hids, hsites⟩, hroot⟩, hrank⟩, hblocks⟩ := h
  have hmem : ∀ {α : Type} {l : List α} {i : Nat} {x : α}, l[i]? = some x → (x, i) ∈ l.zipIdx :=
    fun h => List.mem_zipIdx_iff_getElem?.2 h
  refine
    { ids := fun i b hb => by
        simpa [wfData, Std.HashMap.get?_eq_getElem?] using hids _ (hmem hb)
      sites := fun v s hs => by simpa [wfData] using hsites _ hs
      sitesRev := fun v s hs => by
        rcases foldl_insert_get _ v s hs with h | h
        · simp at h
        · exact h
      root := by simpa [wfData] using hroot
      rank := fun b c hc => by
        simp only [wfData] at hc ⊢
        have hb : b < info.cfg.idom.size := by
          rcases Nat.lt_or_ge b info.cfg.idom.size with h | h
          · exact h
          · rw [Array.getElem?_eq_none h] at hc; cases hc
        have := hrank b (List.mem_range.2 hb)
        simp only [hc] at this
        simpa [wfData] using this
      params := ?_, uses := ?_, results := ?_, pure := ?_, termUses := ?_, edges := ?_ }
  all_goals intro i b hb
  all_goals obtain ⟨⟨⟨hpar, hbody⟩, hterm⟩, hsucc⟩ := by simpa using hblocks _ (hmem hb)
  · intro p hp; simpa [wfData, Std.HashMap.get?_eq_getElem?] using hpar p.1 p.2 hp
  · intro j st hst v hv
    exact availB_sound (by simpa [wfData] using (hbody st j (hmem hst)).1.1 v hv)
  · intro j st hst
    have h2 := (hbody st j (hmem hst)).1.2
    split at h2
    · rename_i ts hts
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h2
      refine ⟨ts, hts, h2.1, fun n r hr => ?_⟩
      have hn : n < ts.length := by
        rw [h2.1]; exact (List.getElem?_eq_some_iff.1 hr).1
      have hz : (r, ts[n]) ∈ st.results.zip ts :=
        List.mem_iff_getElem?.2 ⟨n, by simp [List.getElem?_zip_eq_some, hr]⟩
      have := h2.2 _ hz
      simpa [wfData, List.getElem?_eq_getElem hn] using this
    · cases h2
  · intro j st hst hp
    have h3 := (hbody st j (hmem hst)).2
    simpa [hp, wfData, Std.HashMap.get?_eq_getElem?] using h3
  · intro v hv
    exact availB_sound (by simpa [wfData] using hterm v hv)
  · intro id hid
    have h4 := hsucc id hid
    split at h4
    · rename_i j hj
      simp only [Bool.and_eq_true, beq_iff_eq] at h4
      obtain ⟨h5, h6⟩ := h4
      cases hbj : f.blocks[j]? with
      | none => simp [hbj] at h5
      | some b' =>
        simp only [hbj, Option.map_some, Option.some.injEq] at h5
        refine ⟨j, b', hj, hbj, h5, fun c hc => ?_⟩
        simp only [wfData] at hc
        simp only [hc] at h6
        exact ancB_sound h6
    · cases h4

/-- `wfCheck` establishes the facts `WfM`. -/
theorem wfM_of_wfCheck {f : Function} {info : Info} (h : wfCheck f = .ok info) :
    WfM f (wfData f info) := by
  have : wfCertM f info.cfg info.types = true := by
    unfold wfCheck at h
    cases hc : checkCoreM f with
    | error e => simp [hc, bind, Except.bind] at h
    | ok i =>
      simp only [hc, bind, Except.bind, ensure, pure, Except.pure] at h
      by_cases hw : wfCertM f i.cfg i.types = true
      · simp only [hw, ite_true] at h; cases h; exact hw
      · simp only [hw] at h; cases h
  exact wfCertM_sound this

/-! ## The lemmas of `DomInv` and `GvnEditX` for `WfM` -/

namespace WfM

section
variable {f : Function} {W : WfData} (hW : WfM f W)
include hW

theorem site_result {i : Nat} {b : Block} {j : Nat} {st : Stmt} {r : ValueId}
    (hb : f.blocks[i]? = some b) (hst : b.body[j]? = some st) (hr : r ∈ st.results) :
    W.dm r = some (i, j + 1) :=
  hW.sites _ _ (mem_defSites.2 ⟨i, b, hb, .inr ⟨j, st, hst, hr, rfl⟩⟩)

theorem site_param {i : Nat} {b : Block} {p : ValueId × Ty} (hb : f.blocks[i]? = some b)
    (hp : p ∈ b.params) : W.dm p.1 = some (i, 0) :=
  hW.sites _ _ (mem_defSites.2 ⟨i, b, hb, .inl ⟨p, hp, rfl, rfl⟩⟩)

theorem site_stmt {v : ValueId} {d j : Nat} (h : W.dm v = some (d, j + 1)) :
    ∃ b st, f.blocks[d]? = some b ∧ b.body[j]? = some st ∧ v ∈ st.results := by
  obtain ⟨i, b, hb, ⟨p, _, _, hs⟩ | ⟨j', st, hst, hr, hs⟩⟩ := mem_defSites.1 (hW.sitesRev _ _ h)
  · cases hs
  · simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨b, st, hb, hst, hr⟩

theorem site_param' {v : ValueId} {d : Nat} (h : W.dm v = some (d, 0)) :
    ∃ b p, f.blocks[d]? = some b ∧ p ∈ b.params ∧ p.1 = v := by
  obtain ⟨i, b, hb, ⟨p, hp, h1, hs⟩ | ⟨j', st, hst, hr, hs⟩⟩ := mem_defSites.1 (hW.sitesRev _ _ h)
  · simp only [Prod.mk.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    exact ⟨b, p, hb, hp, h1⟩
  · simp at hs

theorem site_bound {v : ValueId} {d t : Nat} (h : W.dm v = some (d, t)) :
    ∃ b, f.blocks[d]? = some b ∧ t ≤ b.body.length := by
  obtain ⟨i, b, hb, ⟨p, _, _, hs⟩ | ⟨j', st, hst, _, hs⟩⟩ := mem_defSites.1 (hW.sitesRev _ _ h)
  · simp only [Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs; exact ⟨b, hb, Nat.zero_le _⟩
  · simp only [Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
    exact ⟨b, hb, (List.getElem?_eq_some_iff.1 hst).1⟩

theorem avail_operand {i k : Nat} {v : ValueId} {d j : Nat} {b : Block} {st : Stmt} {x : ValueId}
    (hv : Avail W i k v) (hd : W.dm v = some (d, j + 1)) (hb : f.blocks[d]? = some b)
    (hst : b.body[j]? = some st) (hx : x ∈ operands st.inst) : Avail W i k x := by
  obtain ⟨d', t', hx', hxa⟩ := hW.uses d b hb j st hst x hx
  obtain ⟨d0, t0, hv', hva⟩ := hv
  rw [hd] at hv'
  simp only [Option.some.injEq, Prod.mk.injEq] at hv'
  obtain ⟨rfl, rfl⟩ := hv'
  refine ⟨d', t', hx', ?_⟩
  rcases hxa with ⟨rfl, ht⟩ | ⟨hne, ha⟩ <;> rcases hva with ⟨rfl, ht2⟩ | ⟨hne2, ha2⟩
  · exact .inl ⟨rfl, by omega⟩
  · exact .inr ⟨hne2, ha2⟩
  · exact .inr ⟨hne, ha⟩
  · refine .inr ⟨fun he => ?_, ha.trans ha2⟩
    subst he
    exact hne (Anc.antisymm hW.rank ha ha2)

theorem avail_not_result {bi k : Nat} {b : Block} {st : Stmt} {v : ValueId}
    (hb : f.blocks[bi]? = some b) (hst : b.body[k]? = some st) (hv : Avail W bi k v) :
    v ∉ st.results := by
  intro hr
  obtain ⟨d, t, hd, hva⟩ := hv
  rw [hW.site_result hb hst hr] at hd
  simp only [Option.some.injEq, Prod.mk.injEq] at hd
  obtain ⟨rfl, rfl⟩ := hd
  rcases hva with ⟨_, ht⟩ | ⟨hne, _⟩
  · omega
  · exact hne rfl

theorem avail_succ {bi k : Nat} {b : Block} {st : Stmt} {v : ValueId}
    (hb : f.blocks[bi]? = some b) (hst : b.body[k]? = some st) (hv : Avail W bi (k + 1) v) :
    v ∈ st.results ∨ Avail W bi k v := by
  obtain ⟨d, t, hd, hva⟩ := hv
  rcases hva with ⟨rfl, ht⟩ | h2
  · rcases Nat.lt_or_ge t (k + 1) with h | h
    · exact .inr ⟨d, t, hd, .inl ⟨rfl, by omega⟩⟩
    · have ht' : t = k + 1 := by omega
      subst ht'
      obtain ⟨b', st', hb', hst', hr⟩ := hW.site_stmt hd
      rw [hb] at hb'; cases hb'
      rw [hst] at hst'; cases hst'
      exact .inl hr
  · exact .inr ⟨d, t, hd, .inr h2⟩

theorem avail_entry {v : ValueId} (hv : Avail W 0 0 v) : W.dm v = some (0, 0) := by
  obtain ⟨d, t, hd, hva⟩ := hv
  rcases hva with ⟨rfl, ht⟩ | ⟨hne, ha⟩
  · rw [hd, show t = 0 by omega]
  · obtain ⟨c, hc, _⟩ := ha.strict hne
    rw [hW.root] at hc; cases hc

theorem idx_unique {j j' : Nat} {b b' : Block} (hb : f.blocks[j]? = some b)
    (hb' : f.blocks[j']? = some b') (hid : b.id = b'.id) : j = j' := by
  have h1 := hW.ids j b hb
  have h2 := hW.ids j' b' hb'
  rw [hid, h2] at h1
  exact (Option.some.inj h1).symm

theorem avail_pred {bi j : Nat} {b b2 : Block} {v : ValueId} (hb : f.blocks[bi]? = some b)
    (hj : f.blocks[j]? = some b2) (hsucc : b2.id ∈ termSuccs b.term) (hv : Avail W j 0 v)
    (hnp : W.dm v ≠ some (j, 0)) : Avail W bi b.body.length v := by
  obtain ⟨j', b', hj', hb', hid', hanc⟩ := hW.edges bi b hb b2.id hsucc
  have : j' = j := by
    have := hW.ids j b2 hj
    rw [hj'] at this; exact Option.some.inj this
  subst j'
  obtain ⟨d, t, hd, hva⟩ := hv
  rcases hva with ⟨rfl, ht⟩ | ⟨hne, ha⟩
  · exact absurd (by rw [hd, show t = 0 by omega]) hnp
  obtain ⟨c, hc, hac⟩ := ha.strict hne
  have hab := hac.trans (hanc c hc)
  refine ⟨d, t, hd, ?_⟩
  by_cases hdb : d = bi
  · subst hdb
    obtain ⟨b3, hb3, ht⟩ := hW.site_bound hd
    rw [hb] at hb3; cases hb3
    exact .inl ⟨rfl, ht⟩
  · exact .inr ⟨hdb, hab⟩

/-- The block index of a branch target. -/
theorem block?_index {id : BlockId} {b : Block} (h : f.block? id = some b) :
    ∃ j : Nat, f.blocks[j]? = some b ∧ b.id = id := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 (List.mem_of_find?_eq_some h)
  exact ⟨j, hj, by simpa using List.find?_some h⟩

/-- Available values are defined, hence below the fresh value. -/
theorem avail_lt {i k v : Nat} (h : Avail W i k v) : v < f.freshValue := by
  obtain ⟨d, t, hd, -⟩ := h
  obtain ⟨i', b, hb, hp⟩ := mem_defSites.1 (hW.sitesRev v (d, t) hd)
  have hbm : b ∈ f.blocks := List.mem_of_getElem? hb
  rcases hp with ⟨p, hp, hpv, -⟩ | ⟨j, st, hst, hv, -⟩
  · rw [← hpv]; exact (lt_freshValue hbm).1 p hp
  · exact (lt_freshValue hbm).2 st (List.mem_of_getElem? hst) v hv

end

/-! ## The run-time invariant `Opt.Inv` -/

/-- After a statement (or a call returning): the results are bound (`Opt.Inv.results`, result
types from the signature declarations). -/
theorem inv_results {f : Function} {W : WfData} (hW : WfM f W) {syms fr bi k st rest vals regs}
    (h : Inv f W syms fr bi k) (hb : fr.body = st :: rest)
    (hty : ∀ ts, st.inst.resultTypes (sigOf f) (sigDeclOf f) = some ts → vals.map (·.ty) = ts)
    (hpure : isPure st.inst = true → ∃ a, vals = [a] ∧ evalNode fr (symMem syms) st.inst = some a)
    (hset : fr.regs.setMany st.results vals = some regs) :
    Inv f W syms { fr with regs, body := rest } bi (k + 1) := by
  obtain ⟨hfunc, ⟨b, hbi, hbody, hterm, hk⟩, hslots, hregs, hpd⟩ := h
  rw [hbody] at hb
  obtain ⟨hst, hrest, hklt⟩ := drop_eq_cons hb
  obtain ⟨hlen, hsm⟩ := setMany_spec hset
  have hres : ∀ r ∈ st.results, W.dm r = some (bi, k + 1) := fun r hr => hW.site_result hbi hst hr
  have hnot : ∀ v, Avail W bi k v → v ∉ st.results := by
    intro v ⟨d, t, hv, hva⟩ hr
    rw [hres v hr] at hv
    simp only [Option.some.injEq, Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    rcases hva with ⟨_, ht⟩ | ⟨hne, _⟩
    · omega
    · exact hne rfl
  have hprev : ∀ v, Avail W bi (k + 1) v → W.dm v ≠ some (bi, k + 1) → Avail W bi k v := by
    intro v ⟨d, t, hv, hva⟩ hne
    refine ⟨d, t, hv, ?_⟩
    rcases hva with ⟨rfl, ht⟩ | h2
    · refine .inl ⟨rfl, ?_⟩
      rcases Nat.lt_or_ge t (k + 1) with h | h
      · omega
      · exact absurd (by rw [hv, show t = k + 1 by omega]) hne
    · exact .inr h2
  have hsame : ∀ n, (∀ x ∈ operands n, Avail W bi k x) →
      evalNode { fr with regs, body := rest } (symMem syms) n = evalNode fr (symMem syms) n := by
    intro n hops
    exact evalNode_congr rfl rfl rfl fun x hx => (hsm x).1 (hnot x (hops x hx))
  obtain ⟨ts, hts, htl, htm⟩ := hW.results bi b hbi k st hst
  have hvty := hty ts hts
  refine ⟨hfunc, ⟨b, hbi, by rw [hrest], hterm, hklt⟩, hslots, fun v hv => ?_, fun v n hv hp => ?_⟩
  · by_cases hdv : W.dm v = some (bi, k + 1)
    · obtain ⟨b', st', hb', hst', hr'⟩ := hW.site_stmt hdv
      rw [hbi] at hb'; cases hb'
      rw [hst] at hst'; cases hst'
      obtain ⟨n, hn, hrv⟩ := (hsm v).2 hr'
      have hnl : n < vals.length := by
        rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hn).1
      refine ⟨vals[n], by simpa [List.getElem?_eq_getElem hnl] using hrv, ?_⟩
      rw [htm n v hn, ← hvty]
      simp [List.getElem?_eq_getElem hnl]
    · have hv' := hprev v hv hdv
      obtain ⟨a, ha, hta⟩ := hregs v hv'
      exact ⟨a, by simp only; rw [(hsm v).1 (hnot v hv'), ha], hta⟩
  · obtain ⟨d, j, b', st', hd, hb', hst', hr', hn, hpn⟩ := hp
    by_cases hdv : W.dm v = some (bi, k + 1)
    · rw [hd] at hdv
      simp only [Option.some.injEq, Prod.mk.injEq, Nat.add_right_cancel_iff] at hdv
      obtain ⟨h1, h2⟩ := hdv
      subst d; subst j
      rw [hbi] at hb'; cases hb'
      rw [hst] at hst'; cases hst'
      subst hn
      obtain ⟨a, rfl, ha⟩ := hpure hpn
      obtain ⟨n', hn', hrv⟩ := (hsm v).2 (by rw [hr']; simp)
      rw [hr'] at hn'
      have : n' = 0 := by
        cases n' with
        | zero => rfl
        | succ n' => simp at hn'
      subst this
      simp only at hrv ⊢
      rw [hrv, hsame _ (fun x hx => hW.uses bi b hbi k st hst x hx), ha]
      rfl
    · have hv' := hprev v hv hdv
      simp only
      rw [(hsm v).1 (hnot v hv'), hpd v n hv' ⟨d, j, b', st', hd, hb', hst', hr', hn, hpn⟩,
        hsame n (fun x hx => hW.avail_operand hv' hd hb' hst' (hn ▸ hx))]

/-- Function entry (`Opt.Inv.entry`). -/
theorem inv_entry {f : Function} {W : WfData} (hW : WfM f W) {syms} {b : Block} {args : List Val}
    {regs : Regs} {slots : List (SlotId × Nat)} (hb : f.entry? = some b)
    (hty : args.map (·.ty) = b.params.map (·.2))
    (hr : Regs.empty.setMany (b.params.map (·.1)) args = some regs)
    (hsl : slots.map (·.1) = f.slots.map (·.1)) :
    Inv f W syms ⟨f, regs, slots, b.body, b.term⟩ 0 0 := by
  have hb0 : f.blocks[0]? = some b := by
    simpa [Function.entry?, List.head?_eq_getElem?] using hb
  have hroot : ∀ v, Avail W 0 0 v → W.dm v = some (0, 0) := fun v hv => hW.avail_entry hv
  obtain ⟨hlen, hsm⟩ := setMany_spec hr
  refine ⟨rfl, ⟨b, hb0, by simp, rfl, Nat.zero_le _⟩, fun s hs => ?_, fun v hv => ?_,
    fun v n hv hp => ?_⟩
  · rw [lookup_isSome] at hs ⊢; rw [hsl]; exact hs
  · obtain ⟨b', p, hb', hp, hpv⟩ := hW.site_param' (hroot v hv)
    rw [hb0] at hb'; cases hb'
    have hvm : v ∈ b.params.map (·.1) := List.mem_map.2 ⟨p, hp, hpv⟩
    obtain ⟨n, hn, hrv⟩ := (hsm v).2 hvm
    have hnl : n < args.length := by
      rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hn).1
    refine ⟨args[n], by simpa [List.getElem?_eq_getElem hnl] using hrv, ?_⟩
    have h1 : (b.params.map (·.2))[n]? = some args[n].ty := by
      rw [← hty]; simp [List.getElem?_eq_getElem hnl]
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hn h1
    obtain ⟨q, hq, rfl⟩ := hn
    obtain ⟨q', hq', hq2⟩ := h1
    rw [hq] at hq'; cases hq'
    rw [hW.params 0 b hb0 q (List.mem_of_getElem? hq), hq2]
  · obtain ⟨d, j, _, _, hd, _⟩ := hp
    rw [hroot v hv] at hd; cases hd

/-- Branching from the end of block `bi` to one of its successors (`Opt.Inv.enter`). -/
theorem inv_enter {f : Function} {W : WfData} (hW : WfM f W) {syms fr bi k bc fr'}
    (h : Inv f W syms fr bi k) (hb : fr.body = []) (hbc : bc.block ∈ termSuccs fr.term)
    (he : enterBlock fr bc = .ok fr') :
    ∃ j b2, f.blocks[j]? = some b2 ∧ f.block? bc.block = some b2 ∧ Inv f W syms fr' j 0 := by
  obtain ⟨hfunc, ⟨b, hbi, hbody, hterm, hk⟩, hslots, hregs, hpd⟩ := h
  have hk' : k = b.body.length := by
    rw [hb] at hbody
    have := congrArg List.length hbody
    simp at this; omega
  subst hk'
  obtain ⟨b2, args, regs, hb2, hargs, hty, hset, rfl⟩ := enterBlock_ok he
  rw [hfunc] at hb2
  obtain ⟨j, hj⟩ : ∃ j, f.blocks[j]? = some b2 := by
    have := List.mem_of_find?_eq_some hb2
    exact List.mem_iff_getElem?.1 this
  have hid : b2.id = bc.block := by simpa using List.find?_some hb2
  rw [hterm] at hbc
  obtain ⟨j', b', hj', hb', hid', hanc⟩ := hW.edges bi b hbi bc.block hbc
  have : j' = j := by
    have := hW.ids j b2 hj
    rw [hid, hj'] at this; exact Option.some.inj this
  subst j'
  obtain ⟨hlen, hsm⟩ := setMany_spec hset
  have hup : ∀ v d t, W.dm v = some (d, t) → d ≠ j → Anc W.idom d j →
      Avail W bi b.body.length v := by
    intro v d t hv hne ha
    obtain ⟨c, hc, hac⟩ := ha.strict hne
    have hab := hac.trans (hanc c hc)
    refine ⟨d, t, hv, ?_⟩
    by_cases hdb : d = bi
    · subst hdb
      obtain ⟨b3, hb3, ht⟩ := hW.site_bound hv
      rw [hbi] at hb3; cases hb3
      exact .inl ⟨rfl, ht⟩
    · exact .inr ⟨hdb, hab⟩
  have hnotp : ∀ v d t, W.dm v = some (d, t) → d ≠ j → v ∉ b2.params.map (·.1) := by
    intro v d t hv hne hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    rw [hW.site_param hj hp] at hv
    simp only [Option.some.injEq, Prod.mk.injEq] at hv
    exact hne hv.1.symm
  refine ⟨j, b2, hj, hb2, hfunc, ⟨b2, hj, by simp, rfl, Nat.zero_le _⟩, hslots, fun v hv => ?_,
    fun v n hv hp => ?_⟩
  · obtain ⟨d, t, hdv, hva⟩ := hv
    rcases hva with ⟨hdj, ht⟩ | ⟨hne, ha⟩
    · subst d
      have ht0 : t = 0 := by omega
      subst ht0
      obtain ⟨b3, p, hb3, hp, hpv⟩ := hW.site_param' hdv
      rw [hj] at hb3; cases hb3
      have hvm : v ∈ b2.params.map (·.1) := List.mem_map.2 ⟨p, hp, hpv⟩
      obtain ⟨n, hn, hrv⟩ := (hsm v).2 hvm
      have hnl : n < args.length := by
        rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hn).1
      refine ⟨args[n], by simpa [List.getElem?_eq_getElem hnl] using hrv, ?_⟩
      have h1 : (b2.params.map (·.2))[n]? = some args[n].ty := by
        rw [← hty]; simp [List.getElem?_eq_getElem hnl]
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hn h1
      obtain ⟨q, hq, rfl⟩ := hn
      obtain ⟨q', hq', hq2⟩ := h1
      rw [hq] at hq'; cases hq'
      rw [hW.params j b2 hj q (List.mem_of_getElem? hq), hq2]
    · obtain ⟨a, ha', hta⟩ := hregs v (hup v d t hdv hne ha)
      exact ⟨a, by simp only; rw [(hsm v).1 (hnotp v d t hdv hne), ha'], hta⟩
  · obtain ⟨d, jj, b3, st, hd, hb3, hst, hr3, hn, hpn⟩ := hp
    obtain ⟨d0, t0, hdv, hva⟩ := hv
    rw [hd] at hdv
    simp only [Option.some.injEq, Prod.mk.injEq] at hdv
    obtain ⟨rfl, rfl⟩ := hdv
    rcases hva with ⟨_, ht⟩ | ⟨hne, ha⟩
    · omega
    have hvb := hup v d (jj + 1) hd hne ha
    have hv0 : Avail W j 0 v := ⟨d, jj + 1, hd, .inr ⟨hne, ha⟩⟩
    simp only
    rw [(hsm v).1 (hnotp v d _ hd hne), hpd v n hvb ⟨d, jj, b3, st, hd, hb3, hst, hr3, hn, hpn⟩]
    refine (evalNode_congr (fr := fr) (fr' := { fr with regs, body := b2.body, term := b2.term })
      rfl rfl rfl fun x hx => ?_).symm
    obtain ⟨d', t', hx', hxa⟩ := hW.avail_operand hv0 hd hb3 hst (hn ▸ hx)
    refine (hsm x).1 (hnotp x d' t' hx' ?_)
    rintro rfl
    obtain ⟨d'', t'', hx'', hxa'⟩ := hW.uses d b3 hb3 jj st hst x (hn ▸ hx)
    rw [hx'] at hx''
    simp only [Option.some.injEq, Prod.mk.injEq] at hx''
    obtain ⟨rfl, rfl⟩ := hx''
    rcases hxa' with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact hne h1.symm
    · exact hne (Anc.antisymm hW.rank ha h2)

/-- The invariant reads only registers below the fresh value (`Opt.Inv.regs_congr`). -/
theorem inv_regs_congr {f : Function} {W : WfData} (hW : WfM f W) {syms : String → Option Nat}
    {fr : Frame} {bi k : Nat} (h : Inv f W syms fr bi k) {r : Regs}
    (hr : ∀ v < f.freshValue, r v = fr.regs v) : Inv f W syms { fr with regs := r } bi k where
  func := h.func
  block := h.block
  slots := h.slots
  regs v hv := by show ∃ a, r v = some a ∧ _; rw [hr v (hW.avail_lt hv)]; exact h.regs v hv
  pure v n hv hp := by
    show r v = _
    rw [hr v (hW.avail_lt hv), h.pure v n hv hp]
    obtain ⟨d, j, b, st, hd, hb, hst, -, hi, -⟩ := hp
    symm
    apply evalNode_congr (fr := fr) (fr' := { fr with regs := r }) rfl rfl rfl
    intro x hx
    rw [← hi] at hx
    exact hr x (hW.avail_lt (hW.uses d b hb j st hst x hx))

end WfM

end Opt.MidVal
