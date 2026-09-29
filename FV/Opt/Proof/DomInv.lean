import FV.Opt.Proof.SemFacts

/-!
# The run-time invariant of well-formed functions

`Opt.Inv f W syms fr bi k`: the frame `fr` executes `f` before statement `k` of block `bi`, and
every value available there (`Opt.Avail`) holds a value of its type; a value defined by a pure
statement `v = n` holds `evalNode` of `n` in the *current* registers. This is the dominance lemma
(D) of `docs/contracts/midend.md` as an invariant: it is established at function entry and kept
by every statement, call return and branch (`Inv.results`, `Inv.enter`, `Inv.entry`), using
only the certificate facts `Opt.Wf`.
-/

namespace Opt

open Clif

/-- Memory with link-time symbols `syms` (pure nodes read nothing else of memory). -/
def symMem (syms : String → Option Nat) : Mem := { symbols := syms }

/-- `v` is defined by the pure statement `v = n`. -/
def PureDef (f : Function) (W : WfData) (v : ValueId) (n : Inst) : Prop :=
  ∃ d j b st, W.dm v = some (d, j + 1) ∧ f.blocks[d]? = some b ∧ b.body[j]? = some st ∧
    st.results = [v] ∧ st.inst = n ∧ isPure n = true

/-- The run-time invariant (module doc). -/
structure Inv (f : Function) (W : WfData) (syms : String → Option Nat) (fr : Frame) (bi k : Nat) :
    Prop where
  func : fr.func = f
  block : ∃ b, f.blocks[bi]? = some b ∧ fr.body = b.body.drop k ∧ fr.term = b.term ∧
    k ≤ b.body.length
  slots : ∀ s, (f.slots.lookup s).isSome → (fr.slots.lookup s).isSome
  regs : ∀ v, Avail W bi k v → ∃ a, fr.regs v = some a ∧ W.tm v = some a.ty
  pure : ∀ v n, Avail W bi k v → PureDef f W v n → fr.regs v = evalNode fr (symMem syms) n

/-! ## Registers -/

theorem setMany_spec {r r' : Regs} {xs : List ValueId} {vs : List Val}
    (h : r.setMany xs vs = some r') :
    xs.length = vs.length ∧ ∀ y, (y ∉ xs → r' y = r y) ∧
      (y ∈ xs → ∃ n : Nat, xs[n]? = some y ∧ r' y = vs[n]?) := by
  induction xs generalizing r vs with
  | nil => cases vs <;> simp_all [Regs.setMany]
  | cons x xs ih =>
    cases vs with
    | nil => simp [Regs.setMany] at h
    | cons v vs =>
      simp only [Regs.setMany_cons] at h
      obtain ⟨hl, hy⟩ := ih h
      refine ⟨by simp [hl], fun y => ⟨fun hn => ?_, fun hm => ?_⟩⟩
      · simp only [List.mem_cons, not_or] at hn
        rw [(hy y).1 hn.2, Regs.set_other _ _ hn.1]
      · by_cases hyx : y ∈ xs
        · obtain ⟨n, h1, h2⟩ := (hy y).2 hyx
          exact ⟨n + 1, by simpa using h1, by simpa using h2⟩
        · have : y = x := by simpa [hyx] using hm
          subst this
          exact ⟨0, rfl, by rw [(hy y).1 hyx]; simp⟩

theorem setMany_same {r1 r2 r1' r2' : Regs} {xs : List ValueId} {vs : List Val}
    (h1 : r1.setMany xs vs = some r1') (h2 : r2.setMany xs vs = some r2') :
    ∀ y ∈ xs, r1' y = r2' y := by
  induction xs generalizing r1 r2 vs with
  | nil => simp
  | cons x xs ih =>
    cases vs with
    | nil => simp [Regs.setMany] at h1
    | cons v vs =>
      simp only [Regs.setMany_cons] at h1 h2
      intro y hy
      by_cases hyx : y ∈ xs
      · exact ih h1 h2 y hyx
      · have : y = x := by simpa [hyx] using hy
        subst this
        rw [(setMany_spec h1).2 y |>.1 hyx, (setMany_spec h2).2 y |>.1 hyx]
        simp

theorem setMany_len {r : Regs} {xs : List ValueId} {vs : List Val} (h : xs.length = vs.length) :
    ∃ r', r.setMany xs vs = some r' := by
  induction xs generalizing r vs with
  | nil => cases vs <;> simp_all [Regs.setMany]
  | cons x xs ih =>
    cases vs with
    | nil => simp at h
    | cons v vs => simp only [Regs.setMany_cons]; exact ih (by simpa using h)

theorem lookup_isSome {α : Type} {l : List (Nat × α)} {s : Nat} :
    (l.lookup s).isSome ↔ s ∈ l.map (·.1) := by
  induction l with
  | nil => simp [List.lookup]
  | cons x l ih =>
    obtain ⟨a, b⟩ := x
    simp only [List.lookup, List.map_cons, List.mem_cons]
    by_cases h : s = a
    · subst h; simp
    · simp only [show (s == a) = false by simpa using h, h, false_or]; exact ih

/-! ## Sites -/

section
variable {f : Function} {W : WfData} (hW : Wf f W)
include hW

theorem site_result {i : Nat} {b : Block} {j : Nat} {st : Stmt} {r : ValueId}
    (hb : f.blocks[i]? = some b) (hst : b.body[j]? = some st) (hr : r ∈ st.results) :
    W.dm r = some (i, j + 1) :=
  hW.sites _ _ (mem_defSites.2 ⟨i, b, hb, .inr ⟨j, st, hst, hr, rfl⟩⟩)

theorem site_param {i : Nat} {b : Block} {p : ValueId × Ty} (hb : f.blocks[i]? = some b)
    (hp : p ∈ b.params) : W.dm p.1 = some (i, 0) :=
  hW.sites _ _ (mem_defSites.2 ⟨i, b, hb, .inl ⟨p, hp, rfl, rfl⟩⟩)

/-- A site `(d, j + 1)` is a result of statement `j` of block `d`. -/
theorem site_stmt {v : ValueId} {d j : Nat} (h : W.dm v = some (d, j + 1)) :
    ∃ b st, f.blocks[d]? = some b ∧ b.body[j]? = some st ∧ v ∈ st.results := by
  obtain ⟨i, b, hb, ⟨p, _, _, hs⟩ | ⟨j', st, hst, hr, hs⟩⟩ := mem_defSites.1 (hW.sitesRev _ _ h)
  · cases hs
  · simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨b, st, hb, hst, hr⟩

/-- A site `(d, 0)` is a parameter of block `d`. -/
theorem site_param' {v : ValueId} {d : Nat} (h : W.dm v = some (d, 0)) :
    ∃ b p, f.blocks[d]? = some b ∧ p ∈ b.params ∧ p.1 = v := by
  obtain ⟨i, b, hb, ⟨p, hp, h1, hs⟩ | ⟨j', st, hst, hr, hs⟩⟩ := mem_defSites.1 (hW.sitesRev _ _ h)
  · simp only [Prod.mk.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    exact ⟨b, p, hb, hp, h1⟩
  · simp at hs

/-- Every site is within its block. -/
theorem site_bound {v : ValueId} {d t : Nat} (h : W.dm v = some (d, t)) :
    ∃ b, f.blocks[d]? = some b ∧ t ≤ b.body.length := by
  obtain ⟨i, b, hb, ⟨p, _, _, hs⟩ | ⟨j', st, hst, _, hs⟩⟩ := mem_defSites.1 (hW.sitesRev _ _ h)
  · simp only [Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs; exact ⟨b, hb, Nat.zero_le _⟩
  · simp only [Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
    exact ⟨b, hb, (List.getElem?_eq_some_iff.1 hst).1⟩

/-- Operands of an available definition are available. -/
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

end

theorem drop_eq_cons {l : List Stmt} {k : Nat} {st : Stmt} {rest : List Stmt}
    (h : l.drop k = st :: rest) : l[k]? = some st ∧ l.drop (k + 1) = rest ∧ k < l.length := by
  have h1 : l[k]? = some st := by
    have := congrArg (·[0]?) h
    simpa [List.getElem?_drop] using this
  refine ⟨h1, ?_, (List.getElem?_eq_some_iff.1 h1).1⟩
  rw [← List.tail_drop, h]; rfl

/-! ## Preservation -/

/-- After a statement (or a call returning): the results are bound. -/
theorem Inv.results {f : Function} {W : WfData} (hW : Wf f W) {syms fr bi k st rest vals regs}
    (h : Inv f W syms fr bi k) (hb : fr.body = st :: rest)
    (hty : ∀ ts, st.inst.resultTypes (sigOf f) (fun _ => none) = some ts → vals.map (·.ty) = ts)
    (hpure : isPure st.inst = true → ∃ a, vals = [a] ∧ evalNode fr (symMem syms) st.inst = some a)
    (hset : fr.regs.setMany st.results vals = some regs) :
    Inv f W syms { fr with regs, body := rest } bi (k + 1) := by
  obtain ⟨hfunc, ⟨b, hbi, hbody, hterm, hk⟩, hslots, hregs, hpd⟩ := h
  rw [hbody] at hb
  obtain ⟨hst, hrest, hklt⟩ := drop_eq_cons hb
  obtain ⟨hlen, hsm⟩ := setMany_spec hset
  -- results are at site (bi, k + 1)
  have hres : ∀ r ∈ st.results, W.dm r = some (bi, k + 1) := fun r hr => site_result hW hbi hst hr
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
    · obtain ⟨b', st', hb', hst', hr'⟩ := site_stmt hW hdv
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
        hsame n (fun x hx => avail_operand hW hv' hd hb' hst' (hn ▸ hx))]

/-- Function entry. -/
theorem Inv.entry {f : Function} {W : WfData} (hW : Wf f W) {syms} {b : Block} {args : List Val}
    {regs : Regs} {slots : List (SlotId × Nat)} (hb : f.entry? = some b)
    (hty : args.map (·.ty) = b.params.map (·.2))
    (hr : Regs.empty.setMany (b.params.map (·.1)) args = some regs)
    (hsl : slots.map (·.1) = f.slots.map (·.1)) :
    Inv f W syms ⟨f, regs, slots, b.body, b.term⟩ 0 0 := by
  have hb0 : f.blocks[0]? = some b := by
    simpa [Function.entry?, List.head?_eq_getElem?] using hb
  have hroot : ∀ v, Avail W 0 0 v → W.dm v = some (0, 0) := by
    intro v ⟨d, t, hv, hva⟩
    rcases hva with ⟨rfl, ht⟩ | ⟨hne, ha⟩
    · rw [hv, show t = 0 by omega]
    · obtain ⟨c, hc, _⟩ := ha.strict hne
      rw [hW.root] at hc; cases hc
  obtain ⟨hlen, hsm⟩ := setMany_spec hr
  refine ⟨rfl, ⟨b, hb0, by simp, rfl, Nat.zero_le _⟩, fun s hs => ?_, fun v hv => ?_,
    fun v n hv hp => ?_⟩
  · rw [lookup_isSome] at hs ⊢; rw [hsl]; exact hs
  · obtain ⟨b', p, hb', hp, hpv⟩ := site_param' hW (hroot v hv)
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

/-- Branching from the end of block `bi` to one of its successors. -/
theorem Inv.enter {f : Function} {W : WfData} (hW : Wf f W) {syms fr bi k bc fr'}
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
  -- values available at the start of `j` other than its parameters are available at the end of `bi`
  have hup : ∀ v d t, W.dm v = some (d, t) → d ≠ j → Anc W.idom d j →
      Avail W bi b.body.length v := by
    intro v d t hv hne ha
    obtain ⟨c, hc, hac⟩ := ha.strict hne
    have hab := hac.trans (hanc c hc)
    refine ⟨d, t, hv, ?_⟩
    by_cases hdb : d = bi
    · subst hdb
      obtain ⟨b3, hb3, ht⟩ := site_bound hW hv
      rw [hbi] at hb3; cases hb3
      exact .inl ⟨rfl, ht⟩
    · exact .inr ⟨hdb, hab⟩
  have hnotp : ∀ v d t, W.dm v = some (d, t) → d ≠ j → v ∉ b2.params.map (·.1) := by
    intro v d t hv hne hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    rw [site_param hW hj hp] at hv
    simp only [Option.some.injEq, Prod.mk.injEq] at hv
    exact hne hv.1.symm
  refine ⟨j, b2, hj, hb2, hfunc, ⟨b2, hj, by simp, rfl, Nat.zero_le _⟩, hslots, fun v hv => ?_,
    fun v n hv hp => ?_⟩
  · obtain ⟨d, t, hdv, hva⟩ := hv
    rcases hva with ⟨hdj, ht⟩ | ⟨hne, ha⟩
    · subst d
      have ht0 : t = 0 := by omega
      subst ht0
      obtain ⟨b3, p, hb3, hp, hpv⟩ := site_param' hW hdv
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
    -- operands are not parameters of `j`
    obtain ⟨d', t', hx', hxa⟩ := avail_operand hW hv0 hd hb3 hst (hn ▸ hx)
    refine (hsm x).1 (hnotp x d' t' hx' ?_)
    rintro rfl
    obtain ⟨d'', t'', hx'', hxa'⟩ := hW.uses d b3 hb3 jj st hst x (hn ▸ hx)
    rw [hx'] at hx''
    simp only [Option.some.injEq, Prod.mk.injEq] at hx''
    obtain ⟨rfl, rfl⟩ := hx''
    rcases hxa' with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact hne h1.symm
    · exact hne (Anc.antisymm hW.rank ha h2)

/-! ## Availability -/

theorem Avail.mono {W : WfData} {i k k2 : Nat} {v : ValueId} (h : Avail W i k v) (hk : k ≤ k2) :
    Avail W i k2 v := by
  obtain ⟨d, t, hv, h1 | h2⟩ := h
  · exact ⟨d, t, hv, .inl ⟨h1.1, by omega⟩⟩
  · exact ⟨d, t, hv, .inr h2⟩

section
variable {f : Function} {W : WfData} (hW : Wf f W)
include hW

theorem avail_not_result {bi k : Nat} {b : Block} {st : Stmt} {v : ValueId}
    (hb : f.blocks[bi]? = some b) (hst : b.body[k]? = some st) (hv : Avail W bi k v) :
    v ∉ st.results := by
  intro hr
  obtain ⟨d, t, hd, hva⟩ := hv
  rw [site_result hW hb hst hr] at hd
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
      obtain ⟨b', st', hb', hst', hr⟩ := site_stmt hW hd
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

/-- The block index of a branch target. -/
theorem block?_index {id : BlockId} {b : Block} (h : f.block? id = some b) :
    ∃ j : Nat, f.blocks[j]? = some b ∧ b.id = id := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 (List.mem_of_find?_eq_some h)
  exact ⟨j, hj, by simpa using List.find?_some h⟩

/-- Values available at the start of a successor `j` of `bi`, other than `j`'s parameters,
are available at the end of `bi` (the edge certificate). -/
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
    obtain ⟨b3, hb3, ht⟩ := site_bound hW hd
    rw [hb] at hb3; cases hb3
    exact .inl ⟨rfl, ht⟩
  · exact .inr ⟨hdb, hab⟩

end

end Opt
