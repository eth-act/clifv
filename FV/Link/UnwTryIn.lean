import FV.Link.UnwFnsComplete
import FV.Backend.Proof.LowerComplete
import FV.Backend.Proof.SpillEdges
import FV.Backend.Proof.SpillStep4Cfg
import FV.Backend.Proof.DeadCleanupPrepareMap
import FV.Backend.Proof.TryRegs

/-!
# The `try_call` handlers of the prepared code from the input (S10g, #404)

`TryInfoOk vcp` (`FV/Link/UnwFnsComplete.lean`) is what `callSites_complete` and
`padsNonzero_complete` need of the prepared code `vcp` (through `handlersOk_of_tryInfo`,
`padsOk_of_tryInfo`). Here it follows from the input:

* `tryTablesB f`: every `try_call`/`try_call_indirect` exception table of `f` has at least one
  item, each a `tag n` item with `n ≤ 1` (Rust's cleanup and catch handlers; no `default`, no
  `context` item) — decidable on the CLIF function;
* `tryInfoOk_of_input`: on in-scope input (`Dominated`, `LowerScope`, `ArityOk`) with
  `tryTablesB`, the pipeline's prepared code `prepare (prune (lowerFunction f))` satisfies
  `TryInfoOk`.

The tags: `lowerFunction` builds a `tryCall`'s handlers from the table's items
(`exnTableOpnd`, `tryInfoOf`), `prune` deletes instructions and `prepare` retargets
(`setTargets` keeps the tags). The labels: every `tryCall` is the last instruction of its block
(`TryBack`, through the lowering, `prepare` and the cleanup), so its handlers' labels are
successors in the prepared CFG (`cfg_spec`), and no edge enters the entry block
(`EdgesOk.entry`, `preds_empty`).
-/

namespace Link.EhCheck.Complete

set_option autoImplicit false

open Backend Backend.Proof Backend.Proof.Driver E2E

/-! ## The input condition -/

/-- An exception-table item `lowerFunction`'s unwinding covers: a cleanup (`tag 0`) or catch
(`tag 1`) handler. -/
def itemOkB : Clif.ExnItem → Bool
  | .tag n _ => decide (n ≤ 1)
  | _ => false

/-- **The `try_call` tables of `f`**: each has at least one item, each a `tag 0`/`tag 1`
handler. -/
def tryTablesB (f : Clif.Function) : Bool :=
  f.blocks.all fun B => match B.term with
    | .tryCall _ _ et | .tryCallIndirect _ _ et => !et.items.isEmpty && et.items.all itemOkB
    | _ => true

theorem tryTables_of {f : Clif.Function} (h : tryTablesB f = true) {B : Clif.Block}
    (hB : B ∈ f.blocks) {et : Clif.ExnTable} (ht : IsTryWith B.term et) :
    et.items ≠ [] ∧ ∀ x ∈ et.items, ∃ n d, x = .tag n d ∧ n ≤ 1 := by
  have hb := List.all_eq_true.1 h B hB
  have hb' : (!et.items.isEmpty && et.items.all itemOkB) = true := by
    rcases ht with ⟨fn, args, he⟩ | ⟨c, args, he⟩ <;> rw [he] at hb <;> exact hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true] at hb'
  refine ⟨hb'.1, fun x hx => ?_⟩
  have := hb'.2 x hx
  cases x with
  | tag n d => exact ⟨n, d, rfl, by simpa [itemOkB] using this⟩
  | default d => simp [itemOkB] at this
  | context v => simp [itemOkB] at this

/-! ## The tags -/

/-- A `tryCall`'s handlers: at least one, each a `tag 0`/`tag 1` handler. -/
def TagsOk (ti : TryInfo) : Prop :=
  ti.handlers ≠ [] ∧ ∀ h ∈ ti.handlers, ∃ n l, h = .tag n l ∧ n ≤ 1

/-- The instruction property: every `tryCall`'s handlers are `TagsOk`. -/
def TryTags (m : MInst) : Prop := ∀ c ti, m = .tryCall c ti → TagsOk ti

theorem mapM_items : ∀ (l : List Clif.ExnItem) (its : List (Option Nat)),
    (∀ x ∈ l, ∃ n d, x = .tag n d ∧ n ≤ 1) →
    l.mapM (fun
      | .tag n _ => (pure (some n) : Except String (Option Nat))
      | .default _ => pure none
      | .context _ => throw "exception table context items are not supported") = .ok its →
    its.length = l.length ∧ ∀ o ∈ its, ∃ n, o = some n ∧ n ≤ 1
  | [], its, _, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | x :: l, its, hl, h => by
    obtain ⟨n, d, rfl, hn⟩ := hl x (by simp)
    simp only [List.mapM_cons, pure, Except.pure, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i its' hr
      simp only [Except.ok.injEq] at h
      subst h
      obtain ⟨h1, h2⟩ := mapM_items l its' (fun y hy => hl y (by simp [hy])) hr
      refine ⟨by simp [h1], fun o ho => ?_⟩
      rcases List.mem_cons.1 ho with rfl | ho
      · exact ⟨n, rfl, hn⟩
      · exact h2 o ho

/-- The item kinds `exnTableOpnd` reads off a table of `tag 0`/`tag 1` items. -/
theorem exnTableOpnd_items {f : Clif.Function} {et : Clif.ExnTable} {sig : Clif.Signature}
    {items : List (Option Nat)} (h : exnTableOpnd f et = .ok (sig, items))
    (ht : ∀ x ∈ et.items, ∃ n d, x = .tag n d ∧ n ≤ 1) :
    items.length = et.items.length ∧ ∀ o ∈ items, ∃ n, o = some n ∧ n ≤ 1 := by
  unfold exnTableOpnd at h
  cases hs : f.sigDecls.lookup et.sig with
  | none => simp [hs] at h
  | some sig' =>
    simp only [hs] at h
    split at h
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    · simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · split at h
        · cases h
        · rename_i its hits
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact mapM_items et.items its ht hits

/-- `tryInfoOf`'s handlers on such items. -/
theorem tryInfoOf_tags {sig : Clif.Signature} {items : List (Option Nat)} {ls : List Label}
    {info : TryInfo} (h : tryInfoOf sig items ls = some info) (hne : items ≠ [])
    (hit : ∀ o ∈ items, ∃ n, o = some n ∧ n ≤ 1) : TagsOk info := by
  unfold tryInfoOf at h
  split at h
  · cases h
  · rename_i hlen
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen
    cases h
    refine ⟨?_, fun hd hhd => ?_⟩
    · obtain ⟨o, os, rfl⟩ := List.exists_cons_of_ne_nil hne
      obtain ⟨l, ls', rfl⟩ : ∃ l ls', ls = l :: ls' := by
        cases ls with
        | nil => simp at hlen
        | cons l ls' => exact ⟨l, ls', rfl⟩
      simp
    · simp only [List.mem_map] at hhd
      obtain ⟨⟨o, l⟩, hp, rfl⟩ := hhd
      obtain ⟨n, rfl, hn⟩ := hit o (List.of_mem_zip hp).1
      exact ⟨n, l, rfl, hn⟩

/-! ## Lists whose `tryCall`s are last and well tagged -/

/-- No `tryCall` in `l`. -/
def NoTry (l : List MInst) : Prop := ∀ m ∈ l, ∀ c ti, m ≠ .tryCall c ti

/-- A `tryCall` of `l` is its last element. -/
def LastOnly (l : List MInst) : Prop :=
  ∀ k c ti, l[k]? = some (.tryCall c ti) → k + 1 = l.length

/-- `l`'s `tryCall`s are last and `TryTags`. -/
def Good (l : List MInst) : Prop := LastOnly l ∧ ∀ m ∈ l, TryTags m

theorem good_noTry {l : List MInst} (h : NoTry l) : Good l :=
  ⟨fun _ c ti hk => absurd rfl (h _ (List.mem_of_getElem? hk) c ti),
    fun m hm c ti he => absurd he (h m hm c ti)⟩

theorem good_append {A B : List MInst} (hA : NoTry A) (hB : Good B) : Good (A ++ B) := by
  refine ⟨fun k c ti hk => ?_, fun m hm => ?_⟩
  · by_cases hkA : k < A.length
    · rw [List.getElem?_append_left hkA] at hk
      exact absurd rfl (hA _ (List.mem_of_getElem? hk) c ti)
    · rw [List.getElem?_append_right (by omega)] at hk
      have := hB.1 _ c ti hk
      simp only [List.length_append]
      omega
  · rcases List.mem_append.1 hm with hm | hm
    · exact fun c ti he => absurd he (hA m hm c ti)
    · exact hB.2 m hm

theorem mapRegs_tryCall {R : Reg → Reg} {m : MInst} {c : CallInfo} {ti : TryInfo}
    (h : m.mapRegs R = .tryCall c ti) : ∃ c0, m = .tryCall c0 ti := by
  cases m <;> simp only [MInst.mapRegs, reduceCtorEq] at h
  rename_i c0 ti0
  simp only [MInst.tryCall.injEq] at h
  exact ⟨c0, by rw [h.2]⟩

theorem good_map (R : Reg → Reg) {l : List MInst} (h : Good l) : Good (l.map (·.mapRegs R)) := by
  refine ⟨fun k c ti hk => ?_, fun m hm c ti he => ?_⟩
  · rw [List.getElem?_map] at hk
    cases hlk : l[k]? with
    | none => rw [hlk] at hk; cases hk
    | some m0 =>
      rw [hlk] at hk
      simp only [Option.map_some, Option.some.injEq] at hk
      obtain ⟨c0, rfl⟩ := mapRegs_tryCall hk
      rw [List.length_map]
      exact h.1 k c0 ti hlk
  · obtain ⟨m0, hm0, rfl⟩ := List.mem_map.1 hm
    obtain ⟨c0, rfl⟩ := mapRegs_tryCall he
    exact h.2 _ hm0 c0 ti rfl

theorem noTry_map (R : Reg → Reg) {l : List MInst} (h : NoTry l) : NoTry (l.map (·.mapRegs R)) := by
  intro m hm
  obtain ⟨m0, hm0, rfl⟩ := List.mem_map.1 hm
  exact notTry_mapRegs R m0 (h m0 hm0)

/-- `lowerFunction`'s `tryCall`: the last call of code without `tryCall`, with `info`. -/
theorem good_tryFix {info : TryInfo} {ms : List MInst} (hms : NoTry ms) (hi : TagsOk info) :
    Good (tryFix info ms) := by
  unfold tryFix
  split
  · rename_i c _
    refine good_append (fun m hm => hms m (List.dropLast_subset _ hm)) ⟨fun k c' ti hk => ?_,
      fun m hm c' ti he => ?_⟩
    · cases k with
      | zero => rfl
      | succ k => simp at hk
    · simp only [List.mem_singleton] at hm
      subst hm
      simp only [MInst.tryCall.injEq] at he
      rw [← he.2]
      exact hi
  · exact good_noTry hms

/-! ## The lowered code -/

theorem noTry_extra (results : List Nat) (rss : List (List Reg)) :
    NoTry (extraOf results rss) := by
  intro m hm c ti he
  obtain ⟨s, a, b, rfl⟩ := mem_extraOf hm
  cases he

/-- **The blocks of `lowerFunction`'s VCode**: every `tryCall` is its block's last instruction,
with `TagsOk` handlers, on input with `tryTablesB`. -/
theorem lower_good {f : Clif.Function} {vc : VCode} (hs : LowerScope f)
    (ht : tryTablesB f = true) (hl : lowerFunction f = .ok vc) :
    ∀ vb ∈ vc.blocks.toList, Good vb.insts.toList := by
  obtain ⟨ctx, ranges, st0, bl, hb, hlb, hvb, -, -⟩ := lowerFunction_run hs.subsetE hl
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  have hemp := lowBlocks_emptied hlb
  rw [hvb]
  intro vb hvb'
  obtain ⟨R, -, ⟨bi, B, L, hB, hL, rfl⟩ | ⟨B, L, e, -, he, rfl⟩⟩ := mem_vcBlocksOf hvb'
  · simp only [fixBlock, Array.toList_map, rawBlock]
    apply good_map
    obtain ⟨-, hcall, htst, nl0, nl', hterm⟩ := hspec bi B L hB hL
    rw [List.append_assoc]
    refine good_append ?_ (good_append ?_ ?_)
    · intro m hm c ti he
      unfold pre at hm
      split at hm
      · simp only [List.mem_cons] at hm
        rcases hm with rfl | hm
        · cases he
        · simp only [entryLoads, List.mem_filterMap] at hm
          obtain ⟨q, -, hq⟩ := hm
          unfold entryLoadOf at hq
          split at hq
          · cases hq; cases he
          · cases hq
      · simp at hm
    · intro m hm
      simp only [List.mem_flatten, List.mem_map, List.mem_range] at hm
      obtain ⟨sg, ⟨j, -, rfl⟩, hm⟩ := hm
      unfold seg at hm
      rw [hB, hL] at hm
      simp only at hm
      split at hm
      · rename_i stm sl hstm hsl
        obtain ⟨tr, hrun⟩ := hcall j sl hsl
        have h1 := emitted_of_run hrun (hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl))
        refine noTry_map id ?_ m hm
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact h1 x hx
        · exact noTry_extra _ _ x hx
      · simp at hm
    · unfold tseg
      rw [hL]
      simp only
      apply good_map
      obtain ⟨hn, hy⟩ := lowTerm_spec hterm
      cases htry : B.term.isTry with
      | false =>
        obtain ⟨htl, -, out, tr, hc⟩ := hn htry
        rw [htl]
        exact good_noTry (emitted_of_run hc htst)
      | true =>
        obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := by
          cases hB' : B.term <;> rw [hB'] at htry <;> simp [Clif.Terminator.isTry] at htry
          · exact ⟨_, .inl ⟨_, _, rfl⟩⟩
          · exact ⟨_, .inr ⟨_, _, rfl⟩⟩
        obtain ⟨T, htl, -, hex, -, -, hinfo, out, tr, hc⟩ := hy et het
        rw [htl]
        obtain ⟨hne, hall⟩ := tryTables_of ht (List.mem_of_getElem? hB) het
        obtain ⟨hlen, hit⟩ := exnTableOpnd_items hex hall
        have hne' : T.items ≠ [] := by
          intro h0; rw [h0] at hlen; exact hne (List.eq_nil_of_length_eq_zero hlen.symm)
        exact good_tryFix (emitted_of_run hc rfl) (tryInfoOf_tags hinfo hne' hit)
  · obtain ⟨tl, hi⟩ := edgeBlocks_insts he
    simp only [fixBlock, hi, Array.toList_map]
    apply good_map
    exact good_noTry (by intro m hm c ti h; simp at hm; subst hm; cases h)

/-! ## `prepare` and the cleanup -/

theorem good_cons {i : MInst} {l : List MInst} (h : Good (i :: l)) : Good l :=
  ⟨fun k c ti hk => by
      have := h.1 (k + 1) c ti (by simpa using hk)
      simp only [List.length_cons] at this
      omega,
    fun m hm => h.2 m (List.mem_cons_of_mem _ hm)⟩

/-- Deleting instructions keeps `Good`. -/
theorem good_sublist {xs ys : List MInst} (hs : xs.Sublist ys) (h : Good ys) : Good xs := by
  induction hs with
  | slnil => exact h
  | cons i _ ih => exact ih (good_cons h)
  | @cons_cons xs ys i hs ih =>
    have hy := ih (good_cons h)
    refine ⟨fun k c ti hk => ?_, fun m hm => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        have := h.1 0 c ti rfl
        simp only [List.length_cons] at this ⊢
        have hy0 : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hy0
        simp [List.sublist_nil.1 hs]
      | succ k =>
        have := hy.1 k c ti (by simpa using hk)
        simp only [List.length_cons]
        omega
    · rcases List.mem_cons.1 hm with rfl | hm
      · exact h.2 _ (List.mem_cons_self ..)
      · exact hy.2 m hm

/-- `setTargets` keeps a `tryCall`'s tags. -/
theorem setTargets_tags {t t' : MInst} {ls : List Label} (h : t.setTargets ls = some t')
    (ht : TryTags t) : TryTags t' := by
  intro c ti he
  subst he
  unfold MInst.setTargets at h
  split at h
  · cases h
  · cases h
  · cases h
  · split at h <;> cases h
  · rename_i c0 ti0
    split at h
    · rename_i hlen
      simp only [Option.some.injEq, MInst.tryCall.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hne, hall⟩ := ht _ ti0 rfl
      refine ⟨?_, fun hd hhd => ?_⟩
      · obtain ⟨h0, hs0, e0⟩ := List.exists_cons_of_ne_nil hne
        obtain ⟨l0, ls0, rfl⟩ : ∃ l0 ls0, ls = l0 :: ls0 := by
          cases ls with
          | nil => simp at hlen
          | cons l0 ls0 => exact ⟨l0, ls0, rfl⟩
        simp [e0]
      · simp only [List.mem_map] at hhd
        obtain ⟨⟨h0, l⟩, hp, rfl⟩ := hhd
        obtain ⟨n, l', rfl, hn⟩ := hall h0 (List.of_mem_zip hp).1
        exact ⟨n, l, rfl, hn⟩
    · cases h
  · cases h

/-- A block whose last instruction is replaced by its retargeting stays `Good`. -/
theorem good_retarget {l : List MInst} {t t' : MInst} {ls : List Label} (h : Good l)
    (hb : l.getLast? = some t) (hset : t.setTargets ls = some t') : Good (l.dropLast ++ [t']) := by
  have hne : l ≠ [] := by rintro rfl; simp at hb
  have hlast : l = l.dropLast ++ [t] := by
    rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at hb
    rw [← hb]; exact (List.dropLast_concat_getLast hne).symm
  have hnt : NoTry l.dropLast := by
    intro m hm c ti he
    subst he
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hm
    have hk' : l[k]? = some (.tryCall c ti) := by
      rw [hlast, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1]; exact hk
    have h1 := h.1 k c ti hk'
    have h2 := (List.getElem?_eq_some_iff.1 hk).1
    rw [List.length_dropLast] at h2
    omega
  refine good_append hnt ⟨fun k c ti hk => ?_, fun m hm => ?_⟩
  · cases k with
    | zero => rfl
    | succ k => simp at hk
  · simp only [List.mem_singleton] at hm
    subst hm
    exact setTargets_tags hset (h.2 t (by rw [hlast]; simp))

/-- **`prepare` keeps `Good` blocks.** -/
theorem prepare_good {vc vcp : VCode} (hp : prepare vc = .ok vcp)
    (h : ∀ vb ∈ vc.blocks.toList, Good vb.insts.toList) :
    ∀ vb ∈ vcp.blocks.toList, Good vb.insts.toList := by
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, -, -, hS, -, rfl⟩ := Prep.prepare_facts hp
  intro vb hvb
  simp only [Array.toList_map, List.mem_map] at hvb
  obtain ⟨i, -, rfl⟩ := hvb
  by_cases hi2 : i < (B ++ E).size
  · rw [getElem!_pos (B ++ E) i hi2]
    by_cases hiB : i < B.size
    · rw [Array.getElem_append_left hiB]
      have hi1 : i < (Prep.keep vc.blocks (reachable ss0)).size := by rw [← hS.size]; exact hiB
      obtain ⟨b, hb, e, -⟩ := Prep.keep_src hi1
      have hmem : (Prep.keep vc.blocks (reachable ss0))[i] ∈ vc.blocks.toList := by rw [e]; simp
      rcases hS.rw i hi1 hiB with h' | ⟨t, t', ls, h1, -, h3, h4, -⟩
      · rw [h']; exact h _ hmem
      · rw [h4]
        simp only [Array.toList_push, Array.toList_pop]
        refine good_retarget (h _ hmem) ?_ h3
        rw [List.getLast?_eq_getElem?]
        rw [Array.back?_eq_getElem?] at h1
        simpa using h1
    · rw [Array.getElem_append_right (Nat.le_of_not_lt hiB)]
      have he : i - B.size < E.size := by simp at hi2; omega
      obtain ⟨l, hl⟩ := hS.edges _ he
      rw [hl]
      exact good_noTry (by intro m hm c ti h; simp at hm; subst hm; cases h)
  · rw [getElem!_neg (B ++ E) i hi2]
    exact good_noTry (fun m hm => absurd hm (by show m ∉ ([] : List MInst); simp))

/-! ## The handlers' landing pads -/

theorem findIdx?_first {α : Type} {p : α → Bool} {xs : Array α} {k : Nat}
    (h : xs.findIdx? p = some k) : ∃ hk : k < xs.size, p xs[k] = true ∧ ∀ i (hi : i < k), p xs[i] = false := by
  rw [Array.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hk, h1, h2⟩ := h
  exact ⟨hk, h1, fun i hi => by simpa using h2 i hi⟩

/-- **`TryInfoOk` of the pipeline's prepared code from the input**: on in-scope input whose
`try_call` tables have only `tag 0`/`tag 1` items (`tryTablesB`), `prepare (prune vc)` of
`lowerFunction`'s output satisfies `TryInfoOk`. -/
theorem tryInfoOk_of_input {f : Clif.Function} {vc vcp : VCode} (hd : Dominated f)
    (hs : LowerScope f) (har : Spill.ArityOk f) (ht : tryTablesB f = true)
    (hl : lowerFunction f = .ok vc) (hp : prepare (DeadCleanup.prune vc) = .ok vcp) :
    TryInfoOk vcp := by
  obtain ⟨raw, hraw, rfl⟩ := DeadCleanup.prune_prepare_ok_inv hp
  have hgraw := prepare_good hraw (lower_good hs ht hl)
  have hg : ∀ vb ∈ (DeadCleanup.preparedCleanup vc raw).blocks.toList, Good vb.insts.toList := by
    intro vb hvb
    rw [DeadCleanup.preparedCleanup_blocks, Array.toList_map, List.mem_map] at hvb
    obtain ⟨vb0, h0, rfl⟩ := hvb
    exact good_sublist (DeadCleanup.preparedCleanupBlock_sublist vc vb0) (hgraw vb0 h0)
  obtain ⟨ss, ps, hcfg⟩ := Spill.cfg_ok_of_prepare hraw (prepDomain_of_lower hs hl hs.nonempty)
  have hent := (Spill.edgesHyp_of hd hs har hl hraw ss ps hcfg).entry.2.1
  have hcfg' : (DeadCleanup.preparedCleanup vc raw).cfg = .ok (ss, ps) := by
    rw [DeadCleanup.preparedCleanup_cfg]; exact hcfg
  have cs := Prep.cfg_spec hcfg'
  intro vb hvb c ti hi
  obtain ⟨htags, -⟩ := hg vb hvb
  have hgood := hg vb hvb
  obtain ⟨hne, hall⟩ := hgood.2 _ hi c ti rfl
  refine ⟨hne, fun h hh => ⟨hall h hh, ?_⟩⟩
  obtain ⟨b, hb⟩ := List.mem_iff_getElem?.1 hvb
  have hb' : (DeadCleanup.preparedCleanup vc raw).blocks[b]? = some vb := by simpa using hb
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hi
  have hlast := htags k c ti hk
  have hback : vb.insts.back? = some (.tryCall c ti) := by
    rw [Array.back?_eq_getElem?, show vb.insts.size - 1 = k by simp at hlast; omega]
    simpa using hk
  obtain ⟨t, ts, ht1, -, hts, -, htgt⟩ := cs.blk b vb hb'
  rw [hback, Option.some.injEq] at ht1
  subst ht1
  obtain ⟨j, hj⟩ : ∃ j, (MInst.tryCall c ti).targets[j]? = some h.label := by
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hh
    exact ⟨j, by
      rw [MInst.targets, List.getElem?_append_left (by simpa using (List.getElem?_eq_some_iff.1 hj).1),
        List.getElem?_map, hj]; rfl⟩
  obtain ⟨s, hsj, hlab⟩ := htgt j h.label hj
  obtain ⟨hsz, hp1, hp2⟩ := findIdx?_first hlab
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact Spill.preds_empty hcfg' hent hts (by simpa using Array.mem_of_getElem? hsj)
  refine ⟨⟨_, Array.getElem_mem_toList hsz, by simpa using hp1⟩, ?_⟩
  intro he
  have h0 := hp2 0 (Nat.pos_of_ne_zero hs0)
  rw [Array.getElem?_eq_getElem (by omega)] at he
  simp only [Option.map_some, Option.some.injEq] at he
  simp [he] at h0

/-- **`callSites` succeeds on the pipeline's emitted code, from the input**: `callSites_complete`
with `HandlersOk` from `tryInfoOk_of_input`. -/
theorem callSites_complete_input {f : Clif.Function} {vc vcp : VCode} {rf : RFunc} {af : AFunc}
    {k : Nat} {fa : FnAsm} (hd : Dominated f) (hs : LowerScope f) (har : Spill.ArityOk f)
    (ht : tryTablesB f = true) (hl : lowerFunction f = .ok vc)
    (hp : prepare (DeadCleanup.prune vc) = .ok vcp) (halloc : lowerRFunc vcp rf = .ok af)
    (hsize : rf.blocks.size = vcp.blocks.size) (hemit : emitFunc k af = .ok fa) :
    ∃ l, callSites af fa = .ok l :=
  callSites_complete hemit (handlersOk_of_tryInfo halloc hsize (tryInfoOk_of_input hd hs har ht hl hp))

/-- **`padsNonzeroB` holds of the pipeline's emitted code, from the input**:
`padsNonzero_complete` with `PadsOk` from `tryInfoOk_of_input`. -/
theorem padsNonzero_complete_input {f : Clif.Function} {vc vcp : VCode} {rf : RFunc} {af : AFunc}
    {k : Nat} {fa : FnAsm} {fb : FnBin} (hd : Dominated f) (hs : LowerScope f)
    (har : Spill.ArityOk f) (ht : tryTablesB f = true) (hl : lowerFunction f = .ok vc)
    (hp : prepare (DeadCleanup.prune vc) = .ok vcp) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlay : fa.layout = .ok fb) {vb : VBlock}
    {items : Array RItem} (hvb : vcp.blocks[0]? = some vb) (hit : rf.blocks[0]? = some items) :
    padsNonzeroB af fa = true :=
  padsNonzero_complete halloc hemit hlay hvb hit
    (padsOk_of_tryInfo halloc (tryInfoOk_of_input hd hs har ht hl hp) hvb)

end Link.EhCheck.Complete
