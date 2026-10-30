import FV.Opt.Proof.CompleteUnreachable
import FV.Opt.Proof.CheckSpec
import FV.Opt.Proof.SimpSim
import FV.Opt.Dce

/-!
# Completeness of the DCE stage (M1)

On a well-formed function (`check g = .ok info`), the output of `Opt.dce` passes `check` and the
edit validator `editOk id` (`dce_complete`), so `Opt.optimizeReport` never stops at a DCE stage.

The pass keeps exactly the statements that are not removable or have a live result
(`dce_eq`), where the live set is closed: the operands of kept non-removable statements and of
terminators are live, and so are the operands of a removable statement with a live result
(`dceLive_closed`; the mark loop's fuel suffices: every round that leaves work behind marks a new
removable definition).
-/

namespace Opt

open Clif

/-! ## `dce` with named loop bodies -/

abbrev DefOps := Std.HashMap ValueId (List ValueId)

def dceStmtBody (st : Stmt) (s : DefOps × Array ValueId) : Id (ForInStep (DefOps × Array ValueId)) :=
  if removable st.inst = true then do
    let d ← forIn st.results s.1 fun r d => pure (ForInStep.yield (d.insert r (operands st.inst)))
    pure (ForInStep.yield (d, s.2))
  else pure (ForInStep.yield (s.1, s.2 ++ (operands st.inst).toArray))

def dceBlockBody (b : Block) (s : DefOps × Array ValueId) : Id (ForInStep (DefOps × Array ValueId)) := do
  let s' ← forIn b.body (s.1, s.2) dceStmtBody
  pure (ForInStep.yield (s'.1, s'.2 ++ (termOperands b.term).toArray))

def liveInner (defOps : DefOps) (v : ValueId) (s : Std.HashSet ValueId × Array ValueId) :
    Id (ForInStep (Std.HashSet ValueId × Array ValueId)) :=
  if s.1.contains v = true then pure (ForInStep.yield (s.1, s.2))
  else pure (ForInStep.yield (s.1.insert v, s.2 ++ ((defOps.get? v).getD []).toArray))

def liveBody (defOps : DefOps) (_x : Nat) (s : Array ValueId × Std.HashSet ValueId) :
    Id (ForInStep (Array ValueId × Std.HashSet ValueId)) :=
  if s.1.isEmpty = true then pure (ForInStep.done (s.1, s.2))
  else do
    let s' ← forIn s.1 (s.2, #[]) (liveInner defOps)
    pure (ForInStep.yield (s'.2, s'.1))

/-- The definitions of removable statements and the roots of the mark phase. -/
def dceScan (g : Function) : DefOps × Array ValueId :=
  (forIn g.blocks ((∅ : DefOps), (#[] : Array ValueId)) dceBlockBody).run

/-- The live set. -/
def dceLive (g : Function) : Std.HashSet ValueId :=
  (forIn [:(dceScan g).1.size + (dceScan g).2.size + 1] ((dceScan g).2, (∅ : Std.HashSet ValueId))
    (liveBody (dceScan g).1)).run.2

/-- DCE's choice. -/
def dceKeep (live : Std.HashSet ValueId) (st : Stmt) : Bool :=
  !removable st.inst || st.results.any live.contains

theorem dce_eq_raw (g : Function) : (dce g).1 = { g with blocks := (Id.run (forIn g.blocks
    ((0 : Nat), (#[] : Array Block)) fun b s =>
      pure (ForInStep.yield (s.1 + (b.body.length - (b.body.filter (dceKeep (dceLive g))).length),
        s.2.push { b with body := b.body.filter (dceKeep (dceLive g)) })))).2.toList } := rfl

theorem foldl_push_toList {α β γ : Type} (l : List α) (F : α → β) (G : γ → α → γ) (n : γ)
    (acc : Array β) :
    (l.foldl (fun s b => (G s.1 b, s.2.push (F b))) (n, acc)).2.toList = acc.toList ++ l.map F := by
  induction l generalizing n acc with
  | nil => simp
  | cons a l ih => simp [ih]

/-- **What DCE does**: it filters every body with `dceKeep (dceLive g)`. -/
theorem dce_eq (g : Function) :
    (dce g).1 = { g with blocks := g.blocks.map fun b =>
      { b with body := b.body.filter (dceKeep (dceLive g)) } } := by
  rw [dce_eq_raw]
  simp only [List.forIn_pure_yield_eq_foldl, Id.run_pure]
  congr 1
  have := foldl_push_toList g.blocks
    (fun b => { b with body := b.body.filter (dceKeep (dceLive g)) })
    (fun n b => n + (b.body.length - (b.body.filter (dceKeep (dceLive g))).length)) 0 #[]
  simpa using this

/-! ## The scan: definitions of removable statements and roots -/

def stmtScan (s : DefOps × Array ValueId) (st : Stmt) : DefOps × Array ValueId :=
  if removable st.inst = true then (st.results.foldl (fun d r => d.insert r (operands st.inst)) s.1, s.2)
  else (s.1, s.2 ++ (operands st.inst).toArray)

def blockScan (s : DefOps × Array ValueId) (b : Block) : DefOps × Array ValueId :=
  ((b.body.foldl stmtScan s).1, (b.body.foldl stmtScan s).2 ++ (termOperands b.term).toArray)

theorem dceStmtBody_eq : dceStmtBody = fun st s => pure (ForInStep.yield (stmtScan s st)) := by
  funext st s
  unfold dceStmtBody stmtScan
  split <;> simp [List.forIn_pure_yield_eq_foldl]

theorem dceBlockBody_eq : dceBlockBody = fun b s => pure (ForInStep.yield (blockScan s b)) := by
  funext b s
  simp [dceBlockBody, dceStmtBody_eq, List.forIn_pure_yield_eq_foldl, blockScan]

theorem dceScan_eq (g : Function) : dceScan g = g.blocks.foldl blockScan (∅, #[]) := by
  simp [dceScan, dceBlockBody_eq, List.forIn_pure_yield_eq_foldl]

/-- The roots: operands of non-removable statements and of terminators. -/
def rootsOf (b : Block) : List ValueId :=
  b.body.flatMap (fun st => if removable st.inst = true then [] else operands st.inst) ++
    termOperands b.term

/-- The recorded operand lists of removable definitions. -/
def opsOf (b : Block) : List (ValueId × List ValueId) :=
  b.body.flatMap fun st => if removable st.inst = true then st.results.map (·, operands st.inst) else []

theorem stmtScan_foldl (body : List Stmt) (s : DefOps × Array ValueId) :
    (body.foldl stmtScan s).2.toList =
      s.2.toList ++ body.flatMap (fun st => if removable st.inst = true then [] else operands st.inst) ∧
    (body.foldl stmtScan s).1 =
      (body.flatMap fun st => if removable st.inst = true then st.results.map (·, operands st.inst)
        else []).foldl (fun d x => d.insert x.1 x.2) s.1 := by
  induction body generalizing s with
  | nil => simp
  | cons st body ih =>
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (stmtScan s st)
    refine ⟨?_, ?_⟩
    · rw [h1]; unfold stmtScan; split <;> simp_all
    · rw [h2]; unfold stmtScan
      split
      · simp only [List.flatMap_cons, ite_true, *, List.foldl_append, List.foldl_map]
      · simp_all

theorem dceScan_spec (g : Function) :
    (dceScan g).2.toList = g.blocks.flatMap rootsOf ∧
      (dceScan g).1 = (g.blocks.flatMap opsOf).foldl (fun d x => d.insert x.1 x.2) ∅ := by
  rw [dceScan_eq]
  suffices ∀ (bs : List Block) (s : DefOps × Array ValueId),
      (bs.foldl blockScan s).2.toList = s.2.toList ++ bs.flatMap rootsOf ∧
        (bs.foldl blockScan s).1 = (bs.flatMap opsOf).foldl (fun d x => d.insert x.1 x.2) s.1 by
    simpa using this g.blocks (∅, #[])
  intro bs
  induction bs with
  | nil => simp
  | cons b bs ih =>
    intro s
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (blockScan s b)
    obtain ⟨h3, h4⟩ := stmtScan_foldl b.body s
    refine ⟨?_, ?_⟩
    · rw [h1]; simp [blockScan, h3, rootsOf]
    · rw [h2]; simp [blockScan, h4, opsOf, List.foldl_append]

/-! ## The mark phase -/

def innerStep (d : DefOps) (s : Std.HashSet ValueId × Array ValueId) (v : ValueId) :
    Std.HashSet ValueId × Array ValueId :=
  if s.1.contains v = true then s else (s.1.insert v, s.2 ++ ((d.get? v).getD []).toArray)

theorem liveInner_eq (d : DefOps) :
    liveInner d = fun v s => pure (ForInStep.yield (innerStep d s v)) := by
  funext v s; unfold liveInner innerStep; split <;> rfl

theorem innerStep_foldl (d : DefOps) (ws : List ValueId) :
    ∀ (s : Std.HashSet ValueId × Array ValueId),
      (∀ x, (ws.foldl (innerStep d) s).1.contains x = true ↔ s.1.contains x = true ∨ x ∈ ws) ∧
      (∀ v ∈ ws, s.1.contains v = false → ∀ x ∈ (d[v]?).getD [], x ∈ (ws.foldl (innerStep d) s).2.toList) ∧
      (∀ x ∈ (ws.foldl (innerStep d) s).2.toList, x ∈ s.2.toList ∨
        ∃ v ∈ ws, s.1.contains v = false ∧ x ∈ (d[v]?).getD []) ∧
      (∀ x ∈ s.2.toList, x ∈ (ws.foldl (innerStep d) s).2.toList) := by
  induction ws with
  | nil => intro s; simp
  | cons v ws ih =>
    intro s
    rw [List.foldl_cons]
    by_cases hv : s.1.contains v = true
    · have hs : innerStep d s v = s := by simp [innerStep, hv]
      rw [hs]
      obtain ⟨h1, h2, h3, h4⟩ := ih s
      refine ⟨fun x => ?_, fun u hu hl => ?_, fun x hx => ?_, h4⟩
      · rw [h1]; constructor
        · rintro (h | h); exact .inl h; exact .inr (List.mem_cons_of_mem _ h)
        · rintro (h | h)
          · exact .inl h
          · simp only [List.mem_cons] at h
            rcases h with rfl | h; exact .inl hv; exact .inr h
      · simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · rw [hv] at hl; cases hl
        · exact h2 u hu hl
      · rcases h3 x hx with h | ⟨u, hu, hl, hx⟩
        · exact .inl h
        · exact .inr ⟨u, List.mem_cons_of_mem _ hu, hl, hx⟩
    · have hvf : s.1.contains v = false := by simpa using hv
      have hs : innerStep d s v = (s.1.insert v, s.2 ++ ((d[v]?).getD []).toArray) := by
        simp [innerStep, hvf, Std.HashMap.get?_eq_getElem?]
      rw [hs]
      obtain ⟨h1, h2, h3, h4⟩ := ih (s.1.insert v, s.2 ++ ((d[v]?).getD []).toArray)
      simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at h1 h2 h3
      refine ⟨fun x => ?_, fun u hu hl => ?_, fun x hx => ?_, fun x hx => h4 x (by simp [hx])⟩
      · rw [h1]; simp only [List.mem_cons]
        constructor
        · rintro ((h | h) | h)
          · exact .inr (.inl h.symm)
          · exact .inl h
          · exact .inr (.inr h)
        · rintro (h | h | h)
          · exact .inl (.inr h)
          · exact .inl (.inl h.symm)
          · exact .inr h
      · simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · intro x hx; exact h4 x (by simp [hx])
        · by_cases huv : u = v
          · subst huv; intro x hx; exact h4 x (by simp [hx])
          · exact h2 u hu (by
              simp only [Std.HashSet.contains_insert, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
              exact ⟨Ne.symm huv, hl⟩)
      · rcases h3 x hx with h | ⟨u, hu, hl, hx⟩
        · simp only [Array.toList_append, List.mem_append] at h
          rcases h with h | h
          · exact .inl h
          · exact .inr ⟨v, List.mem_cons_self .., hvf, by simpa using h⟩
        · simp only [Std.HashSet.contains_insert, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hl
          exact .inr ⟨u, List.mem_cons_of_mem _ hu, hl.2, hx⟩

def liveInv (d : DefOps) (w0 : List ValueId) (s : Array ValueId × Std.HashSet ValueId) : Prop :=
  (∀ x ∈ w0, s.2.contains x = true ∨ x ∈ s.1.toList) ∧
    ∀ v, s.2.contains v = true → ∀ x ∈ (d[v]?).getD [], s.2.contains x = true ∨ x ∈ s.1.toList

def livePot (d : DefOps) (s : Array ValueId × Std.HashSet ValueId) : Nat :=
  if s.1.isEmpty then 0 else 1 + (d.keys.filter fun k => !s.2.contains k).length

theorem filter_length_lt {α : Type} {l : List α} {p q : α → Bool}
    (hpq : ∀ k ∈ l, q k = true → p k = true) {k : α} (hk : k ∈ l) (hp : p k = true)
    (hq : q k = false) : (l.filter q).length < (l.filter p).length := by
  induction l with
  | nil => simp at hk
  | cons a l ih =>
    have hle : ∀ (l : List α), (∀ k ∈ l, q k = true → p k = true) →
        (l.filter q).length ≤ (l.filter p).length := by
      intro l h
      induction l with
      | nil => simp
      | cons b l ih' =>
        simp only [List.filter_cons]
        have := ih' fun k hk => h k (List.mem_cons_of_mem _ hk)
        by_cases hqb : q b = true
        · simp [hqb, h b (List.mem_cons_self ..)]; omega
        · simp only [hqb, Bool.false_eq_true, ite_false]
          split <;> simp <;> omega
    simp only [List.mem_cons] at hk
    simp only [List.filter_cons]
    rcases hk with rfl | hk
    · have := hle l fun k hk => hpq k (List.mem_cons_of_mem _ hk)
      simp [hp, hq]; omega
    · have := ih (fun k hk => hpq k (List.mem_cons_of_mem _ hk)) hk
      by_cases hqa : q a = true
      · simp [hqa, hpq a (List.mem_cons_self ..) hqa]; omega
      · simp only [hqa, Bool.false_eq_true, ite_false]
        split <;> simp <;> omega

/-- **The live set is closed**: it contains the roots and the operands of the removable
definitions of its values. -/
theorem dceLive_closed (g : Function) :
    (∀ x ∈ (dceScan g).2.toList, (dceLive g).contains x = true) ∧
      ∀ v, (dceLive g).contains v = true →
        ∀ x ∈ ((dceScan g).1[v]?).getD [], (dceLive g).contains x = true := by
  unfold dceLive
  generalize (dceScan g).1 = d
  generalize hw0 : (dceScan g).2 = w0
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have key := forIn_pot (List.range' [:d.size + w0.size + 1].start [:d.size + w0.size + 1].size
      [:d.size + w0.size + 1].step) (w0, ∅) (liveBody d) (liveInv d w0.toList)
    (fun s => liveInv d w0.toList s ∧ s.1.isEmpty = true) (livePot d) ?_ ?_ ?_
  · obtain ⟨⟨h1, h2⟩, he⟩ := key
    have he' : ∀ x, x ∉ ((forIn (List.range' [:d.size + w0.size + 1].start
        [:d.size + w0.size + 1].size [:d.size + w0.size + 1].step) (w0, ∅) (liveBody d)).run.1).toList := by
      intro x hx
      have := Array.isEmpty_iff.1 he
      rw [this] at hx; simp at hx
    exact ⟨fun x hx => (h1 x hx).resolve_right (he' x),
      fun v hv x hx => (h2 v hv x hx).resolve_right (he' x)⟩
  · exact ⟨fun x hx => .inr hx, fun v hv => by simp at hv⟩
  · simp only [livePot, Std.Legacy.Range.size, List.length_range']
    split
    · omega
    · rename_i hne
      have : 0 < w0.size := by
        rcases Nat.eq_zero_or_pos w0.size with h | h
        · exact absurd (Array.isEmpty_iff_size_eq_zero.2 h) hne
        · exact h
      have := List.length_filter_le (fun k => !(∅ : Std.HashSet ValueId).contains k) d.keys
      rw [Std.HashMap.length_keys] at this
      omega
  · rintro _ ⟨work, live⟩ ⟨ha, hb⟩
    unfold liveBody
    simp only
    by_cases he : work.isEmpty = true
    · simp only [he, ite_true]
      exact ⟨⟨ha, hb⟩, he⟩
    · have hne := he
      simp only [he, Bool.false_eq_true, ite_false]
      rw [← Array.forIn_toList, liveInner_eq, List.forIn_pure_yield_eq_foldl]
      simp only [bind_pure_comp, Id.run_map, Id.run_pure]
      obtain ⟨i1, i2, i3, i4⟩ := innerStep_foldl d work.toList (live, #[])
      generalize work.toList.foldl (innerStep d) (live, #[]) = r at i1 i2 i3 i4
      obtain ⟨l', n'⟩ := r
      simp only at i1 i2 i3 i4 ⊢
      refine ⟨⟨fun x hx => ?_, fun v hv x hx => ?_⟩, ?_⟩
      · rcases ha x hx with h | h
        · exact .inl ((i1 x).2 (.inl h))
        · exact .inl ((i1 x).2 (.inr h))
      · by_cases hl : live.contains v = true
        · rcases hb v hl x hx with h | h
          · exact .inl ((i1 x).2 (.inl h))
          · exact .inl ((i1 x).2 (.inr h))
        · have hvw : v ∈ work.toList := ((i1 v).1 hv).resolve_left hl
          exact .inr (i2 v hvw (by simpa using hl) x hx)
      · simp only [livePot, hne, Bool.false_eq_true, ite_false]
        split
        · omega
        · rename_i hne'
          obtain ⟨x, hx⟩ : ∃ x, x ∈ n'.toList := by
            cases hn : n'.toList with
            | nil => exact absurd (by simp [Array.isEmpty_iff, ← Array.toList_eq_nil_iff, hn]) hne'
            | cons x _ => exact ⟨x, by simp⟩
          rcases i3 x hx with h | ⟨v, hv, hl, hxv⟩
          · simp at h
          · have hk : v ∈ d.keys := by
              rw [Std.HashMap.mem_keys]
              cases hd : d[v]? with
              | none => rw [hd] at hxv; simp at hxv
              | some _ => exact Std.HashMap.mem_iff_isSome_getElem?.2 (by simp [hd])
            have := filter_length_lt (l := d.keys) (p := fun k => !live.contains k)
              (q := fun k => !l'.contains k)
              (fun k _ hq => by
                simp only [Bool.not_eq_true'] at hq ⊢
                cases hk' : live.contains k
                · rfl
                · have := (i1 k).2 (.inl hk'); rw [this] at hq; cases hq) hk
              (by simp [hl]) (by simp [(i1 v).2 (.inr hv)])
            omega

/-! ## List facts for filtered bodies -/

/-- The position in `l.filter p` of the element at position `k` of `l`. -/
def fidx {α : Type} (p : α → Bool) (l : List α) (k : Nat) : Nat := ((l.take k).filter p).length

theorem getElem?_filter_fidx {α : Type} (p : α → Bool) :
    ∀ (l : List α) (k : Nat) (a : α), l[k]? = some a → p a = true →
      (l.filter p)[fidx p l k]? = some a
  | [], k, a, h, _ => by simp at h
  | b :: l, 0, a, h, hp => by
    simp at h; subst h; simp [fidx, List.filter_cons, hp]
  | b :: l, k + 1, a, h, hp => by
    simp only [List.getElem?_cons_succ] at h
    have := getElem?_filter_fidx p l k a h hp
    simp only [fidx, List.take_succ_cons, List.filter_cons] at this ⊢
    split
    · simpa using this
    · simpa using this

theorem exists_fidx {α : Type} (p : α → Bool) :
    ∀ (l : List α) (k' : Nat) (a : α), (l.filter p)[k']? = some a →
      ∃ k, l[k]? = some a ∧ p a = true ∧ fidx p l k = k'
  | [], k', a, h => by simp at h
  | b :: l, k', a, h => by
    simp only [List.filter_cons] at h
    by_cases hb : p b = true
    · simp only [hb, ite_true] at h
      cases k' with
      | zero =>
        simp at h; subst h
        exact ⟨0, rfl, hb, by simp [fidx]⟩
      | succ k' =>
        simp only [List.getElem?_cons_succ] at h
        obtain ⟨k, hk, hp, hf⟩ := exists_fidx p l k' a h
        exact ⟨k + 1, by simpa using hk, hp, by simp [fidx, List.filter_cons, hb] at hf ⊢; omega⟩
    · simp only [hb, Bool.false_eq_true, ite_false] at h
      obtain ⟨k, hk, hp, hf⟩ := exists_fidx p l k' a h
      exact ⟨k + 1, by simpa using hk, hp, by simp [fidx, List.filter_cons, hb] at hf ⊢; omega⟩

theorem fidx_succ {α : Type} (p : α → Bool) (b : α) (l : List α) (k : Nat) :
    fidx p (b :: l) (k + 1) = (if p b = true then 1 else 0) + fidx p l k := by
  simp only [fidx, List.take_succ_cons, List.filter_cons]
  split <;> simp <;> omega

theorem fidx_lt {α : Type} (p : α → Bool) :
    ∀ (l : List α) {k j : Nat}, k < j → ∀ {a : α}, l[k]? = some a → p a = true →
      fidx p l k < fidx p l j
  | [], _, _, _, _, hk, _ => by simp at hk
  | b :: l, 0, j + 1, _, a, hk, hp => by
    simp at hk; subst hk
    rw [fidx_succ]; simp [fidx, hp]; omega
  | b :: l, k + 1, j + 1, hkj, a, hk, hp => by
    rw [fidx_succ, fidx_succ]
    have := fidx_lt p l (k := k) (j := j) (by omega) (by simpa using hk) hp
    omega
  | _ :: _, _ + 1, 0, hkj, _, _, _ => by omega
  | _ :: _, 0, 0, hkj, _, _, _ => by omega

theorem fidx_le_length {α : Type} (p : α → Bool) (l : List α) {k : Nat} {a : α} (hk : l[k]? = some a)
    (hp : p a = true) : fidx p l k < (l.filter p).length := by
  have := getElem?_filter_fidx p l k a hk hp
  exact (List.getElem?_eq_some_iff.1 this).1

/-- An `AllAlong` over a filtered list, for related states. -/
theorem allAlong_filter {α β : Type} {C C' : β → α → Prop} {g : β → α → β} {R : β → β → Prop}
    (p : α → Bool) :
    ∀ (l : List α) (s s' : β), R s s' → AllAlong C g l s →
      (∀ s s' a, a ∈ l → R s s' → p a = true → C s a → C' s' a) →
      (∀ s s' a, a ∈ l → R s s' → p a = true → R (g s a) (g s' a)) →
      (∀ s s' a, a ∈ l → R s s' → p a = false → R (g s a) s') →
      AllAlong C' g (l.filter p) s' ∧ R (l.foldl g s) ((l.filter p).foldl g s')
  | [], s, s', hR, _, _, _, _ => ⟨trivial, hR⟩
  | a :: l, s, s', hR, ⟨hC, hA⟩, hc, hk, hd => by
    have hc' := fun s s' b hb => hc s s' b (List.mem_cons_of_mem _ hb)
    have hk' := fun s s' b hb => hk s s' b (List.mem_cons_of_mem _ hb)
    have hd' := fun s s' b hb => hd s s' b (List.mem_cons_of_mem _ hb)
    simp only [List.filter_cons, List.foldl_cons]
    by_cases hp : p a = true
    · simp only [hp, ite_true, AllAlong, List.foldl_cons]
      have := allAlong_filter p l (g s a) (g s' a) (hk s s' a (List.mem_cons_self ..) hR hp) hA hc' hk' hd'
      exact ⟨⟨hc s s' a (List.mem_cons_self ..) hR hp hC, this.1⟩, this.2⟩
    · have hpf : p a = false := by simpa using hp
      simp only [hpf, Bool.false_eq_true, ite_false]
      exact allAlong_filter p l (g s a) s' (hd s s' a (List.mem_cons_self ..) hR hpf) hA hc' hk' hd'

/-! ## Liveness facts on functions whose values are defined once -/

theorem foldl_insert_notin' {β : Type} {l : List (ValueId × β)} {v : ValueId}
    (hv : v ∉ l.map (·.1)) : ∀ m : Std.HashMap ValueId β,
      (l.foldl (fun m (x : ValueId × β) => m.insert x.1 x.2) m)[v]? = m[v]? := by
  induction l with
  | nil => intro m; rfl
  | cons x l ih =>
    intro m
    simp only [List.map_cons, List.mem_cons, not_or] at hv
    rw [List.foldl_cons, ih hv.2]
    have : (x.1 == v) = false := by simpa using Ne.symm hv.1
    simp [Std.HashMap.getElem?_insert, this]

theorem foldl_insert_get_nodup {β : Type} :
    ∀ (l : List (ValueId × β)), (l.map (·.1)).Nodup → ∀ x ∈ l, ∀ m : Std.HashMap ValueId β,
      (l.foldl (fun m (x : ValueId × β) => m.insert x.1 x.2) m)[x.1]? = some x.2
  | [], _, x, hx, _ => by simp at hx
  | y :: l, hn, x, hx, m => by
    simp only [List.map_cons, List.nodup_cons] at hn
    rw [List.foldl_cons]
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · rw [foldl_insert_notin' hn.1]; simp
    · exact foldl_insert_get_nodup l hn.2 x hx _

theorem defSites_fst (g : Function) :
    (defSites g).map (·.1) = g.blocks.flatMap fun b => b.params.map (·.1) ++ b.body.flatMap (·.results) := by
  unfold defSites
  rw [List.map_flatMap]
  rw [flatMap_congr' (h := fun x : Block × Nat =>
    (fun b : Block => b.params.map (·.1) ++ b.body.flatMap (·.results)) x.1) ?_]
  · rw [← List.flatMap_map Prod.fst (fun b : Block => b.params.map (·.1) ++ b.body.flatMap (·.results)),
      List.zipIdx_map_fst]
  · rintro ⟨b, i⟩ _
    simp only [List.map_append, List.map_map]
    rw [sites_body_fst]
    rfl

theorem flatMap_sublist {α β : Type} {l : List α} {F G : α → List β} (h : ∀ a ∈ l, (F a).Sublist (G a)) :
    (l.flatMap F).Sublist (l.flatMap G) := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact (h a (List.mem_cons_self ..)).append (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem opsOf_keys_sublist (g : Function) :
    ((g.blocks.flatMap opsOf).map (·.1)).Sublist ((defSites g).map (·.1)) := by
  rw [defSites_fst, List.map_flatMap]
  apply flatMap_sublist
  intro b _
  simp only [opsOf, List.map_flatMap]
  refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
  apply flatMap_sublist
  intro st _
  split
  · rw [List.map_map, show ((fun x : ValueId × List ValueId => x.fst) ∘ fun x => (x, operands st.inst)) = id
      from rfl, List.map_id]
    exact List.Sublist.refl _
  · simp

/-- Values are defined once. -/
def UniqueDefs (g : Function) : Prop := ((defSites g).map (·.1)).Nodup

theorem dceScan_ops {g : Function} (hu : UniqueDefs g) {b : Block} (hb : b ∈ g.blocks) {st : Stmt}
    (hst : st ∈ b.body) (hr : removable st.inst = true) {r : ValueId} (hrr : r ∈ st.results) :
    (dceScan g).1[r]? = some (operands st.inst) := by
  rw [(dceScan_spec g).2]
  exact foldl_insert_get_nodup _ ((opsOf_keys_sublist g).nodup hu) (r, operands st.inst)
    (List.mem_flatMap.2 ⟨b, hb, List.mem_flatMap.2 ⟨st, hst, by simp [hr, hrr]⟩⟩) ∅

theorem dce_term_live (g : Function) {b : Block} (hb : b ∈ g.blocks) {v : ValueId}
    (hv : v ∈ termOperands b.term) : (dceLive g).contains v = true := by
  apply (dceLive_closed g).1
  rw [(dceScan_spec g).1]
  exact List.mem_flatMap.2 ⟨b, hb, by simp [rootsOf, hv]⟩

/-- The operands of a kept statement are live. -/
theorem dce_ops_live {g : Function} (hu : UniqueDefs g) {b : Block} (hb : b ∈ g.blocks) {st : Stmt}
    (hst : st ∈ b.body) (hk : dceKeep (dceLive g) st = true) {v : ValueId}
    (hv : v ∈ operands st.inst) : (dceLive g).contains v = true := by
  by_cases hr : removable st.inst = true
  · simp only [dceKeep, hr, Bool.not_true, Bool.false_or, List.any_eq_true] at hk
    obtain ⟨r, hrr, hl⟩ := hk
    exact (dceLive_closed g).2 r hl v (by rw [dceScan_ops hu hb hst hr hrr]; exact hv)
  · apply (dceLive_closed g).1
    rw [(dceScan_spec g).1]
    exact List.mem_flatMap.2 ⟨b, hb, by simp [rootsOf, hr]; exact .inl ⟨st, hst, by simpa using hr, hv⟩⟩

/-! ## Facts from `check` -/

theorem seenStep_contains (s : Std.HashSet ValueId) (st : Stmt) (v : ValueId) :
    (seenStep s st).contains v = true ↔ s.contains v = true ∨ v ∈ st.results := by
  unfold seenStep
  generalize st.results = rs
  induction rs generalizing s with
  | nil => simp
  | cons r rs ih =>
    rw [List.foldl_cons, ih]
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact .inr (.inl h.symm)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h.symm)
      · exact .inr h

/-- What `check g = .ok info` provides. -/
structure Checked (g : Function) (info : Info) : Prop where
  core : CoreOk g
  info_eq : info = coreInfo g
  wf : Wf g (wfData g info)
  arity : Arity g
  nodup : ((defList g).map (·.1)).Nodup
  unique : UniqueDefs g

theorem checked_of_check {g : Function} {info : Info} (h : check g = .ok info) : Checked g info := by
  obtain ⟨hc, hi, _⟩ := (check_ok_iff g info).1 h
  have hd := (defsOk_iff g).1 hc.2.2.2.1
  have hn := ((allAlong_evC_iff _ _).1 hd.2).2
  exact ⟨hc, hi, wf_of_check h, hd.1, hn, by unfold UniqueDefs; rw [defSites_map_fst hd.1]; exact hn⟩

theorem Checked.defined {g : Function} {info : Info} (hc : Checked g info) {v : ValueId} {s : Nat × Nat}
    (h : (wfData g info).dm v = some s) : v ∈ (defList g).map (·.1) := by
  have := hc.wf.sitesRev v s h
  rw [← defSites_map_fst hc.arity]
  exact List.mem_map_of_mem (f := (·.1)) this

theorem Checked.op_defined {g : Function} {info : Info} (hc : Checked g info) {i : Nat} {b : Block}
    (hb : g.blocks[i]? = some b) {st : Stmt} (hst : st ∈ b.body) {v : ValueId}
    (hv : v ∈ operands st.inst) : v ∈ (defList g).map (·.1) := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hst
  obtain ⟨d, t, hd, -⟩ := hc.wf.uses i b hb j st hj v hv
  exact hc.defined hd

theorem Checked.term_defined {g : Function} {info : Info} (hc : Checked g info) {i : Nat} {b : Block}
    (hb : g.blocks[i]? = some b) {v : ValueId} (hv : v ∈ termOperands b.term) :
    v ∈ (defList g).map (·.1) := by
  obtain ⟨d, t, hd, -⟩ := hc.wf.termUses i b hb v hv
  exact hc.defined hd

theorem Sublist.flatMap' {α β : Type} {l1 l2 : List α} (h : l1.Sublist l2) (F : α → List β) :
    (l1.flatMap F).Sublist (l2.flatMap F) := by
  induction h with
  | slnil => exact List.Sublist.slnil
  | cons a _ ih => simp only [List.flatMap_cons]; exact ih.trans (List.sublist_append_right _ _)
  | cons_cons a _ ih => simp only [List.flatMap_cons]; exact ih.append_left _

/-! ## The output of DCE -/

/-- A block with its body filtered. -/
def fltB (live : Std.HashSet ValueId) (b : Block) : Block :=
  { b with body := b.body.filter (dceKeep live) }

section DceOut

variable (g : Function)

theorem dce_blocks : (dce g).1.blocks = g.blocks.map (fltB (dceLive g)) := by
  rw [dce_eq]; rfl

theorem dce_get (i : Nat) : (dce g).1.blocks[i]? = (g.blocks[i]?).map (fltB (dceLive g)) := by
  rw [dce_blocks, List.getElem?_map]

theorem dce_build : Cfg.build (dce g).1 = Cfg.build g := by
  apply build_congr
  simp only [cfgShape, dce_blocks, List.map_map]
  rfl

theorem dce_stmtEvs (i : Nat) (st : Stmt) : stmtEvs (dce g).1 i st = stmtEvs g i st := by
  rw [dce_eq]; rfl

theorem dce_arity (h : Arity g) : Arity (dce g).1 := by
  intro b hb st hst
  rw [dce_blocks, List.mem_map] at hb
  obtain ⟨b0, hb0, rfl⟩ := hb
  have := h b0 hb0 st ((List.mem_filter.1 hst).1)
  simpa [stmtTys, dce_eq] using this

theorem dce_defList_sublist : (defList (dce g).1).Sublist (defList g) := by
  unfold defList
  rw [dce_blocks, List.zipIdx_map, List.flatMap_map]
  apply flatMap_sublist
  rintro ⟨b, i⟩ _
  simp only [Prod.map, id, blockEvs, fltB, dce_stmtEvs]
  exact (Sublist.flatMap' (List.filter_sublist) _).append_left _

theorem dce_mem_defList {e : DefEv} :
    e ∈ defList (dce g).1 ↔ ∃ i b, g.blocks[i]? = some b ∧
      ((∃ p ∈ b.params, e = (p.1, p.2, i)) ∨
        ∃ st ∈ b.body, dceKeep (dceLive g) st = true ∧ e ∈ stmtEvs g i st) := by
  rw [mem_defList]
  simp only [dce_get, Option.map_eq_some_iff, dce_stmtEvs]
  constructor
  · rintro ⟨i, b', ⟨b, hb, rfl⟩, h⟩
    refine ⟨i, b, hb, ?_⟩
    rcases h with h | ⟨st, hst, he⟩
    · exact .inl h
    · exact .inr ⟨st, (List.mem_filter.1 hst).1, (List.mem_filter.1 hst).2, he⟩
  · rintro ⟨i, b, hb, h⟩
    refine ⟨i, fltB (dceLive g) b, ⟨b, hb, rfl⟩, ?_⟩
    rcases h with h | ⟨st, hst, hk, he⟩
    · exact .inl h
    · exact .inr ⟨st, List.mem_filter.2 ⟨hst, hk⟩, he⟩

theorem stmtEvs_fst_mem {f : Function} {i : Nat} {st : Stmt} {e : DefEv} (h : e ∈ stmtEvs f i st) :
    e.1 ∈ st.results := by
  unfold stmtEvs at h
  split at h
  · obtain ⟨⟨r, t⟩, hz, rfl⟩ := List.mem_map.1 h
    exact List.of_mem_zip hz |>.1
  · simp at h

/-- A definition with a live value survives. -/
theorem dce_def_live {e : DefEv} (he : e ∈ defList g) (hl : (dceLive g).contains e.1 = true) :
    e ∈ defList (dce g).1 := by
  rw [dce_mem_defList]
  obtain ⟨i, b, hb, h⟩ := mem_defList.1 he
  refine ⟨i, b, hb, ?_⟩
  rcases h with h | ⟨st, hst, hes⟩
  · exact .inl h
  · refine .inr ⟨st, hst, ?_, hes⟩
    simp only [dceKeep, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true]
    exact .inr ⟨e.1, stmtEvs_fst_mem hes, hl⟩

end DceOut

/-! ## `check` accepts the output -/

theorem termCalls_args {t : Terminator} {bc : BlockCall} (h : bc ∈ termCalls t) {a : ValueId}
    (ha : a ∈ bc.args) : a ∈ termOperands t := by
  cases t <;> simp_all [termCalls, termOperands]
  all_goals first
    | (rcases h with rfl | rfl <;> simp [ha])
    | (rcases h with rfl | h; · simp [ha]
       · exact .inr (.inr ⟨bc, h, ha⟩))

theorem brTable_operand {t : Terminator} {x : ValueId} {d : BlockCall} {tb : List BlockCall}
    (h : t = .brTable x d tb) : x ∈ termOperands t := by
  subst h; simp [termOperands]

theorem getElem!_map_params (l : List Block) (F : Block → Block) (hF : ∀ b, (F b).params = b.params)
    (j : Nat) : ((l.map F).toArray[j]!).params = (l.toArray[j]!).params := by
  simp only [getElem!_def, List.getElem?_toArray, List.getElem?_map]
  cases l[j]? <;> simp [hF]

section DceCheck

variable {g : Function} {info : Info} (hc : Checked g info)
include hc

/-- Lookups in the output's maps agree with the input's on live defined values. -/
theorem dce_lookup {v : ValueId} (hl : (dceLive g).contains v = true)
    (hd : v ∈ (defList g).map (·.1)) :
    (defsState (dce g).1).1[v]? = (defsState g).1[v]? ∧
      (defsState (dce g).1).2.1[v]? = (defsState g).2.1[v]? := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
  have he' := dce_def_live g he hl
  have hn' := (dce_defList_sublist g |>.map (·.1)).nodup hc.nodup
  have h1 := (defsState_get _ hn').1 e he'
  have h2 := (defsState_get _ hc.nodup).1 e he
  rw [h1.1, h1.2, h2.1, h2.2]; exact ⟨rfl, rfl⟩

theorem dce_availCk {i : Nat} {s s' : Std.HashSet ValueId}
    (hR : ∀ v, s.contains v = true → (dceLive g).contains v = true → s'.contains v = true)
    {v : ValueId} (hl : (dceLive g).contains v = true) (hd : v ∈ (defList g).map (·.1))
    (h : availCk g (defsState g).2.1 i s v = true) :
    availCk (dce g).1 (defsState (dce g).1).2.1 i s' v = true := by
  unfold availCk at h ⊢
  rw [dce_build, Std.HashMap.get?_eq_getElem?, (dce_lookup hc hl hd).2]
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact .inl (hR v h hl)
  · exact .inr (by simpa [Std.HashMap.get?_eq_getElem?] using h)

/-- **`checkCore` accepts DCE's output.** -/
theorem dce_coreOk : CoreOk (dce g).1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc.core
  have hn' := (dce_defList_sublist g |>.map (·.1)).nodup hc.nodup
  refine ⟨by rw [dce_build]; exact h1, by rw [dce_build]; exact h2,
    by rw [dce_build]; exact h3, ?_, ?_, ?_⟩
  · rw [defsOk_iff]
    exact ⟨dce_arity g hc.arity, (allAlong_evC_iff _ _).2 ⟨fun e _ => by simp, hn'⟩⟩
  · rw [dce_blocks, getElem!_map_params g.blocks (fltB (dceLive g)) (fun _ => rfl)]; exact h5
  · intro x hx
    rw [dce_blocks, List.zipIdx_map, List.mem_map] at hx
    obtain ⟨⟨b, i⟩, hbi, rfl⟩ := hx
    have hb : g.blocks[i]? = some b := List.mem_zipIdx_iff_getElem?.1 hbi
    have hbm : b ∈ g.blocks := List.mem_of_getElem? hb
    obtain ⟨hA, hterm, hcalls, hbr⟩ := h6 (b, i) hbi
    simp only [Prod.map, id] at hA hterm hcalls hbr ⊢
    let R : Std.HashSet ValueId → Std.HashSet ValueId → Prop := fun s s' =>
      ∀ v, s.contains v = true → (dceLive g).contains v = true → s'.contains v = true
    have hF := allAlong_filter (C := stmtUseC g (defsState g).1 (defsState g).2.1 i)
      (C' := stmtUseC (dce g).1 (defsState (dce g).1).1 (defsState (dce g).1).2.1 i)
      (g := seenStep) (R := R) (dceKeep (dceLive g)) b.body (paramSeen b) (paramSeen b)
      (fun v h _ => h) hA ?_ ?_ ?_
    · refine ⟨hF.1, fun v hv => ?_, fun bc hbc => ?_, ?_⟩
      · exact dce_availCk hc hF.2 (dce_term_live g hbm hv) (hc.term_defined hb hv) (hterm v hv)
      · obtain ⟨j, hj, hok⟩ := hcalls bc hbc
        refine ⟨j, by rw [dce_build]; exact hj, ?_⟩
        rw [dce_blocks, getElem!_map_params g.blocks (fltB (dceLive g)) (fun _ => rfl)]
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok ⊢
        refine ⟨hok.1, fun x hx => ?_⟩
        have ha : x.2 ∈ bc.args := (List.of_mem_zip hx).2
        have hta := termCalls_args hbc ha
        rw [Std.HashMap.get?_eq_getElem?, (dce_lookup hc (dce_term_live g hbm hta)
          (hc.term_defined hb hta)).1]
        simpa [Std.HashMap.get?_eq_getElem?] using hok.2 x hx
      · have key : ∀ x d tb, b.term = .brTable x d tb → (defsState g).1[x]? = some .i32 →
            (defsState (dce g).1).1[x]? = some .i32 := by
          intro x d tb ht h
          have hx : x ∈ termOperands b.term := brTable_operand ht
          rw [(dce_lookup hc (dce_term_live g hbm hx) (hc.term_defined hb hx)).1]; exact h
        revert hbr
        simp only [fltB]
        cases ht : b.term <;> simp only [brTableOk, imp_self]
        exact key _ _ _ ht
    · intro s s' st hst hR hk hC
      refine ⟨fun v hv => ?_, fun hp => ?_⟩
      · exact dce_availCk hc hR (dce_ops_live hc.unique hbm hst hk hv) (hc.op_defined hb hst hv)
          (hC.1 v hv)
      · rw [← hC.2 hp]
        apply pureTyped_congr _ (by rw [dce_eq]) (by rw [dce_eq])
        intro x hx
        simp only [Std.HashMap.get?_eq_getElem?]
        exact (dce_lookup hc (dce_ops_live hc.unique hbm hst hk hx) (hc.op_defined hb hst hx)).1
    · intro s s' st _ hR _ v hv hl
      rw [seenStep_contains] at hv ⊢
      rcases hv with hv | hv
      · exact .inl (hR v hv hl)
      · exact .inr hv
    · intro s s' st _ hR hk v hv hl
      rw [seenStep_contains] at hv
      rcases hv with hv | hv
      · exact hR v hv hl
      · simp only [dceKeep, Bool.or_eq_false_iff, Bool.not_eq_false', List.any_eq_false] at hk
        exact absurd hl (by simpa using hk.2 v hv)

end DceCheck

end Opt

namespace Opt

open Clif

/-! ## Generic facts on checked functions -/

theorem ancB_refl (idom : Array (Option Nat)) : ∀ fuel a, ancB idom fuel a a = true := by
  intro fuel a; cases fuel <;> simp [ancB]

/-- A definition site is unique on a function whose values are defined once. -/
theorem site_unique {g : Function} (hu : UniqueDefs g) {v : ValueId} {s1 s2 : Nat × Nat}
    (h1 : (v, s1) ∈ defSites g) (h2 : (v, s2) ∈ defSites g) : s1 = s2 := by
  have e1 := (defMap_get_iff hu v s1).2 h1
  have e2 := (defMap_get_iff hu v s2).2 h2
  rw [e1] at e2; cases e2; rfl

/-- `checkCore`'s type of a defined value. -/
theorem tm_of_defList {f : Function} (hn : ((defList f).map (·.1)).Nodup) {e : DefEv}
    (he : e ∈ defList f) : (wfData f (coreInfo f)).tm e.1 = some e.2.1 := by
  simp only [wfData, coreInfo, Std.HashMap.get?_eq_getElem?]
  exact ((defsState_get f hn).1 e he).1

/-- `checkCore`'s types of the results of a statement. -/
theorem tm_result {f : Function} (hn : ((defList f).map (·.1)).Nodup) {i : Nat} {b : Block}
    (hb : f.blocks[i]? = some b) {st : Stmt} (hst : st ∈ b.body) {ts : List Ty}
    (hts : st.inst.resultTypes (sigOf f) (fun _ => none) = some ts)
    (hlen : ts.length = st.results.length) {n : Nat} {r : ValueId} (hr : st.results[n]? = some r) :
    (wfData f (coreInfo f)).tm r = ts[n]? := by
  have hn' : n < ts.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hr).1
  have he : (r, ts[n], i) ∈ defList f := by
    rw [mem_defList]
    refine ⟨i, b, hb, .inr ⟨st, hst, ?_⟩⟩
    unfold stmtEvs stmtTys
    rw [show st.inst.resultTypes (fun r => (f.externs.lookup r).map (·.sig)) (fun _ => none) = some ts
      from hts]
    exact List.mem_map.2 ⟨(r, ts[n]),
      List.mem_iff_getElem?.2 ⟨n, by simp [List.getElem?_zip_eq_some, hr]⟩, rfl⟩
  rw [tm_of_defList hn he, List.getElem?_eq_getElem hn']

theorem tm_param {f : Function} (hn : ((defList f).map (·.1)).Nodup) {i : Nat} {b : Block}
    (hb : f.blocks[i]? = some b) {p : ValueId × Ty} (hp : p ∈ b.params) :
    (wfData f (coreInfo f)).tm p.1 = some p.2 :=
  tm_of_defList hn (e := (p.1, p.2, i)) (mem_defList.2 ⟨i, b, hb, .inl ⟨p, hp, rfl⟩⟩)

theorem fidx_length {α : Type} (p : α → Bool) (l : List α) : fidx p l l.length = (l.filter p).length := by
  simp [fidx]

theorem renStmt_id (s : Stmt) : renStmt id s = s := by
  cases s; simp [renStmt, mapOperands_id]

/-- Alignment of a body with a filtered copy (`σ = id`): kept statements match, the others must be
deletable. -/
theorem align_filter (c : EditCtx) (hσ : c.σ = id) (p : Stmt → Bool) :
    ∀ (l : List Stmt), (∀ s ∈ l, p s = false → ∀ k, c.delOk s k = true) →
      ∀ k, c.align l (l.filter p) k = true
  | [], _, k => by simp [EditCtx.align]
  | s :: l, hd, k => by
    have ih := align_filter c hσ p l (fun s' hs' => hd s' (List.mem_cons_of_mem _ hs'))
    have hkeep : ∀ t, c.keepOk s t = true ↔ t = s := by
      intro t; simp [EditCtx.keepOk, hσ, renStmt_id]
    by_cases hp : p s = true
    · simp only [List.filter_cons, hp, ite_true]
      rw [EditCtx.align]
      simp only [(hkeep s).2 rfl, ite_true]
      exact ih _
    · have hpf : p s = false := by simpa using hp
      simp only [List.filter_cons, hpf, Bool.false_eq_true, ite_false]
      have hdel := hd s (List.mem_cons_self ..) hpf k
      cases hf : l.filter p with
      | nil => rw [EditCtx.align, hdel, Bool.true_and, ← hf]; exact ih k
      | cons t ts =>
        have ht : p t = true := (List.mem_filter.1 (hf ▸ List.mem_cons_self ..)).2
        have hne : c.keepOk s t = false := by
          cases hk : c.keepOk s t
          · rfl
          · rw [(hkeep t).1 hk, hpf] at ht; cases ht
        rw [EditCtx.align]
        simp only [hne, Bool.false_eq_true, ite_false, hdel, ite_true]
        rw [← hf]
        exact ih k

/-! ## DCE: definition sites of the output -/

theorem dce_mem_defSites {g : Function} {v : ValueId} {s : Nat × Nat} :
    (v, s) ∈ defSites (dce g).1 ↔ ∃ i b, g.blocks[i]? = some b ∧
      ((∃ p ∈ b.params, p.1 = v ∧ s = (i, 0)) ∨
        ∃ j st, b.body[j]? = some st ∧ dceKeep (dceLive g) st = true ∧ v ∈ st.results ∧
          s = (i, fidx (dceKeep (dceLive g)) b.body j + 1)) := by
  rw [mem_defSites]
  simp only [dce_get, Option.map_eq_some_iff]
  constructor
  · rintro ⟨i, b', ⟨b, hb, rfl⟩, h | ⟨j', st, hst, hv, rfl⟩⟩
    · exact ⟨i, b, hb, .inl h⟩
    · obtain ⟨j, hj, hk, rfl⟩ := exists_fidx _ b.body j' st hst
      exact ⟨i, b, hb, .inr ⟨j, st, hj, hk, hv, rfl⟩⟩
  · rintro ⟨i, b, hb, h | ⟨j, st, hj, hk, hv, rfl⟩⟩
    · exact ⟨i, _, ⟨b, hb, rfl⟩, .inl h⟩
    · exact ⟨i, _, ⟨b, hb, rfl⟩, .inr ⟨_, st, getElem?_filter_fidx _ b.body j st hj hk, hv, rfl⟩⟩

/-- The position of a definition site of block `b` after filtering its body with `p`. -/
def fpos (p : Stmt → Bool) (b : Block) : Nat → Nat
  | 0 => 0
  | j + 1 => fidx p b.body j + 1

section DceWf

variable {g : Function} {info : Info} (hc : Checked g info)
include hc

theorem dce_nodup : ((defList (dce g).1).map (·.1)).Nodup :=
  (dce_defList_sublist g |>.map (·.1)).nodup hc.nodup

theorem dce_unique : UniqueDefs (dce g).1 := by
  unfold UniqueDefs
  rw [defSites_map_fst (dce_arity g hc.arity)]
  exact dce_nodup hc

omit hc in
theorem dce_live_site {v : ValueId} {d t : Nat} (hs : (v, (d, t)) ∈ defSites g)
    (hl : (dceLive g).contains v = true) :
    ∃ b, g.blocks[d]? = some b ∧ (v, (d, fpos (dceKeep (dceLive g)) b t)) ∈ defSites (dce g).1 ∧
      ∀ j0, t = j0 + 1 → ∃ st0, b.body[j0]? = some st0 ∧ dceKeep (dceLive g) st0 = true := by
  obtain ⟨i, b, hb, ⟨p, hp, rfl, he⟩ | ⟨j, st, hj, hv, he⟩⟩ := mem_defSites.1 hs
  · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact ⟨b, hb, dce_mem_defSites.2 ⟨d, b, hb, .inl ⟨p, hp, rfl, rfl⟩⟩, fun j0 h => by cases h⟩
  · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    have hk : dceKeep (dceLive g) st = true := by
      simp only [dceKeep, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true]
      exact .inr ⟨v, hv, hl⟩
    refine ⟨b, hb, dce_mem_defSites.2 ⟨d, b, hb, .inr ⟨j, st, hj, hk, hv, rfl⟩⟩, fun j0 h => ?_⟩
    cases h; exact ⟨st, hj, hk⟩

theorem dce_idom : (wfData (dce g).1 (coreInfo (dce g).1)).idom = (wfData g info).idom := by
  simp [wfData, coreInfo, dce_build, hc.info_eq]

theorem dce_rank : (wfData (dce g).1 (coreInfo (dce g).1)).rank = (wfData g info).rank := by
  simp [wfData, coreInfo, dce_build, hc.info_eq]

theorem dce_index : (wfData (dce g).1 (coreInfo (dce g).1)).index = (wfData g info).index := by
  simp [wfData, coreInfo, dce_build, hc.info_eq]

/-- Availability moves to the filtered position. -/
theorem dce_avail {i : Nat} {b : Block} (hb : g.blocks[i]? = some b) {j : Nat} {v : ValueId}
    (hl : (dceLive g).contains v = true) (hA : Avail (wfData g info) i j v) :
    Avail (wfData (dce g).1 (coreInfo (dce g).1)) i (fidx (dceKeep (dceLive g)) b.body j) v := by
  obtain ⟨d, t, hd, h⟩ := hA
  have hs := hc.wf.sitesRev v (d, t) hd
  obtain ⟨bd, hbd, hs', hk⟩ := dce_live_site hs hl
  refine ⟨d, fpos (dceKeep (dceLive g)) bd t, (defMap_get_iff (dce_unique hc) v _).2 hs', ?_⟩
  rcases h with ⟨rfl, ht⟩ | ⟨hne, ha⟩
  · left
    refine ⟨rfl, ?_⟩
    rw [hb] at hbd; cases hbd
    cases t with
    | zero => simp [fpos]
    | succ j0 =>
      obtain ⟨st0, h0, hk0⟩ := hk j0 rfl
      exact fidx_lt _ b.body (by omega) h0 hk0
  · right
    exact ⟨hne, by rw [dce_idom hc]; exact ha⟩

/-- **The output of DCE satisfies the certificate facts** (over its own `checkCore` data). -/
theorem dce_wf : Wf (dce g).1 (wfData (dce g).1 (coreInfo (dce g).1)) := by
  have hW := hc.wf
  have hn' := dce_nodup hc
  refine { ids := ?_, sites := ?_, sitesRev := ?_, root := ?_, rank := ?_, params := ?_,
           uses := ?_, results := ?_, pure := ?_, termUses := ?_, edges := ?_ }
  · intro i b' hb'
    rw [dce_get, Option.map_eq_some_iff] at hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    rw [dce_index hc]; exact hW.ids i b hb
  · exact fun v s hs => (defMap_get_iff (dce_unique hc) v s).2 hs
  · exact fun v s hs => (defMap_get_iff (dce_unique hc) v s).1 hs
  · rw [dce_idom hc]; exact hW.root
  · rw [dce_idom hc, dce_rank hc]; exact hW.rank
  · exact fun i b hb p hp => tm_param hn' hb hp
  · intro i b' hb' j' st hst v hv
    rw [dce_get, Option.map_eq_some_iff] at hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    obtain ⟨j, hj, hk, rfl⟩ := exists_fidx _ b.body j' st hst
    exact dce_avail hc hb (dce_ops_live hc.unique (List.mem_of_getElem? hb) (List.mem_of_getElem? hj)
      hk hv) (hW.uses i b hb j st hj v hv)
  · intro i b' hb' j' st hst
    have hb'' := hb'
    rw [dce_get, Option.map_eq_some_iff] at hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    obtain ⟨j, hj, hk, rfl⟩ := exists_fidx _ b.body j' st hst
    obtain ⟨ts, hts, hlen, -⟩ := hW.results i b hb j st hj
    have hts' : st.inst.resultTypes (sigOf (dce g).1) (fun _ => none) = some ts := by
      rw [show sigOf (dce g).1 = sigOf g by rw [dce_eq]; rfl]; exact hts
    exact ⟨ts, hts', hlen, fun n r hr => tm_result hn' hb'' (List.mem_of_getElem? hst) hts' hlen hr⟩
  · intro i b' hb' j' st hst hp
    rw [dce_get, Option.map_eq_some_iff] at hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    obtain ⟨j, hj, hk, rfl⟩ := exists_fidx _ b.body j' st hst
    have hbm := List.mem_of_getElem? hb
    have hsm := List.mem_of_getElem? hj
    rw [← hW.pure i b hb j st hj hp]
    apply pureTyped_congr _ (by rw [dce_eq]) (by rw [dce_eq])
    intro x hx
    simp only [wfData, coreInfo, hc.info_eq, Std.HashMap.get?_eq_getElem?]
    exact (dce_lookup hc (dce_ops_live hc.unique hbm hsm hk hx) (hc.op_defined hb hsm hx)).1
  · intro i b' hb' v hv
    rw [dce_get, Option.map_eq_some_iff] at hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    have := dce_avail hc hb (dce_term_live g (List.mem_of_getElem? hb) hv) (hW.termUses i b hb v hv)
    rw [fidx_length] at this
    exact this
  · intro i b' hb' id hid
    rw [dce_get, Option.map_eq_some_iff] at hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    obtain ⟨j, b0, hj, hb0, hid0, hanc⟩ := hW.edges i b hb id hid
    refine ⟨j, fltB (dceLive g) b0, by rw [dce_index hc]; exact hj, by rw [dce_get, hb0]; rfl,
      hid0, ?_⟩
    rw [dce_idom hc]; exact hanc

/-- **`check` accepts DCE's output.** -/
theorem dce_check : check (dce g).1 = .ok (coreInfo (dce g).1) := by
  have hw : wfCert (dce g).1 (coreInfo (dce g).1).cfg (coreInfo (dce g).1).types = true :=
    wfCert_complete (dce_wf hc)
  exact (check_ok_iff (dce g).1 (coreInfo (dce g).1)).2 ⟨dce_coreOk hc, rfl, hw⟩

/-- A deleted statement can be deleted (its results are not defined in the output). -/
theorem dce_delOk {i : Nat} {b : Block} (hb : g.blocks[i]? = some b) {s : Stmt} (hs : s ∈ b.body)
    (hk : dceKeep (dceLive g) s = false) (gidom : Array (Option Nat)) (gblocks : Array Block)
    (k : Nat) :
    EditCtx.delOk { σ := id, gdm := (defMap (dce g).1).get?, gidom, gblocks, bi := i } s k = true := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hs
  simp only [dceKeep, Bool.or_eq_false_iff, Bool.not_eq_false', List.any_eq_false] at hk
  simp only [EditCtx.delOk, hk.1, Bool.true_and, Bool.or_eq_true, List.all_eq_true, id,
    Option.isNone_iff_eq_none]
  left
  intro r hr
  cases hg : (defMap (dce g).1).get? r with
  | none => rfl
  | some s' =>
    exfalso
    have hs' := (defMap_get_iff (dce_unique hc) r s').1 hg
    have hsite : (r, (i, j + 1)) ∈ defSites g := mem_defSites.2 ⟨i, b, hb, .inr ⟨j, s, hj, hr, rfl⟩⟩
    obtain ⟨i', b', hb', ⟨p, hp, hpr, rfl⟩ | ⟨j', st, hj', hk', hr', rfl⟩⟩ := dce_mem_defSites.1 hs'
    · have := site_unique hc.unique hsite (mem_defSites.2 ⟨i', b', hb', .inl ⟨p, hp, hpr, rfl⟩⟩)
      simp at this
    · have := site_unique hc.unique hsite (mem_defSites.2 ⟨i', b', hb', .inr ⟨j', st, hj', hr', rfl⟩⟩)
      simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at this
      obtain ⟨rfl, rfl⟩ := this
      rw [hb] at hb'; cases hb'
      rw [hj] at hj'; cases hj'
      simp only [dceKeep, hk.1, Bool.not_true, Bool.false_or, List.any_eq_true] at hk'
      obtain ⟨x, hx, hxl⟩ := hk'
      exact absurd hxl (by simpa using hk.2 x hx)

/-- **The edit validator accepts DCE's output** (renaming `id`). -/
theorem dce_editOk : editOk id g (dce g).1 info (coreInfo (dce g).1) = true := by
  have hidom : (coreInfo (dce g).1).cfg.idom = info.cfg.idom := dce_idom hc
  simp only [editOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, hidom⟩, by rw [dce_blocks, List.length_map]⟩, ?_⟩, ?_⟩
  · simp [sameHeader, dce_eq]
  · rintro ⟨⟨b, b'⟩, i⟩ hx
    have hx' := List.mem_zipIdx_iff_getElem?.1 hx
    simp only [List.getElem?_zip_eq_some] at hx'
    obtain ⟨hb, hb'⟩ := hx'
    rw [dce_get, hb] at hb'
    simp only [Option.map_some, Option.some.injEq] at hb'
    subst hb'
    simp only [fltB, id, mapTerm_id, implies_true, and_true, true_and]
    exact align_filter _ rfl _ b.body
      (fun s hs hk k => dce_delOk hc hb hs hk _ _ k) 0
  · rintro ⟨v, d, t⟩ hv
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at hv
    have hs : (v, (d, t)) ∈ defSites g := (defMap_get_iff hc.unique v _).1
      (by rw [Std.HashMap.get?_eq_getElem?]; exact hv)
    simp only [id]
    split
    · rename_i d' t' hg
      have hs' := (defMap_get_iff (dce_unique hc) v _).1 hg
      obtain ⟨i', b', hb', ⟨p, hp, hpr, he⟩ | ⟨j', st, hj', -, hr', he⟩⟩ := dce_mem_defSites.1 hs'
      · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        have := site_unique hc.unique hs (mem_defSites.2 ⟨d', b', hb', .inl ⟨p, hp, hpr, rfl⟩⟩)
        simp only [Prod.mk.injEq] at this; rw [this.1]; exact ancB_refl _ _ _
      · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        have := site_unique hc.unique hs (mem_defSites.2 ⟨d', b', hb', .inr ⟨j', st, hj', hr', rfl⟩⟩)
        simp only [Prod.mk.injEq] at this; rw [this.1]; exact ancB_refl _ _ _
    · rfl

end DceWf

/-- **Completeness of the DCE stage**: on a well-formed function, DCE's output passes `check` and
the edit validator, so `Opt.optimizeReport` never stops at a DCE stage. -/
theorem dce_complete {g : Function} {info : Info} (h : check g = .ok info) :
    check (dce g).1 = .ok (coreInfo (dce g).1) ∧
      editOk id g (dce g).1 info (coreInfo (dce g).1) = true :=
  ⟨dce_check (checked_of_check h), dce_editOk (checked_of_check h)⟩

end Opt

namespace Opt.CompleteDceWitness

open Clif

/-- `v0` is dead; `v1` is returned. -/
def fn : Function where
  name := "w"
  sig := {}
  blocks := [{ id := 0, body := [{ results := [0], inst := .iconst .i32 1 },
    { results := [1], inst := .iconst .i32 2 }], term := .ret [1] }]

theorem checks : (match check fn with | .ok _ => true | .error _ => false) = true := by native_decide

/-- Non-vacuity of `dce_complete`: `fn` is well-formed, DCE removes `v0`, and the stage is
accepted. -/
theorem witness : (dce fn).2 = 1 ∧ ∃ i i', check fn = .ok i ∧ check (dce fn).1 = .ok i' ∧
    editOk id fn (dce fn).1 i i' = true := by
  refine ⟨by native_decide, ?_⟩
  have h := checks
  split at h
  · rename_i i hi
    exact ⟨i, _, hi, (dce_complete hi).1, (dce_complete hi).2⟩
  · cases h

end Opt.CompleteDceWitness
