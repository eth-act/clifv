module

public import FV.Backend.RegallocPerEdgePrepare
public import FV.Backend.Proof.PrepareComplete
public import FV.Backend.Proof.RegallocLemmas

@[expose] public section

/-! The indexed splitting loop has the same label graph as the original loop.
Only synthetic-block branch arguments are erased in this proof projection;
the executable blocks and their per-successor vectors are retained unchanged.
This lets graph reasoning reuse the original reachability/splitting facts. -/
namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof

abbrev EdgeRow := Array (Array Reg)
abbrev InnerState := Nat × Array VBlock × Array EdgeRow × EdgeRow × Array Label

def graphBlock (b : VBlock) : VBlock := { b with branchArgs := #[] }

def graphState (st : InnerState) : Nat × Array VBlock × Array Label :=
  (st.1, st.2.1.map graphBlock, st.2.2.2.2)

/-- Exact pure step of prepareAt's indexed inner loop, in its SSA tuple order. -/
def innerStepAt (preds : Array (Array Nat)) (st : InnerState)
    (x : (Nat × Label) × Nat) : InnerState :=
  if preds[x.1.1]!.size > 1 then
    (st.1 + 1,
      st.2.1.push {label := st.1, insts := #[.jump x.1.2], branchArgs := st.2.2.2.1[x.2]!},
      st.2.2.1.push #[st.2.2.2.1[x.2]!], st.2.2.2.1.set! x.2 #[], st.2.2.2.2.push st.1)
  else (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.push x.1.2)

/-- Indexed copies do not affect the splitting step's graph projection. -/
theorem innerStepAt_graph (preds : Array (Array Nat)) (st : InnerState)
    (x : (Nat × Label) × Nat) :
    graphState (innerStepAt preds st x) = Prep.innerStep preds (graphState st) x.1 := by
  unfold innerStepAt Prep.innerStep
  split <;> simp [graphState, graphBlock]

/-- Every complete indexed inner fold projects to the original graph fold. -/
theorem innerFoldAt_graph (preds : Array (Array Nat))
    (xs : List ((Nat × Label) × Nat)) (st : InnerState) :
    graphState (xs.foldl (innerStepAt preds) st) =
      (xs.map Prod.fst).foldl (Prep.innerStep preds) (graphState st) := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, innerStepAt_graph]

/-- The actual monadic inner-loop body is the pure indexed fold above. -/
theorem innerForInAt_eq (preds : Array (Array Nat))
    (xs : Array ((Nat × Label) × Nat)) (st : InnerState) :
    (forIn xs st fun x st => do
      if preds[x.1.1]!.size > 1 then
        let args := st.2.2.2.1[x.2]!
        pure (.yield (st.1 + 1,
          st.2.1.push {label := st.1, insts := #[.jump x.1.2], branchArgs := args},
          st.2.2.1.push #[args], st.2.2.2.1.set! x.2 #[], st.2.2.2.2.push st.1))
      else pure (.yield (st.1, st.2.1, st.2.2.1, st.2.2.2.1,
        st.2.2.2.2.push x.1.2)) : Except String InnerState) =
      .ok (xs.toList.foldl (innerStepAt preds) st) := by
  rw [← Array.forIn_toList]
  exact Prep.forIn_yield_foldl _ _ (innerStepAt preds) _ (fun x st => by
    unfold innerStepAt
    split <;> rfl)

/-- Synthetic blocks and synthetic outgoing rows remain paired. This invariant
does not impose any restrictions on the copied registers or target parameters. -/
def EdgeRowsAgree (E : Array VBlock) (rows : Array EdgeRow) : Prop :=
  E.size = rows.size ∧ ∀ (e : Nat) (b : VBlock),
    E[e]? = some b → rows[e]? = some #[b.branchArgs]

private theorem edgeRowsAgree_push {E : Array VBlock} {rows : Array EdgeRow}
    (h : EdgeRowsAgree E rows) (b : VBlock) :
    EdgeRowsAgree (E.push b) (rows.push #[b.branchArgs]) := by
  refine ⟨by simpa using h.1, ?_⟩
  have sizes := h.1
  intro e block hb
  by_cases he : e < E.size
  · simp only [Array.getElem?_push, Nat.ne_of_lt he, ite_false] at hb
    simp only [Array.getElem?_push, show e ≠ rows.size by omega, ite_false]
    exact h.2 e block hb
  · have bound := (Array.getElem?_eq_some_iff.mp hb).1
    simp only [Array.size_push] at bound
    have : e = E.size := by omega
    subst e
    simp only [Array.getElem?_push, ↓reduceIte, Option.some.injEq] at hb
    subst block
    simp [h.1]

/-- Both branches of the real step preserve the block/vector pairing. -/
theorem innerStepAt_rows (preds : Array (Array Nat)) (st : InnerState)
    (x : (Nat × Label) × Nat) (h : EdgeRowsAgree st.2.1 st.2.2.1) :
    EdgeRowsAgree (innerStepAt preds st x).2.1 (innerStepAt preds st x).2.2.1 := by
  unfold innerStepAt
  split
  · exact edgeRowsAgree_push h _
  · exact h

/-- Pairing is maintained throughout the indexed loop, including preexisting
synthetic blocks from earlier source blocks. -/
theorem innerFoldAt_rows (preds : Array (Array Nat))
    (xs : List ((Nat × Label) × Nat)) (st : InnerState)
    (h : EdgeRowsAgree st.2.1 st.2.2.1) :
    EdgeRowsAgree (xs.foldl (innerStepAt preds) st).2.1
      (xs.foldl (innerStepAt preds) st).2.2.1 := by
  induction xs generalizing st with
  | nil => exact h
  | cons x xs ih => exact ih _ (innerStepAt_rows preds st x h)

/-- Fresh labels, old synthetic blocks, and label positions are preserved by
the complete indexed inner loop, by transport of the original graph proof. -/
theorem innerFoldAt_facts (preds : Array (Array Nat)) (next0 : Nat)
    (xs : List ((Nat × Label) × Nat)) (st : InnerState)
    (hn : st.2.1.size + next0 = st.1)
    (he : Prep.EdgesOk next0 (st.2.1.map graphBlock)) :
    let out := xs.foldl (innerStepAt preds) st
    out.2.1.size + next0 = out.1 ∧
    Prep.EdgesOk next0 (out.2.1.map graphBlock) ∧
    Prep.Ext (st.2.1.map graphBlock) (out.2.1.map graphBlock) ∧
    out.2.2.2.2.size = st.2.2.2.2.size + xs.length ∧
    (∀ j, j < st.2.2.2.2.size → out.2.2.2.2[j]? = st.2.2.2.2[j]?) ∧
    ∀ (j : Nat) (x : (Nat × Label) × Nat), xs[j]? = some x → ∃ label,
      out.2.2.2.2[st.2.2.2.2.size + j]? = some label ∧
      (label = x.1.2 ∨ ∃ e : Nat, (out.2.1.map graphBlock)[e]? =
        some ({label := label, insts := #[.jump x.1.2]} : VBlock)) := by
  have facts := Prep.innerFold preds next0 (xs.map Prod.fst) st.1
    (st.2.1.map graphBlock) st.2.2.2.2 (by simpa using hn) he
  have eq := innerFoldAt_graph preds xs st
  dsimp only [graphState] at eq
  rw [← eq] at facts
  simp only [Array.size_map, List.length_map] at facts
  exact ⟨facts.1, facts.2.1, facts.2.2.1, facts.2.2.2.1, facts.2.2.2.2.1,
    fun j x hx => facts.2.2.2.2.2 j x.1 (by simp [hx])⟩

/-- A selected copy is either still at its original source edge, or has moved
intact to a new single-jump block with an empty first copy. -/
def CopyRoute (st : InnerState) (j : Nat) (target : Label) (args : Array Reg) : Prop :=
  ∃ label, st.2.2.2.2[j]? = some label ∧
    ((label = target ∧ st.2.2.2.1[j]? = some args) ∨
      (st.2.2.2.1[j]? = some #[] ∧ ∃ e : Nat,
        st.2.1[e]? = some {label := label, insts := #[.jump target], branchArgs := args} ∧
        st.2.2.1[e]? = some #[args]))

private theorem innerStepAt_old_route (preds : Array (Array Nat)) (st : InnerState)
    (x : (Nat × Label) × Nat) {j : Nat} {target : Label} {args : Array Reg}
    (hj : j < st.2.2.2.2.size) (hne : x.2 ≠ j) (h : CopyRoute st j target args) :
    CopyRoute (innerStepAt preds st x) j target args := by
  rcases h with ⟨label, hl, h⟩
  unfold innerStepAt
  split
  · refine ⟨label, by simpa [Array.getElem?_push, Nat.ne_of_lt hj] using hl, ?_⟩
    rcases h with ⟨same, row⟩ | ⟨row, e, block, edge⟩
    · exact .inl ⟨same, by simpa [Array.set!, hne] using row⟩
    · have eb := (Array.getElem?_eq_some_iff.mp block).1
      have er := (Array.getElem?_eq_some_iff.mp edge).1
      refine .inr ⟨by simpa [Array.set!, hne] using row, e, ?_, ?_⟩
      · simpa [Array.getElem?_push, Nat.ne_of_lt eb] using block
      · simpa [Array.getElem?_push, Nat.ne_of_lt er] using edge
  · exact ⟨label, by simpa [Array.getElem?_push, Nat.ne_of_lt hj] using hl, h⟩

private theorem innerStepAt_new_route (preds : Array (Array Nat)) (st : InnerState)
    (x : (Nat × Label) × Nat) (args : Array Reg)
    (hi : x.2 = st.2.2.2.2.size) (hrow : st.2.2.2.1[x.2]? = some args)
    (hs : st.2.1.size = st.2.2.1.size) :
    CopyRoute (innerStepAt preds st x) x.2 x.1.2 args := by
  have bound := (Array.getElem?_eq_some_iff.mp hrow).1
  have value : st.2.2.2.1[x.2]! = args := by
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hrow]
    rfl
  unfold innerStepAt
  split
  · refine ⟨st.1, by simp [hi], .inr ⟨?_, st.2.1.size, ?_, ?_⟩⟩
    · simp [Array.set!, Array.getElem?_setIfInBounds_self_of_lt bound]
    · simp [value]
    · simp [hs, value]
  · exact ⟨x.1.2, by simp [hi], .inl ⟨rfl, hrow⟩⟩

private structure CopyInv (targets : Array Label) (original : EdgeRow)
    (k : Nat) (st : InnerState) : Prop where
  labels : st.2.2.2.2.size = k
  paired : EdgeRowsAgree st.2.1 st.2.2.1
  pending : ∀ j, k ≤ j → st.2.2.2.1[j]? = original[j]?
  routes : ∀ j, j < k → ∀ target args,
    targets[j]? = some target → original[j]? = some args → CopyRoute st j target args

private theorem innerStepAt_copyInv (preds : Array (Array Nat))
    (targets : Array Label) (original : EdgeRow) (k : Nat) (st : InnerState)
    (x : (Nat × Label) × Nat) (h : CopyInv targets original k st)
    (hi : x.2 = k) (ht : targets[k]? = some x.1.2) :
    CopyInv targets original (k + 1) (innerStepAt preds st x) := by
  refine ⟨?_, innerStepAt_rows preds st x h.paired, ?_, ?_⟩
  · unfold innerStepAt
    split <;> simpa using h.labels
  · intro j hj
    have ne : x.2 ≠ j := by omega
    unfold innerStepAt
    split <;> simpa [Array.set!, ne] using h.pending j (by omega)
  · intro j hj target args ht' ha'
    by_cases old : j < k
    · exact innerStepAt_old_route preds st x (by rw [h.labels]; exact old)
        (by omega) (h.routes j old target args ht' ha')
    · have eq : j = k := by omega
      subst j
      rw [ht] at ht'
      cases ht'
      have row := h.pending k (Nat.le_refl _)
      rw [ha'] at row
      have idx : x.2 = st.2.2.2.2.size := by rw [hi, h.labels]
      simpa only [hi] using innerStepAt_new_route preds st x args idx
        (by simpa only [hi] using row) h.paired.1

/-- Every selected outgoing vector survives the complete actual inner loop.
The result gives the direct or split copy route for every original successor,
without restricting the registers or requiring empty destination parameters. -/
theorem innerFoldAt_copies (preds : Array (Array Nat))
    (successors : Array Nat) (targets : Array Label) (original : EdgeRow)
    (next : Nat) (E : Array VBlock) (rows : Array EdgeRow)
    (hpair : EdgeRowsAgree E rows)
    (hss : successors.size = targets.size) :
    let out := ((successors.zip targets).zipIdx).toList.foldl (innerStepAt preds)
      (next, E, rows, original, #[])
    out.2.2.2.2.size = targets.size ∧ EdgeRowsAgree out.2.1 out.2.2.1 ∧
      ∀ (j : Nat) (target : Label) (args : Array Reg),
        targets[j]? = some target → original[j]? = some args → CopyRoute out j target args := by
  let xs := ((successors.zip targets).zipIdx).toList
  have inv : CopyInv targets original xs.length
      (xs.foldl (innerStepAt preds) (next, E, rows, original, #[])) := by
    have loop : (forIn xs (next, E, rows, original, #[])
        (fun x st => pure (.yield (innerStepAt preds st x))) : Except String InnerState) =
        .ok (xs.foldl (innerStepAt preds) (next, E, rows, original, #[])) :=
      Prep.forIn_yield_foldl _ _ _ _ (fun _ _ => rfl)
    apply Prep.forIn_inv _ xs (CopyInv targets original) ?_ ?_ _ _ ?_ loop
    · intro k x st st' hx hs hf
      simp only [pure, Except.pure, Except.ok.injEq, ForInStep.yield.injEq] at hf
      subst st'
      have hx' := hx
      dsimp only [xs] at hx'
      rw [Array.toList_zipIdx, List.getElem?_zipIdx] at hx'
      have input : ∃ y, (successors.zip targets).toList[k]? = some y ∧ x = (y,k) := by
        cases hy : (successors.zip targets).toList[k]? with
        | none => rw [hy] at hx'; cases hx'
        | some y =>
          rw [hy] at hx'
          simp only [Option.map_some, Option.some.injEq, Nat.zero_add] at hx'
          exact ⟨y, rfl, hx'.symm⟩
      rcases input with ⟨y, hy, rfl⟩
      have target : targets[k]? = some y.2 := by
        rw [Array.toList_zip] at hy
        simpa using (List.getElem?_zip_eq_some.mp hy).2
      exact innerStepAt_copyInv preds targets original k st (y,k) hs rfl target
    · intro x st st' hf
      cases hf
    · exact ⟨rfl, hpair, fun _ _ => rfl, fun j hj => by omega⟩
  have len : xs.length = targets.size := by simp [xs, hss]
  change (xs.foldl (innerStepAt preds) (next, E, rows, original, #[])).2.2.2.2.size =
    targets.size ∧ _
  exact ⟨by rw [inv.labels, len], inv.paired, fun j target args ht ha =>
    inv.routes j (by have := (Array.getElem?_eq_some_iff.mp ht).1; omega) target args ht ha⟩

abbrev OuterState := Nat × Array VBlock × Array EdgeRow × Array VBlock × Array EdgeRow

/-- Actual outer-loop body, with the proved pure inner fold substituted. -/
def outerStepAt (succs preds : Array (Array Nat)) (outgoing : Array EdgeRow)
    (x : VBlock × Nat) (st : OuterState) : Except String (ForInStep OuterState) := do
  let ss := succs[x.2]!
  let row := outgoing[x.2]!
  if ss.size < 2 then
    return .yield (st.1, st.2.1.push x.1, st.2.2.1.push row, st.2.2.2.1, st.2.2.2.2)
  let some t := x.1.insts.back? | throw "empty block"
  let inner := ((ss.zip t.targets.toArray).zipIdx).toList.foldl (innerStepAt preds)
    (st.1, st.2.2.2.1, st.2.2.2.2, row, #[])
  let some t' := t.setTargets inner.2.2.2.2.toList | throw "setTargets"
  pure (.yield (inner.1, st.2.1.push {x.1 with insts := x.1.insts.pop.push t'},
    st.2.2.1.push inner.2.2.2.1, inner.2.1, inner.2.2.1))

def keptAt (vc : VCode) (edges : Array EdgeRow) (ss : Array (Array Nat)) :
    Array (VBlock × EdgeRow) :=
  ((vc.blocks.zip edges).zip (reachable ss)).filterMap fun ((b,args),live) =>
    if live then some (b,args) else none

/-- Every successful actual preparation supplies the normalized outer-loop
execution and the exact filtering, concatenation and RPO stages. This is derived
from prepareAt itself, rather than supplied as an extra caller certificate. -/
theorem prepareAt_stages {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (h : prepareAt vc edges = .ok p) :
    ∃ (ss0 ps0 ss1 ps1 ss2 ps2 : Array (Array Nat)) (st : OuterState),
      vc.cfg = .ok (ss0, ps0) ∧
      ({vc with blocks := (keptAt vc edges ss0).map Prod.fst} : VCode).cfg = .ok (ss1, ps1) ∧
      forIn ((keptAt vc edges ss0).map Prod.fst).zipIdx
        (Prep.next0Of ((keptAt vc edges ss0).map Prod.fst), #[], #[], #[], #[])
        (outerStepAt ss1 ps1 ((keptAt vc edges ss0).map Prod.snd)) = .ok st ∧
      ({vc with blocks := st.2.1 ++ st.2.2.2.1} : VCode).cfg = .ok (ss2, ps2) ∧
      p = ⟨{vc with blocks := (rpo ss2).map fun i => (st.2.1 ++ st.2.2.2.1)[i]!},
        (rpo ss2).map fun i => (st.2.2.1 ++ st.2.2.2.2)[i]!⟩ := by
  unfold prepareAt at h
  obtain ⟨⟨ss0,ps0⟩,cfg0,h⟩ := Except.bind_ok h
  dsimp only at h
  cases count : (edges.size != vc.blocks.size) with
  | true => simp [count,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at h
  | false =>
    simp only [count,Bool.false_eq_true,ite_false] at h
    obtain ⟨answer,rows,h⟩ := Except.bind_ok h
    cases answer
    obtain ⟨⟨ss1,ps1⟩,cfg1,h⟩ := Except.bind_ok h
    dsimp only at h
    cases incoming : (!(ps1[0]?.getD #[]).isEmpty) with
    | true => simp [incoming,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at h
    | false =>
      simp only [incoming,Bool.false_eq_true,ite_false] at h
      split at h
      · simp [bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at h
      · obtain ⟨st,loop,h⟩ := Except.bind_ok h
        obtain ⟨⟨ss2,ps2⟩,cfg2,h⟩ := Except.bind_ok h
        cases h
        refine ⟨ss0,ps0,ss1,ps1,ss2,ps2,st,cfg0,cfg1,?_,cfg2,rfl⟩
        refine Eq.trans ?_ loop
        congr 1
        funext x state
        simp only [outerStepAt, innerForInAt_eq, bind, Except.bind,
          throw, throwThe, MonadExceptOf.throw, keptAt]
        rfl

end Backend.Proof.PerEdgePrep
