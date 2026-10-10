import FV.Backend.Proof.DeadCleanupCFG
import FV.Backend.Proof.PrepareComplete
import FV.Backend.Proof.RegallocOperands

namespace Backend.DeadCleanup
open Backend.Proof Backend.Proof.Prep

/-! Exact structural correspondence of preparation before and after cleanup.
The map uses the original boundary liveness after CFG restructuring. -/

private def splitRun (vc : VCode) (succs preds : Array (Array Nat)) :
    Except String (Nat × Array VBlock × Array VBlock) := do
  let mut next := (vc.blocks.foldl (fun m (b : VBlock) => max m b.label) 0) + 1
  let mut blocks : Array VBlock := #[]
  let mut edges : Array VBlock := #[]
  for (b, i) in vc.blocks.zipIdx do
    let ss := succs[i]!
    if ss.size < 2 then
      blocks := blocks.push b
      continue
    let some t := b.insts.back? | throw "empty block"
    let mut ls : Array Label := #[]
    for (s, l) in ss.zip t.targets.toArray do
      if preds[s]!.size > 1 then
        edges := edges.push { label := next, insts := #[.jump l] }
        ls := ls.push next
        next := next + 1
      else ls := ls.push l
    let some t' := t.setTargets ls.toList | throw "setTargets"
    blocks := blocks.push { b with insts := b.insts.pop.push t' }
  pure (next, blocks, edges)

private def splitBody (succs preds : Array (Array Nat)) (x : VBlock × Nat)
    (st : Nat × Array VBlock × Array VBlock) :
    Except String (ForInStep (Nat × Array VBlock × Array VBlock)) := do
  let (b, i) := x
  let (next, blocks, edges) := st
  let ss := succs[i]!
  if ss.size < 2 then return .yield (next, blocks.push b, edges)
  let some t := b.insts.back? | throw "empty block"
  let mut next := next
  let mut edges := edges
  let mut ls : Array Label := #[]
  for (s, l) in ss.zip t.targets.toArray do
    if preds[s]!.size > 1 then
      edges := edges.push { label := next, insts := #[.jump l] }
      ls := ls.push next
      next := next + 1
    else ls := ls.push l
  let some t' := t.setTargets ls.toList | throw "setTargets"
  return .yield (next, blocks.push { b with insts := b.insts.pop.push t' }, edges)

private theorem splitRun_body (vc : VCode) (ss ps : Array (Array Nat)) :
    splitRun vc ss ps = forIn vc.blocks.zipIdx (next0Of vc.blocks, #[], #[]) (splitBody ss ps) := by
  simp [splitRun, splitBody, next0Of]
  congr 1

private def prepareRepr (vc : VCode) : Except String VCode := do
  let (succs, _) ← vc.cfg
  let vc := { vc with blocks := keep vc.blocks (reachable succs) }
  let (succs, preds) ← vc.cfg
  if !(preds[0]?.getD #[]).isEmpty then throw "the entry block is a branch target"
  if !(vc.blocks[0]?.map (fun (b : VBlock) => b.params.isEmpty)).getD true then
    throw "entry block has parameters"
  let (_, blocks, edges) ← splitRun vc succs preds
  let vc := { vc with blocks := blocks ++ edges }
  let (succs, _) ← vc.cfg
  pure { vc with blocks := (rpo succs).map fun i => vc.blocks[i]! }

private theorem prepare_repr (vc : VCode) : prepare vc = prepareRepr vc := by
  simp only [prepare, prepareRepr, splitRun, bind_assoc]
  rfl

private def mapBlocks (T : VBlock → VBlock) (vc : VCode) : VCode :=
  { vc with blocks := vc.blocks.map T }

private structure BlockMap (T : VBlock → VBlock) : Prop where
  default : T default = default
  label : ∀ b, (T b).label = b.label
  params : ∀ b, (T b).params = b.params
  branchArgs : ∀ b, (T b).branchArgs = b.branchArgs
  back : ∀ b, (T b).insts.back? = b.insts.back?
  jump : ∀ lab l, T { label := lab, insts := #[.jump l] } = { label := lab, insts := #[.jump l] }
  retarget : ∀ b t t' ls, b.insts.back? = some t →
    t.setTargets ls = some t' →
    T { b with insts := b.insts.pop.push t' } =
      { T b with insts := (T b).insts.pop.push t' }

private def mapStep {β γ : Type} (g : β → γ) : ForInStep β → ForInStep γ
  | .done b => .done (g b)
  | .yield b => .yield (g b)

private theorem forIn_map_state {α α' β γ ε : Type} (f : α → α') (g : β → γ)
    (body : α → β → Except ε (ForInStep β))
    (body' : α' → γ → Except ε (ForInStep γ))
    (h : ∀ a b, body' (f a) (g b) = (body a b).map (mapStep g))
    (xs : List α) (b : β) :
    forIn (xs.map f) (g b) body' = (forIn xs b body).map g := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons, List.forIn_cons, h, bind, Except.bind]
    cases hb : body a b with
    | error e => rfl
    | ok st =>
      cases st with
      | done b' => rfl
      | yield b' => exact ih b'

private theorem mapBlocks_cfg {T : VBlock → VBlock} (hT : BlockMap T) (vc : VCode) :
    (mapBlocks T vc).cfg = vc.cfg := by
  unfold VCode.cfg
  simp only [mapBlocks, Array.size_map, Array.findIdx?_map, Function.comp_def, hT.label]
  rw [Array.mapM_map]
  simp only [Function.comp_def, hT.back, hT.label]

private theorem keep_map (T : VBlock → VBlock) (bs : Array VBlock) (live : Array Bool) :
    keep (bs.map T) live = (keep bs live).map T := by
  simp only [keep, Array.zip_map_left, Array.filterMap_map, Array.map_filterMap]
  congr 1
  funext x
  rcases x with ⟨b, q⟩
  cases q <;> rfl

private theorem next0_map {T : VBlock → VBlock} (hT : BlockMap T) (bs : Array VBlock) :
    next0Of (bs.map T) = next0Of bs := by
  simp only [next0Of, Array.foldl_map, hT.label]

private def mapSplit (T : VBlock → VBlock) (st : Nat × Array VBlock × Array VBlock) :=
  (st.1, st.2.1.map T, st.2.2.map T)

private def mapInner (T : VBlock → VBlock) (st : Nat × Array VBlock × Array Label) :=
  (st.1, st.2.1.map T, st.2.2)

private theorem innerStep_map {T : VBlock → VBlock} (hT : BlockMap T)
    (ps : Array (Array Nat)) (st : Nat × Array VBlock × Array Label) (x : Nat × Label) :
    innerStep ps (mapInner T st) x = mapInner T (innerStep ps st x) := by
  simp only [innerStep, mapInner]
  split <;> simp [mapInner, Array.map_push, hT.jump]

private theorem innerFold_map {T : VBlock → VBlock} (hT : BlockMap T)
    (ps : Array (Array Nat)) (xs : List (Nat × Label))
    (st : Nat × Array VBlock × Array Label) :
    xs.foldl (innerStep ps) (mapInner T st) = mapInner T (xs.foldl (innerStep ps) st) := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, innerStep_map hT, ih]

private theorem splitBody_map {T : VBlock → VBlock} (hT : BlockMap T)
    (ss ps : Array (Array Nat)) (x : VBlock × Nat) (st : Nat × Array VBlock × Array VBlock) :
    splitBody ss ps (Prod.map T id x) (mapSplit T st) =
      (splitBody ss ps x st).map (mapStep (mapSplit T)) := by
  rcases x with ⟨b, i⟩
  rcases st with ⟨next, B, E⟩
  simp only [splitBody, mapSplit, Prod.map, id_eq, hT.back]
  by_cases hs : (ss[i]! : Array Nat).size < 2
  · simp [hs, mapStep, mapSplit, Array.map_push, pure, Except.pure, Except.map]
  simp only [hs, ite_false]
  cases ht : b.insts.back? with
  | none => simp [throw, throwThe, MonadExceptOf.throw, Except.map]
  | some t =>
    simp only
    rw [← Array.forIn_toList, ← Array.forIn_toList]
    rw [forIn_yield_foldl _ _ (innerStep ps) _
      (fun a c => by simp only [innerStep]; split <;> rfl)]
    rw [forIn_yield_foldl _ _ (innerStep ps) _
      (fun a c => by simp only [innerStep]; split <;> rfl)]
    have heq := innerFold_map hT ps
      (((ss[i]! : Array Nat).zip t.targets.toArray).toList) (next, E, #[])
    simp only [mapInner, Array.map_empty] at heq
    rw [heq]
    simp only [pure, Except.pure, bind, Except.bind, mapInner]
    cases hr : t.setTargets
        ((((ss[i]! : Array Nat).zip t.targets.toArray).toList).foldl
          (innerStep ps) (next, E, #[])).2.2.toList with
    | none => simp [throw, throwThe, MonadExceptOf.throw, Except.map]
    | some t' => simp [mapStep, mapSplit, Array.map_push, hT.retarget b t t' _ ht hr, Except.map]

private theorem splitRun_map {T : VBlock → VBlock} (hT : BlockMap T)
    (vc : VCode) (ss ps : Array (Array Nat)) :
    splitRun (mapBlocks T vc) ss ps = (splitRun vc ss ps).map (mapSplit T) := by
  rw [splitRun_body, splitRun_body]
  simp only [mapBlocks, next0_map hT, Array.zipIdx_map,
    ← Array.forIn_toList, Array.toList_map]
  simpa only [mapSplit, Array.map_empty] using
    forIn_map_state (Prod.map T id) (mapSplit T) (splitBody ss ps) (splitBody ss ps)
      (splitBody_map hT ss ps) vc.blocks.zipIdx.toList (next0Of vc.blocks, #[], #[])

private theorem mapBlocks_keep (T : VBlock → VBlock) (vc : VCode) (live : Array Bool) :
    ({ mapBlocks T vc with blocks := keep (mapBlocks T vc).blocks live } : VCode) =
      mapBlocks T { vc with blocks := keep vc.blocks live } := by
  simp only [mapBlocks, keep_map]

private theorem prepare_map {T : VBlock → VBlock} (hT : BlockMap T) (vc : VCode) :
    prepare (mapBlocks T vc) = (prepare vc).map (mapBlocks T) := by
  rw [prepare_repr, prepare_repr]
  unfold prepareRepr
  simp only [mapBlocks_cfg hT]
  cases hc0 : vc.cfg with
  | error e => simp [bind, Except.bind, Except.map]
  | ok r =>
    rcases r with ⟨ss0, ps0⟩
    simp only [bind, Except.bind]
    rw [mapBlocks_keep]
    simp only [mapBlocks_cfg hT]
    cases hc1 : ({ vc with blocks := keep vc.blocks (reachable ss0) } : VCode).cfg with
    | error e => simp [Except.map]
    | ok r =>
      rcases r with ⟨ss1, ps1⟩
      simp only
      have hparams :
          ((keep (mapBlocks T vc).blocks (reachable ss0))[0]?.map fun b => b.params.isEmpty) =
            ((keep vc.blocks (reachable ss0))[0]?.map fun b => b.params.isEmpty) := by
        simp only [mapBlocks, keep_map, Array.getElem?_map, Option.map_map,
          Function.comp_def, hT.params]
      rw [hparams]
      by_cases hpred : (ps1[0]?.getD #[]).isEmpty = true
      · simp only [hpred, Bool.not_true, Bool.false_eq_true, ite_false]
        by_cases hparam :
            ((keep vc.blocks (reachable ss0))[0]?.map fun b => b.params.isEmpty).getD true = true
        · simp only [hparam, Bool.not_true, Bool.false_eq_true, ite_false]
          rw [splitRun_map hT]
          cases hr : splitRun { vc with blocks := keep vc.blocks (reachable ss0) } ss1 ps1 with
          | error e => simp [Except.map]
          | ok st =>
            rcases st with ⟨next, B, E⟩
            simp only [Except.map, mapSplit]
            have houter :
                ({ mapBlocks T vc with blocks := B.map T ++ E.map T } : VCode) =
                  mapBlocks T { vc with blocks := B ++ E } := by
              simp only [mapBlocks, Array.map_append]
            rw [houter, mapBlocks_cfg hT]
            cases hc2 : ({ vc with blocks := B ++ E } : VCode).cfg with
            | error e => simp [Except.map]
            | ok r =>
              rcases r with ⟨ss2, ps2⟩
              simp only [pure, Except.pure, Except.map]
              simp only [mapBlocks, Array.map_append, Array.map_map]
              congr 2
              congr 1
              funext i
              rw [← Array.map_append]
              simp only [Function.comp_def, getElem!_def, Array.getElem?_map]
              change ((B ++ E)[i]?.map T).getD default = T ((B ++ E)[i]?.getD default)
              rw [← hT.default, Option.getD_map]
              rw [hT.default]

        · rw [Bool.eq_false_iff.mpr hparam]; rfl
      · rw [Bool.eq_false_iff.mpr hpred]; rfl

private theorem retarget_facts {t t' : MInst} {ls : List Label}
    (h : t.setTargets ls = some t') :
    t.isTerminator = true ∧ t'.isTerminator = true ∧
      pureForm t = false ∧ pureForm t' = false ∧ t'.operands = t.operands := by
  unfold MInst.setTargets at h
  split at h
  all_goals (try split at h)
  all_goals (cases h)
  all_goals (try exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
  all_goals simp only [MInst.isTerminator, MInst.isBranch, MInst.isRet, pureForm,
    Backend.Proof.operands_tryCall_call]
  all_goals simp [MInst.operands, MInst.visitOperands]

private theorem scan_append_term (n : Nat) (L : List Nat) (xs : List MInst) (t : MInst)
    (ht : pureForm t = false) :
    scan n (xs ++ [t]) L =
      let r := scan n xs (uses n t ++ L.filter fun v => !(defs t).contains v)
      (r.1 ++ [t], r.2) := by
  induction xs with
  | nil => simp [scan, discard, ht]
  | cons i xs ih =>
    simp only [List.cons_append, scan, ih]
    split <;> rfl

private def eraseBlock (n : Nat) (L : List Nat) (b : VBlock) : VBlock :=
  if (b.insts.back?.map MInst.isTerminator).getD false then
    { b with insts := (scan n b.insts.toList L).1.toArray }
  else b

private theorem eraseBlock_back (n : Nat) (L : List Nat) (b : VBlock) :
    (eraseBlock n L b).insts.back? = b.insts.back? := by
  cases ht : b.insts.back? with
  | none => simp [eraseBlock, ht]
  | some t =>
    cases hterm : t.isTerminator with
    | false => simp [eraseBlock, ht, hterm]
    | true =>
      have hnt : pureForm t = false := by
        cases hp : pureForm t
        · rfl
        · have hf := pureForm_notTerminator hp; simp_all
      have ht' : b.insts.toList.getLast? = some t := by simpa using ht
      obtain ⟨xs, hx⟩ := List.getLast?_eq_some_iff.mp ht'
      simpa [eraseBlock, ht, hterm, hx] using scan_last n xs t L hnt

private theorem eraseBlock_map (n : Nat) (L : List Nat) : BlockMap (eraseBlock n L) := by
  refine ⟨rfl, ?_, ?_, ?_, eraseBlock_back n L, ?_, ?_⟩
  · intro b; unfold eraseBlock; split <;> rfl
  · intro b; unfold eraseBlock; split <;> rfl
  · intro b; unfold eraseBlock; split <;> rfl
  · intro lab l
    simp [eraseBlock, scan, discard, pureForm, MInst.isTerminator, MInst.isBranch, MInst.isRet]
  · intro b t t' ls ht hr
    obtain ⟨hterm, hterm', hnt, hnt', hops⟩ := retarget_facts hr
    have hu : uses n t' = uses n t := by simp only [uses, hops]
    have hd : defs t' = defs t := by simp only [defs, hops]
    have hb : b.insts.toList.getLast? = some t := by simpa using ht
    obtain ⟨xs, hx⟩ := List.getLast?_eq_some_iff.mp hb
    have hl : b.insts.toList ≠ [] := by rw [hx]; simp
    simp only [eraseBlock, ht, Option.map_some, hterm, Option.getD_some,
      ite_true, Array.back?_push, hterm']
    simp only [Array.toList_push, Array.toList_pop, hx, List.dropLast_append_cons,
      List.dropLast_nil, List.append_nil, scan_append_term n L xs t hnt,
      scan_append_term n L xs t' hnt', hu, hd]
    congr 1
    apply Array.toList_inj.mp
    simp [Array.toList_push, Array.toList_pop, scan_append_term, hnt', hu, hd]

/-- Apply the original liveness boundary to a prepared block. -/
def preparedCleanupBlock (original : VCode) (b : VBlock) : VBlock :=
  eraseBlock original.classes.size (exitLive original 0 default) b

/-- All block interfaces and the surviving terminator agree with preparation's
original output. -/
theorem preparedCleanupBlock_interface (vc : VCode) (b : VBlock) :
    (preparedCleanupBlock vc b).label = b.label ∧
    (preparedCleanupBlock vc b).params = b.params ∧
    (preparedCleanupBlock vc b).branchArgs = b.branchArgs ∧
    (preparedCleanupBlock vc b).insts.back? = b.insts.back? := by
  have h := eraseBlock_map vc.classes.size (exitLive vc 0 default)
  exact ⟨h.label b, h.params b, h.branchArgs b, h.back b⟩

/-- Transported cleanup can only delete instructions. -/
theorem preparedCleanupBlock_sublist (vc : VCode) (b : VBlock) :
    (preparedCleanupBlock vc b).insts.toList.Sublist b.insts.toList := by
  unfold preparedCleanupBlock eraseBlock
  split
  · simpa using scan_sublist vc.classes.size b.insts.toList (exitLive vc 0 default)
  · exact List.Sublist.refl _

/-- Cleanup transported across preparation, using the original liveness boundary
and preserving the prepared CFG's labels and interfaces. -/
def preparedCleanup (original prepared : VCode) : VCode :=
  mapBlocks (preparedCleanupBlock original) prepared

theorem preparedCleanup_blocks (vc vcp : VCode) :
    (preparedCleanup vc vcp).blocks = vcp.blocks.map (preparedCleanupBlock vc) := rfl

/-- Preparation commutes with cleanup: it makes the same CFG decisions and
retargets the same surviving terminators, including newly added edge blocks. -/
theorem prune_prepare (vc : VCode) :
    prepare (prune vc) = (prepare vc).map (preparedCleanup vc) := by
  cases hc : vc.cfg with
  | error e => simp [prune, hc, prepare, bind, Except.bind, Except.map]
  | ok r =>
    rcases r with ⟨ss, ps⟩
    have heq : clean vc = mapBlocks
        (eraseBlock vc.classes.size (exitLive vc 0 default)) vc := by
      change { vc with blocks := (clean vc).blocks } = _
      rw [clean_blocks_map]
      unfold mapBlocks
      congr 1
      apply Array.toList_inj.mp
      simp only [Array.toList_map]
      apply List.map_congr_left
      intro vb hvb
      obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hvb
      rw [Array.getElem?_toList] at hb
      obtain ⟨t, ts, ht, hterm, _⟩ := (cfg_spec hc).blk b vb hb
      simp [cleanBlock, eraseBlock, ht, hterm, exitLive]
    simp only [prune, hc]
    rw [heq]
    exact prepare_map (eraseBlock_map _ _) vc

/-- The same successful preparation has a cleaned counterpart, with no new
source or successful-preparation premise. -/
theorem prune_prepare_ok {vc vcp : VCode} (hp : prepare vc = .ok vcp) :
    prepare (prune vc) = .ok (preparedCleanup vc vcp) := by
  rw [prune_prepare, hp]
  rfl

/-- No function metadata changes while transporting cleanup across preparation. -/
theorem preparedCleanup_metadata (vc vcp : VCode) :
    (preparedCleanup vc vcp).name = vcp.name ∧
    (preparedCleanup vc vcp).classes = vcp.classes ∧
    (preparedCleanup vc vcp).slotBytes = vcp.slotBytes ∧
    (preparedCleanup vc vcp).outgoing = vcp.outgoing ∧
    (preparedCleanup vc vcp).rulesFired = vcp.rulesFired ∧
    (preparedCleanup vc vcp).blocks.size = vcp.blocks.size := by
  simp [preparedCleanup, mapBlocks]

/-- Prepared instruction predicates survive because each block's code is a sublist. -/
theorem preparedCleanup_insts (vc vcp : VCode) {P : MInst → Prop}
    (h : ∀ vb ∈ vcp.blocks.toList, ∀ i ∈ vb.insts.toList, P i) :
    ∀ vb ∈ (preparedCleanup vc vcp).blocks.toList, ∀ i ∈ vb.insts.toList, P i := by
  intro vb hvb i hi
  simp only [preparedCleanup, mapBlocks, Array.toList_map, List.mem_map] at hvb
  obtain ⟨raw, hraw, rfl⟩ := hvb
  unfold preparedCleanupBlock eraseBlock at hi
  split at hi
  · apply h raw hraw i
    apply (scan_sublist _ _ _).subset
    simpa using hi
  · exact h raw hraw i hi

/-! Joint non-vacuity: an actual redundant producer is removed from prepared
code, and the unconditional preparation-correspondence theorem applies to it. -/
example : ∃ vc : VCode,
    (preparedCleanup vc vc).blocks[0]!.insts.toList = [liveBic, liveReturn] ∧
    prepare (prune vc) = (prepare vc).map (preparedCleanup vc) := by
  let vc : VCode := ⟨"cleanup_prepared", #[⟨0, #[deadMvn, liveBic, liveReturn], #[], #[]⟩],
    #[.int, .int, .int, .int], 0, 0, #[]⟩
  refine ⟨vc, ?_, prune_prepare vc⟩
  simp only [preparedCleanup, mapBlocks, vc, Array.map_singleton]
  simp [preparedCleanupBlock, eraseBlock, liveReturn, MInst.isTerminator, MInst.isBranch, MInst.isRet]
  decide

end Backend.DeadCleanup
