import FV.E2E.EmitSize
import FV.Backend.Proof.DeadCleanupStructure

namespace E2E
open Backend

private theorem slot_moves_words {α : Type} (vb : VBlock) (F : α → RItem)
    (hF : ∀ x, itemWords vb (F x) = 10) (xs : List α) :
    ((xs.map F).map (itemWords vb)).sum = 10 * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, hF, ih]; omega

/-- Moving an instruction to a new index and changing spill-home numbering
does not change its contribution to the fallback allocator's code-size bound. -/
theorem spillInst_words_eq (h h' : Homes) (k k' : Nat) (i : MInst) (vb vb' : VBlock)
    (hk : vb.insts[k]? = some i) (hk' : vb'.insts[k']? = some i) :
    ((spillInst h k i).map (itemWords vb)).sum =
      ((spillInst h' k' i).map (itemWords vb')).sum := by
  unfold spillInst
  split
  · simp [itemWords, hk, hk']
  · rename_i ops hops
    have hL (home : Homes) (block : VBlock) :
        ((((ops.zip (spillLocs ops i.clobbers)).toList.filter (·.1.kind == .use)).map
          fun (o, l) => RItem.move (spillHome home o.vreg o.cls) l).map (itemWords block)).sum =
        10 * ((ops.zip (spillLocs ops i.clobbers)).toList.filter (·.1.kind == .use)).length :=
      slot_moves_words block _ (fun x => by simp [itemWords, spillHome, moveWords]) _
    have hS (home : Homes) (block : VBlock) :
        (((keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList).map
          fun (o, l) => RItem.move l (spillHome home o.vreg o.cls)).map (itemWords block)).sum =
        10 * (keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList).length :=
      slot_moves_words block _ (fun x => by cases x.2 <;> simp [itemWords, spillHome, moveWords]) _
    have hR : ∀ block : VBlock,
        (spillRestores.map (itemWords block)).sum = 10 * calleeSaved.length := by
      intro block
      exact slot_moves_words block _ (fun r => by simp [itemWords, moveWords]) calleeSaved
    have hS' : ((if i.isTerminator then [] else
        (keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList).map
          fun (o, l) => RItem.move l (spillHome h o.vreg o.cls)).map (itemWords vb)).sum =
        ((if i.isTerminator then [] else
        (keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList).map
          fun (o, l) => RItem.move l (spillHome h' o.vreg o.cls)).map (itemWords vb')).sum := by
      by_cases ht : i.isTerminator = true
      · simp only [if_pos ht, List.map_nil, List.sum_nil]
      · simp only [if_neg ht]
        rw [hS h vb, hS h' vb']
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, itemWords, hk, hk', hL, hS']
    cases i <;> simp only [hR, List.map_nil, List.sum_nil]

/-- Exact instruction contribution, independent of its position and spill slots. -/
def spillInstWords (i : MInst) : Nat :=
  ((spillInst {} 0 i).map (itemWords { label := 0, insts := #[i] })).sum

theorem spillInst_words (h : Homes) (k : Nat) (i : MInst) (vb : VBlock)
    (hk : vb.insts[k]? = some i) :
    ((spillInst h k i).map (itemWords vb)).sum = spillInstWords i :=
  spillInst_words_eq h {} k 0 i vb { label := 0, insts := #[i] } hk (by simp)

private theorem words_flatMap {α β : Type} (xs : List α) (F : α → List β) (w : β → Nat) :
    ((xs.flatMap F).map w).sum = (xs.map fun x => ((F x).map w).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

/-- Instruction-body contribution is just a sum over the unallocated code. -/
theorem spillBody_words (h : Homes) (vb : VBlock) :
    (((vb.insts.toList.zipIdx).flatMap fun (i, k) => spillInst h k i).map
      (itemWords vb)).sum = (vb.insts.toList.map spillInstWords).sum := by
  rw [words_flatMap]
  have he : ((vb.insts.toList.zipIdx).map fun (i, k) =>
      ((spillInst h k i).map (itemWords vb)).sum) =
      (vb.insts.toList.zipIdx).map (fun p => spillInstWords p.1) := by
    apply List.map_congr_left
    intro p hp
    obtain ⟨i, k⟩ := p
    obtain ⟨_, hk, hi⟩ := List.mem_zipIdx hp
    have hk' : vb.insts[k]? = some i := by
      simp only [Nat.zero_add, Array.length_toList] at hk
      rw [hi]
      simp only [Nat.sub_zero, Array.getElem_toList]
      exact Array.getElem?_eq_getElem hk
    exact spillInst_words h k i vb hk'
  rw [he]
  congr 1
  simpa only [List.map_map, Function.comp_def] using congrArg (List.map spillInstWords)
    (List.zipIdx_map_fst 0 vb.insts.toList)

/-- Deleting instructions cannot increase the body contribution. -/
theorem spillBody_words_mono (h h' : Homes) {vb vb' : VBlock}
    (hs : vb'.insts.toList.Sublist vb.insts.toList) :
    (((vb'.insts.toList.zipIdx).flatMap fun (i, k) => spillInst h' k i).map
      (itemWords vb')).sum ≤
    (((vb.insts.toList.zipIdx).flatMap fun (i, k) => spillInst h k i).map
      (itemWords vb)).sum := by
  rw [spillBody_words, spillBody_words]
  have sum_sublist {xs ys : List MInst} (h : xs.Sublist ys) :
      (xs.map spillInstWords).sum ≤ (ys.map spillInstWords).sum := by
    induction h with
    | slnil => simp
    | cons h ih => simp only [List.map_cons, List.sum_cons]; omega
    | cons_cons h ih => simp only [List.map_cons, List.sum_cons]; omega
  exact sum_sublist hs

/-- Edge-copy size depends only on the block interfaces, not on homes or code. -/
theorem spillArgMoves_words (h : Homes) (vb tb w : VBlock) :
    ((spillArgMoves h vb tb).map (itemWords w)).sum =
      40 * (vb.branchArgs.toList.zip tb.params.toList).length := by
  simp only [spillArgMoves, List.map_append, List.sum_append, words_flatMap]
  have phase (xs : List ((Reg × Reg) × Nat)) (F : ((Reg × Reg) × Nat) → List RItem)
      (hF : ∀ x, ((F x).map (itemWords w)).sum = 20) :
      (xs.map fun x => ((F x).map (itemWords w)).sum).sum = 20 * xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, hF] at ih ⊢; omega
  rw [phase _ _ (fun x => by simp [itemWords, spillHome, moveWords]),
    phase _ _ (fun x => by simp [itemWords, spillHome, moveWords])]
  simp only [List.length_zipIdx]
  omega

private theorem last_cost {α : Type} (xs : List α) (s c : Nat) :
    ((xs.zipIdx s).map fun p => if p.2 + 1 == s + xs.length then c else 0).sum =
      if xs.isEmpty then 0 else c := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, List.length_cons,
      List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    have hn : s + (xs.length + 1) = (s + 1) + xs.length := by omega
    simp only [hn, ih (s + 1)]
    cases xs with
    | nil => simp
    | cons y ys =>
      have hne : ¬s + 1 = s + 1 + (y :: ys).length := by simp
      simp [hne]

/-- The allocator inserts the same edge-copy contribution once, before the
last instruction; the other contribution is the instruction-body sum. -/
theorem spillBody_with_moves_words (h : Homes) (vb : VBlock) (moves : List RItem) :
    (((vb.insts.toList.zipIdx).flatMap fun (i, k) =>
      (if k + 1 == vb.insts.size then moves else []) ++ spillInst h k i).map
      (itemWords vb)).sum = (vb.insts.toList.map spillInstWords).sum +
      if vb.insts.isEmpty then 0 else (moves.map (itemWords vb)).sum := by
  rw [words_flatMap]
  have he : ((vb.insts.toList.zipIdx).map fun (i, k) =>
      (((if k + 1 == vb.insts.size then moves else []) ++ spillInst h k i).map
        (itemWords vb)).sum) =
      (vb.insts.toList.zipIdx).map (fun p =>
        (if p.2 + 1 == vb.insts.size then (moves.map (itemWords vb)).sum else 0) +
          spillInstWords p.1) := by
    apply List.map_congr_left
    intro p hp
    obtain ⟨i, k⟩ := p
    obtain ⟨_, hk, hi⟩ := List.mem_zipIdx hp
    have hk' : vb.insts[k]? = some i := by
      simp only [Nat.zero_add, Array.length_toList] at hk
      rw [hi]
      simp only [Nat.sub_zero, Array.getElem_toList]
      exact Array.getElem?_eq_getElem hk
    dsimp only
    rw [List.map_append, List.sum_append, spillInst_words h k i vb hk']
    split <;> simp
  have sum_add {α : Type} (xs : List α) (f g : α → Nat) :
      (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega
  rw [he, sum_add]
  have hlast := last_cost vb.insts.toList 0 (moves.map (itemWords vb)).sum
  simp only [Nat.zero_add, Array.length_toList, Array.isEmpty_toList] at hlast
  rw [hlast]
  have hb : ((vb.insts.toList.zipIdx).map (fun p => spillInstWords p.1)).sum =
      (vb.insts.toList.map spillInstWords).sum := by
    congr 1
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map spillInstWords)
      (List.zipIdx_map_fst 0 vb.insts.toList)
  rw [hb]
  omega

/-- Entry-store size depends only on the predecessor's terminator operands. -/
theorem spillEntryStores_words_eq (h h' : Homes) (vc vc' : VCode)
    (succs preds : Array (Array Nat)) (s : Nat) (w w' : VBlock)
    (hb : ∀ b : Nat, (vc.blocks[b]?.map (fun (vb : VBlock) => vb.insts.back?)) =
      (vc'.blocks[b]?.map (fun (vb : VBlock) => vb.insts.back?))) :
    ((spillEntryStores h vc succs preds s).map (itemWords w)).sum =
      ((spillEntryStores h' vc' succs preds s).map (itemWords w')).sum := by
  unfold spillEntryStores
  rcases preds[s]? with _ | ⟨_ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rfl
  · rfl
  · change ((match vc.blocks[b]?, succs[b]? with
      | some vb, some ss => match ss.toList.idxOf? s with
        | some j => (termEdgeDefs vb j).map fun ((o, l) : Operand × Loc) => RItem.move l (spillHome h o.vreg o.cls)
        | none => []
      | _, _ => []).map (itemWords w)).sum =
      ((match vc'.blocks[b]?, succs[b]? with
      | some vb, some ss => match ss.toList.idxOf? s with
        | some j => (termEdgeDefs vb j).map fun ((o, l) : Operand × Loc) =>
            RItem.move l (spillHome h' o.vreg o.cls)
        | none => []
      | _, _ => []).map (itemWords w')).sum
    have ht := hb b
    cases hv : vc.blocks[b]? <;> cases hv' : vc'.blocks[b]? <;>
      simp only [hv, hv', Option.map_none, Option.map_some] at ht ⊢
    · rfl
    · cases ht
    · cases ht
    · rename_i vb vb'
      have he : ∀ j, termEdgeDefs vb j = termEdgeDefs vb' j := by
        intro j
        simp only [termEdgeDefs, Option.some.injEq] at ht ⊢
        rw [ht]
      cases succs[b]? with
      | none => rfl
      | some ss =>
        dsimp only
        cases hi : ss.toList.idxOf? s with
        | none => rfl
        | some j =>
          rw [slot_moves_words w _ (fun (x : Operand × Loc) => by cases x.2 <;> simp [itemWords, spillHome, moveWords]),
            slot_moves_words w' _ (fun (x : Operand × Loc) => by cases x.2 <;> simp [itemWords, spillHome, moveWords]), he]
  · rfl

/-- One block of the existing fallback allocator, factored without changing it. -/
def spillBlockItems (h : Homes) (vc : VCode) (succs preds : Array (Array Nat))
    (bi : Nat) (vb : VBlock) : List RItem :=
  let n := vb.insts.size
  let body := (vb.insts.toList.zipIdx).flatMap fun (i, k) =>
    let moves := if k + 1 == n && !vb.branchArgs.isEmpty then
      match succs[bi]? with
      | some #[t] => match vc.blocks[t]? with
        | some tb => spillArgMoves h vb tb
        | none => []
      | _ => []
      else []
    moves ++ spillInst h k i
  let pre := (if bi == 0 then spillSaves else []) ++ spillEntryStores h vc succs preds bi
  pre ++ body

theorem spillAlloc_block {vc : VCode} {succs preds : Array (Array Nat)}
    (hc : vc.cfg = .ok (succs, preds)) {bi : Nat} {vb : VBlock}
    (hb : vc.blocks[bi]? = some vb) :
    (spillAlloc vc).blocks[bi]? =
      some (spillBlockItems (spillHomes vc) vc succs preds bi vb).toArray := by
  unfold spillAlloc
  rw [hc]
  change (Array.mapIdx _ vc.blocks)[bi]? = _
  rw [Array.getElem?_mapIdx, hb, Option.map_some]
  rfl

def spillEdgeMoves (h : Homes) (vc : VCode) (succs : Array (Array Nat))
    (bi : Nat) (vb : VBlock) : List RItem :=
  if !vb.branchArgs.isEmpty then
    match succs[bi]? with
    | some #[t] => match vc.blocks[t]? with
      | some tb => spillArgMoves h vb tb
      | none => []
    | _ => []
  else []

theorem spillBlock_words (h : Homes) (vc : VCode) (succs preds : Array (Array Nat))
    (bi : Nat) (vb : VBlock) :
    ((spillBlockItems h vc succs preds bi vb).map (itemWords vb)).sum =
      (((if bi == 0 then spillSaves else []) ++ spillEntryStores h vc succs preds bi).map
        (itemWords vb)).sum + (vb.insts.toList.map spillInstWords).sum +
      if vb.insts.isEmpty then 0 else (spillEdgeMoves h vc succs bi vb |>.map (itemWords vb)).sum := by
  have he : ((vb.insts.toList.zipIdx).flatMap fun (i, k) =>
      (if k + 1 == vb.insts.size && !vb.branchArgs.isEmpty then
        match succs[bi]? with
        | some #[t] => match vc.blocks[t]? with
          | some tb => spillArgMoves h vb tb
          | none => []
        | _ => []
      else []) ++ spillInst h k i) =
      (vb.insts.toList.zipIdx).flatMap (fun (i, k) =>
        (if k + 1 == vb.insts.size then spillEdgeMoves h vc succs bi vb else []) ++
          spillInst h k i) := by
    apply congrArg (fun F : MInst × Nat → List RItem => vb.insts.toList.zipIdx.flatMap F)
    funext p
    obtain ⟨i, k⟩ := p
    have norm (a b : Bool) (xs : List RItem) :
        (if a && b then xs else []) = (if a then (if b then xs else []) else []) := by
      cases a <;> cases b <;> rfl
    exact congrArg (fun xs => xs ++ spillInst h k i)
      (norm (k + 1 == vb.insts.size) (!vb.branchArgs.isEmpty)
        (match succs[bi]? with
        | some #[t] => match vc.blocks[t]? with
          | some tb => spillArgMoves h vb tb
          | none => []
        | _ => []))

  unfold spillBlockItems
  rw [List.map_append, List.sum_append, he, spillBody_with_moves_words]
  omega

theorem spillEdgeMoves_words_eq (h h' : Homes) (vc vc' : VCode)
    (succs : Array (Array Nat)) (bi : Nat) (vb vb' : VBlock)
    (ha : vb.branchArgs = vb'.branchArgs)
    (hp : ∀ b : Nat, (vc.blocks[b]?.map VBlock.params) = (vc'.blocks[b]?.map VBlock.params)) :
    ((spillEdgeMoves h vc succs bi vb).map (itemWords vb)).sum =
      ((spillEdgeMoves h' vc' succs bi vb').map (itemWords vb')).sum := by
  unfold spillEdgeMoves
  rw [ha]
  by_cases he : (!vb'.branchArgs.isEmpty) = true
  · rw [if_pos he, if_pos he]
    rcases succs[bi]? with _ | ⟨_ | ⟨t, _ | ⟨u, us⟩⟩⟩
    · rfl
    · rfl
    · change ((match vc.blocks[t]? with
        | some tb => spillArgMoves h vb tb
        | none => []).map (itemWords vb)).sum =
        ((match vc'.blocks[t]? with
        | some tb => spillArgMoves h' vb' tb
        | none => []).map (itemWords vb')).sum
      have ht := hp t
      cases hv : vc.blocks[t]? <;> cases hv' : vc'.blocks[t]? <;>
        simp only [hv, hv', Option.map_none, Option.map_some] at ht ⊢
      · rfl
      · cases ht
      · cases ht
      · rw [spillArgMoves_words, spillArgMoves_words, ha, Option.some.inj ht]
    · rfl
  · rw [if_neg he, if_neg he]
    rfl

/-- Exact per-block monotonicity for an instruction-deleting transformation
that preserves terminators and interfaces. -/
theorem spillBlock_words_mono (h h' : Homes) (vc vc' : VCode)
    (succs preds : Array (Array Nat)) (bi : Nat) (vb vb' : VBlock)
    (ha : vb.branchArgs = vb'.branchArgs) (hb : vb.insts.back? = vb'.insts.back?)
    (hs : vb'.insts.toList.Sublist vb.insts.toList)
    (hp : ∀ b : Nat, (vc.blocks[b]?.map VBlock.params) = (vc'.blocks[b]?.map VBlock.params))
    (ht : ∀ b : Nat, (vc.blocks[b]?.map (fun (vb : VBlock) => vb.insts.back?)) =
      (vc'.blocks[b]?.map (fun (vb : VBlock) => vb.insts.back?))) :
    ((spillBlockItems h' vc' succs preds bi vb').map (itemWords vb')).sum ≤
      ((spillBlockItems h vc succs preds bi vb).map (itemWords vb)).sum := by
  have hsave (block : VBlock) :
      (spillSaves.map (itemWords block)).sum = 10 * calleeSaved.length :=
    slot_moves_words block _ (fun r => by simp [itemWords, moveWords]) calleeSaved
  have hpre : (((if bi == 0 then spillSaves else []) ++
      spillEntryStores h vc succs preds bi).map (itemWords vb)).sum =
      (((if bi == 0 then spillSaves else []) ++
      spillEntryStores h' vc' succs preds bi).map (itemWords vb')).sum := by
    rw [List.map_append, List.sum_append, List.map_append, List.sum_append,
      spillEntryStores_words_eq h h' vc vc' succs preds bi vb vb' ht]
    by_cases hi : (bi == 0) = true
    · simp only [if_pos hi, hsave]
    · simp only [if_neg hi, List.map_nil, List.sum_nil]
  have hempty : vb.insts.isEmpty = vb'.insts.isEmpty := by
    apply Bool.eq_iff_iff.mpr
    simp only [Array.isEmpty_iff, ← Array.back?_eq_none_iff, hb]
  have hedges := spillEdgeMoves_words_eq h h' vc vc' succs bi vb vb' ha hp
  have hbody := spillBody_words_mono h h' hs
  rw [spillBody_words, spillBody_words] at hbody
  rw [spillBlock_words, spillBlock_words, hpre, hempty, hedges]
  omega

/-- The baseline's exact spill-size bound survives deletion across all blocks.
No larger source bound or additional size certificate is required. -/
theorem spillWordBound_map_mono (vc vc' : VCode) (T : VBlock → VBlock)
    (hmap : vc'.blocks = vc.blocks.map T)
    (hargs : ∀ b, (T b).branchArgs = b.branchArgs)
    (hparams : ∀ b, (T b).params = b.params)
    (hback : ∀ b, (T b).insts.back? = b.insts.back?)
    (hsub : ∀ b, (T b).insts.toList.Sublist b.insts.toList)
    {succs preds : Array (Array Nat)}
    (hc : vc.cfg = .ok (succs, preds)) (hc' : vc'.cfg = .ok (succs, preds)) :
    spillWordBound vc' ≤ spillWordBound vc := by
  have hsz (v : VCode) : (spillAlloc v).blocks.size = v.blocks.size := by
    unfold spillAlloc
    rcases v.cfg with _ | ⟨s, p⟩ <;> exact Array.size_mapIdx
  have hps : ∀ b : Nat, (vc.blocks[b]?.map VBlock.params) =
      (vc'.blocks[b]?.map VBlock.params) := by
    intro b
    simp only [hmap, Array.getElem?_map, Option.map_map]
    cases vc.blocks[b]? <;> simp [hparams]
  have hts : ∀ b : Nat, (vc.blocks[b]?.map (fun (vb : VBlock) => vb.insts.back?)) =
      (vc'.blocks[b]?.map (fun (vb : VBlock) => vb.insts.back?)) := by
    intro b
    simp only [hmap, Array.getElem?_map, Option.map_map]
    cases vc.blocks[b]? <;> simp [hback]
  unfold spillWordBound rfWords
  apply sum_map_le_of_getElem?
  · simp [hsz, hmap]
  · intro bi x y hx hy
    obtain ⟨vb', items'⟩ := x
    obtain ⟨vb, items⟩ := y
    rw [Array.getElem?_toList, Array.getElem?_zip_eq_some] at hx hy
    obtain ⟨hvb', hitems'⟩ := hx
    obtain ⟨hvb, hitems⟩ := hy
    dsimp only at hvb' hitems' hvb hitems ⊢
    have he : vb' = T vb := by
      rw [hmap, Array.getElem?_map, hvb, Option.map_some] at hvb'
      exact (Option.some.inj hvb').symm
    subst vb'
    rw [spillAlloc_block hc hvb] at hitems
    rw [spillAlloc_block hc' hvb'] at hitems'
    obtain rfl := Option.some.inj hitems
    obtain rfl := Option.some.inj hitems'
    simp only [List.toList_toArray]
    exact Nat.add_le_add_left (spillBlock_words_mono (spillHomes vc) (spillHomes vc')
      vc vc' succs preds bi vb (T vb) (hargs vb).symm (hback vb).symm (hsub vb) hps hts) 7

/-! Joint non-vacuity with an actual deleted integer producer. The same concrete
blocks instantiate the instruction-body and full per-block inequalities. -/
example : ∃ vb vb' : VBlock,
    vb.insts.size = 3 ∧ vb'.insts.size = 2 ∧
    vb.branchArgs = vb'.branchArgs ∧ vb.insts.back? = vb'.insts.back? ∧
    vb'.insts.toList.Sublist vb.insts.toList ∧
    ((spillBlockItems {} ⟨"size_witness", #[vb], #[.int, .int, .int, .int], 0, 0, #[]⟩ #[#[]] #[#[]] 0 vb').map
      (itemWords vb')).sum ≤
    ((spillBlockItems {} ⟨"size_witness", #[vb], #[.int, .int, .int, .int], 0, 0, #[]⟩ #[#[]] #[#[]] 0 vb).map
      (itemWords vb)).sum := by
  let vb : VBlock := ⟨0, #[DeadCleanup.deadMvn, DeadCleanup.liveBic, DeadCleanup.liveReturn], #[], #[]⟩
  let vb' : VBlock := ⟨0, #[DeadCleanup.liveBic, DeadCleanup.liveReturn], #[], #[]⟩
  have ha : vb.branchArgs = vb'.branchArgs := rfl
  have hb : vb.insts.back? = vb'.insts.back? := rfl
  have hs : vb'.insts.toList.Sublist vb.insts.toList := by decide
  refine ⟨vb, vb', rfl, rfl, ha, hb, hs, ?_⟩
  exact spillBlock_words_mono {} {} _ _ #[#[]] #[#[]] 0 vb vb' ha hb hs
    (fun _ => rfl) (fun _ => rfl)

end E2E
