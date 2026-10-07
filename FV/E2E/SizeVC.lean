import FV.E2E.SizeDefs
import FV.Backend.Proof.PrepareComplete

/-!
# The spill allocation's words from the VCode measures (V6c)

`spillWordBound vcp` (`EmitSize`) bounds the words of the spill allocation's code of the prepared
VCode item by item. This file bounds it by the VCode measure `vcW` (`SizeDefs`), and `vcW` of the
prepared VCode by that of `prepare`'s input:

* `spillWordBound_le`: per block, the prologue (7), the callee-saved saves of the entry block
  (`restW`), the entry stores of the unique predecessor's terminator defs (at most its operands,
  `10` words each: `10 · maxRC`), the branch arguments' parallel copy (`4` slot moves per
  argument), and per instruction `spillInst`'s items: the restores before a `Rets` (`restW`), a
  load or store per operand (`10` words, at most `MInst.operands` of them, `operands_size_le`:
  at most `regCount`) and the instruction (`instWords = szWords`); all within `szInstW`.
* `maxRC_prepare`, `vcW_prepare`: `prepare` keeps blocks (retargeting a terminator keeps its
  weight, `setTargets_w`), adds edge blocks (one `jump`, weight `jumpBW`), at most one per
  branch target of a kept block (`prepare_w`: the splitting loop, step by step), and reorders the
  blocks by `rpo` (each index once, `sum_nodup_le`).
-/

namespace E2E

open Backend Backend.Proof.Cov

/-! ## Sums -/

theorem sum_map_add' {α : Type} (l : List α) (f g : α → Nat) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_mul' {α : Type} (l : List α) (c : Nat) (f : α → Nat) :
    (l.map fun x => c * f x).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem sum_map_le' {α : Type} {f g : α → Nat} :
    ∀ {l : List α}, (∀ x ∈ l, f x ≤ g x) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    have := h a (by simp)
    have := sum_map_le' (l := l) (fun x hx => h x (by simp [hx]))
    omega

theorem sum_map_const_le {α : Type} {f : α → Nat} {c : Nat} :
    ∀ {l : List α}, (∀ x ∈ l, f x ≤ c) → (l.map f).sum ≤ c * l.length
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    have := h a (by simp)
    have := sum_map_const_le (l := l) (fun x hx => h x (by simp [hx]))
    omega

theorem sum_flatMap_le {α β : Type} {G : α → List β} {w : β → Nat} {c : Nat} :
    ∀ {l : List α}, (∀ x ∈ l, ((G x).map w).sum ≤ c) → ((l.flatMap G).map w).sum ≤ c * l.length
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.length_cons, Nat.mul_add,
      Nat.mul_one]
    have := h a (by simp)
    have := sum_flatMap_le (l := l) (fun x hx => h x (by simp [hx]))
    omega

theorem sum_flatMap {α β : Type} (G : α → List β) (w : β → Nat) :
    ∀ l : List α, ((l.flatMap G).map w).sum = (l.map fun x => ((G x).map w).sum).sum
  | [] => by simp
  | a :: l => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      sum_flatMap G w l]

theorem sum_sublist_le {α : Type} (f : α → Nat) {l1 l2 : List α} (h : l1.Sublist l2) :
    (l1.map f).sum ≤ (l2.map f).sum := by
  induction h with
  | slnil => simp
  | cons a _ ih => simp only [List.map_cons, List.sum_cons]; omega
  | cons_cons a _ ih => simp only [List.map_cons, List.sum_cons]; omega

/-- **A sum over distinct indices** is at most the sum over any list containing them. -/
theorem sum_nodup_le (g : Nat → Nat) :
    ∀ {R S : List Nat}, R.Nodup → (∀ x ∈ R, x ∈ S) → (R.map g).sum ≤ (S.map g).sum
  | [], _, _, _ => by simp
  | a :: R, S, hn, hs => by
    obtain ⟨ha, hn'⟩ := List.nodup_cons.mp hn
    have hp := List.perm_cons_erase (hs a (by simp))
    have hsub : ∀ x ∈ R, x ∈ S.erase a := fun x hx =>
      (List.mem_erase_of_ne (fun e => ha (by subst e; exact hx))).mpr (hs x (by simp [hx]))
    have := sum_nodup_le g hn' hsub
    rw [(hp.map g).sum_nat]
    simp only [List.map_cons, List.sum_cons]
    omega

/-- At most one index `k` has `k + 1 = n`: a per-position bound with that one exception. -/
theorem sum_zipIdx_le {α : Type} (F : α × Nat → Nat) (B : α → Nat) (n c : Nat) :
    ∀ (L : List α) (s : Nat), (∀ p ∈ L.zipIdx s, F p ≤ (if p.2 + 1 = n then c else 0) + B p.1) →
      ((L.zipIdx s).map F).sum ≤ (if s + 1 ≤ n then c else 0) + (L.map B).sum
  | [], _, _ => by simp
  | a :: L, s, h => by
    rw [List.zipIdx_cons] at h ⊢
    have h1 := h (a, s) (by simp)
    have h2 := sum_zipIdx_le F B n c L (s + 1) (fun p hp => h p (by simp [hp]))
    simp only [List.map_cons, List.sum_cons] at h1 h2 ⊢
    split at h1 <;> split at h2 <;> split <;> omega

/-! ## Weights of one instruction -/

theorem instWords_eq (m : MInst) : instWords m = szWords m := by cases m <;> rfl

theorem szWords_le (m : MInst) : instWords m ≤ szInstW m := by
  rw [instWords_eq]; unfold szInstW; omega

/-! ### Operands (`MInst.operands`): at most `regCount` -/

/-- The operand collector of `MInst.operands`. -/
def collectR (s : OpSpec) (r : Reg) : StateT (Array Operand) (Except String) Reg := do
  match r with
  | .vreg n cls => modify (·.push ⟨n, cls, s.kind, s.pos, s.con⟩); pure r
  | _ =>
    if r.allocatable then throw s!"allocatable real register {repr r} as an operand"
    else pure r

theorem operands_eq' (i : MInst) :
    i.operands = (do let (_, ops) ← (MInst.visitOperands collectR i).run #[]; pure ops) := rfl

/-- A collector step pushes at most `k` operands. -/
structure PushLe {α : Type} (k : Nat) (x : StateT (Array Operand) (Except String) α) : Prop where
  run : ∀ s a s', x.run s = .ok (a, s') → s'.size ≤ s.size + k

theorem PushLe.pure' {α : Type} (a : α) :
    PushLe 0 (Pure.pure a : StateT (Array Operand) (Except String) α) :=
  ⟨fun s c s' h => by cases h; simp⟩

theorem PushLe.bind {α β : Type} {k1 k2 : Nat} {x : StateT (Array Operand) (Except String) α}
    {f : α → StateT (Array Operand) (Except String) β} (hx : PushLe k1 x)
    (hf : ∀ a, PushLe k2 (f a)) : PushLe (k1 + k2) (x >>= f) := by
  refine ⟨fun s c s'' h => ?_⟩
  rw [StateT.run_bind] at h
  cases hr : x.run s with
  | error e => rw [hr] at h; cases h
  | ok p =>
    obtain ⟨a, s'⟩ := p
    rw [hr] at h
    have := hx.run s a s' hr
    have := (hf a).run s' c s'' h
    omega

theorem PushLe.map {α β : Type} {k : Nat} (g : α → β) {x : StateT (Array Operand) (Except String) α}
    (hx : PushLe k x) : PushLe k (g <$> x) := by
  rw [map_eq_pure_bind]
  have := PushLe.bind hx fun a => PushLe.pure' (g a)
  simpa using this

theorem PushLe.mono {α : Type} {k k' : Nat} {x : StateT (Array Operand) (Except String) α}
    (hx : PushLe k x) (h : k ≤ k') : PushLe k' x :=
  ⟨fun s a s' hr => by have := hx.run s a s' hr; omega⟩

theorem PushLe.collect (sp : OpSpec) (r : Reg) : PushLe 1 (collectR sp r) := by
  refine ⟨fun s a s' h => ?_⟩
  cases r
  case vreg n c =>
    simp only [collectR, StateT.run, modify, modifyGet, MonadStateOf.modifyGet] at h
    cases h
    simp
  all_goals
    simp only [collectR] at h
    split at h
    · cases h
    · cases h; omega

theorem PushLe.mapM' {α β : Type} {k : Nat} {F : α → StateT (Array Operand) (Except String) β}
    (h : ∀ a, PushLe k (F a)) : ∀ l : List α, PushLe (k * l.length) (l.mapM F)
  | [] => by simpa using PushLe.pure' ([] : List β)
  | a :: l => by
    rw [List.mapM_cons]
    have := PushLe.bind (h a) fun b =>
      PushLe.bind (PushLe.mapM' h l) fun bs => PushLe.pure' (b :: bs)
    refine this.mono ?_
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

theorem PushLe.amode (am : AMode) : PushLe 2 (AMode.visit collectR am) := by
  cases am <;> simp only [AMode.visit]
  all_goals first
    | exact (PushLe.pure' _).mono (by omega)
    | exact (PushLe.bind (PushLe.collect _ _) fun _ => PushLe.pure' _).mono (by omega)
    | exact (PushLe.bind (PushLe.collect _ _) fun _ =>
        PushLe.bind (PushLe.collect _ _) fun _ => PushLe.pure' _).mono (by omega)

theorem PushLe.condBrKind (k : CondBrKind) : PushLe 1 (CondBrKind.visit collectR k) := by
  cases k <;> simp only [CondBrKind.visit]
  all_goals first
    | exact (PushLe.pure' _).mono (by omega)
    | exact (PushLe.bind (PushLe.collect _ _) fun _ => PushLe.pure' _).mono (by omega)

/-- Apply the collector combinators. -/
macro "pushLe_steps" : tactic => `(tactic| (
  repeat'
    first
    | exact PushLe.pure' _
    | exact PushLe.collect _ _
    | exact PushLe.amode _
    | exact PushLe.condBrKind _
    | apply PushLe.mapM'
    | apply PushLe.map
    | apply PushLe.bind
    | intro _))

theorem visit_pushLe (i : MInst) : PushLe (regCount i) (MInst.visitOperands collectR i) := by
  cases i
  case call info =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> simp only [MInst.visitOperands] <;> apply PushLe.mono <;> pushLe_steps <;>
      simp [regCount] <;> omega
  case tryCall info ti =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> simp only [MInst.visitOperands] <;> apply PushLe.mono <;> pushLe_steps <;>
      simp [regCount] <;> omega
  all_goals simp only [MInst.visitOperands]
  all_goals apply PushLe.mono
  all_goals pushLe_steps
  all_goals simp [regCount] <;> omega

/-- **An instruction's operands** are at most `regCount` of it. -/
theorem operands_size_le {i : MInst} {ops : Array Operand} (h : i.operands = .ok ops) :
    ops.size ≤ regCount i := by
  rw [operands_eq'] at h
  cases hr : (MInst.visitOperands collectR i).run #[] with
  | error e => rw [hr] at h; cases h
  | ok p =>
    obtain ⟨i₀, ops'⟩ := p
    rw [hr] at h
    cases h
    have := (visit_pushLe i).run #[] i₀ ops hr
    simpa using this

/-! ## `maxRC` -/

theorem foldl_max_le_iff {β : Type} (g : β → Nat) (X : Nat) :
    ∀ (L : List β) (m : Nat), L.foldl (fun m i => max m (g i)) m ≤ X ↔ m ≤ X ∧ ∀ i ∈ L, g i ≤ X
  | [], m => by simp
  | a :: L, m => by
    rw [List.foldl_cons, foldl_max_le_iff g X L]
    simp only [List.mem_cons, forall_eq_or_imp, Nat.max_le, and_assoc]

theorem foldl_blocks_le_iff (X : Nat) : ∀ (L : List VBlock) (m : Nat),
    L.foldl (fun m vb => vb.insts.foldl (fun m i => max m (regCount i)) m) m ≤ X ↔
      m ≤ X ∧ ∀ vb ∈ L, ∀ i ∈ vb.insts.toList, regCount i ≤ X
  | [], m => by simp
  | vb :: L, m => by
    rw [List.foldl_cons, foldl_blocks_le_iff X L, ← Array.foldl_toList, foldl_max_le_iff]
    simp only [List.mem_cons, forall_eq_or_imp, and_assoc]

/-- `maxRC vc` bounds `regCount` of every instruction of `vc`, and is at least 5. -/
theorem maxRC_le_iff {vc : VCode} {X : Nat} : maxRC vc ≤ X ↔
    5 ≤ X ∧ ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, regCount i ≤ X := by
  unfold maxRC
  rw [← Array.foldl_toList, foldl_blocks_le_iff]

theorem regCount_le_maxRC {vc : VCode} {vb : VBlock} {i : MInst} (hvb : vb ∈ vc.blocks.toList)
    (hi : i ∈ vb.insts.toList) : regCount i ≤ maxRC vc :=
  (maxRC_le_iff.mp (Nat.le_refl _)).2 vb hvb i hi

theorem five_le_maxRC (vc : VCode) : 5 ≤ maxRC vc := (maxRC_le_iff.mp (Nat.le_refl _)).1

/-! ## The items of the spill allocation -/

theorem moveWords_stack_r (l : Loc) (n : Nat) (c : RegClass) : moveWords l (.stack n c) = 10 := by
  cases l <;> rfl

theorem moveWords_stack_l (l : Loc) (n : Nat) (c : RegClass) : moveWords (.stack n c) l = 10 := by
  cases l <;> rfl

theorem regSaves_words (vb : VBlock) : ∀ L : List Reg,
    ((L.map fun r => RItem.move (.reg r) (.save r)).map (itemWords vb)).sum = 10 * L.length
  | [] => rfl
  | r :: L => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, regSaves_words vb L]
    simp only [itemWords, moveWords]
    omega

theorem saves_words (vb : VBlock) : (spillSaves.map (itemWords vb)).sum = restW :=
  regSaves_words vb calleeSaved

theorem keptPairs_length (i : MInst) (pairs : List (Operand × Loc)) :
    (keptPairs i pairs).length ≤ pairs.length := by
  have := List.length_filter_le (fun x : Operand × Loc => x.1.kind == .def) pairs
  unfold keptPairs
  split <;> simp only [List.length_take] <;> omega

/-- A list of moves with a slot on one side: 10 words each. -/
theorem slotMoves_le {α : Type} (vb : VBlock) (F : α → RItem) (hF : ∀ x, itemWords vb (F x) ≤ 10)
    (L : List α) : ((L.map F).map (itemWords vb)).sum ≤ 10 * L.length := by
  rw [List.map_map]
  exact sum_map_const_le fun x _ => hF x

theorem termEdgeDefs_length {vc : VCode} {b : Nat} {vb : VBlock} (hb : vc.blocks[b]? = some vb)
    (j : Nat) : (termEdgeDefs vb j).length ≤ maxRC vc := by
  have hvb : vb ∈ vc.blocks.toList := List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hb)
  unfold termEdgeDefs
  split
  · simp
  · rename_i i hi
    have h1 : regCount i ≤ maxRC vc :=
      regCount_le_maxRC hvb (Array.mem_toList_iff.mpr (Array.mem_of_back? hi))
    split
    · simp
    · split
      · simp
      · rename_i ops hops
        have h2 := operands_size_le hops
        have h3 := keptPairs_length i (ops.zip (spillLocs ops i.clobbers)).toList
        have h4 : (ops.zip (spillLocs ops i.clobbers)).toList.length ≤ ops.size := by
          simp only [Array.length_toList, Array.size_zip]; exact Nat.min_le_left _ _
        repeat' split
        all_goals simp only [List.length_take]
        all_goals omega

/-- The entry stores from predecessor `b` (`spillEntryStores`' inner match). -/
theorem entryFrom_words (h : Homes) (vc : VCode) (succs : Array (Array Nat)) (s b : Nat)
    (vb0 : VBlock) :
    ((match vc.blocks[b]?, succs[b]? with
      | some vb, some ss =>
        match ss.toList.idxOf? s with
        | some j => (termEdgeDefs vb j).map fun ((o, l) : Operand × Loc) =>
            RItem.move l (spillHome h o.vreg o.cls)
        | none => []
      | _, _ => []).map (itemWords vb0)).sum ≤ 10 * maxRC vc := by
  split
  · rename_i vb _ hvb _
    split
    · rename_i j _
      refine Nat.le_trans (slotMoves_le vb0 _ (fun x => ?_) _) ?_
      · simp [itemWords, spillHome, moveWords_stack_r]
      · have := termEdgeDefs_length hvb j
        omega
    · simp
  · simp

theorem entry_words (h : Homes) (vc : VCode) (succs preds : Array (Array Nat)) (s : Nat)
    (vb : VBlock) :
    ((spillEntryStores h vc succs preds s).map (itemWords vb)).sum ≤ 10 * maxRC vc := by
  unfold spillEntryStores
  -- the `#[b]` pattern has no equation lemmas: reduce each case by `show`
  rcases preds[s]? with _ | ⟨_ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · show (([] : List RItem).map (itemWords vb)).sum ≤ 10 * maxRC vc
    simp
  · show (([] : List RItem).map (itemWords vb)).sum ≤ 10 * maxRC vc
    simp
  · exact entryFrom_words h vc succs s b vb
  · show (([] : List RItem).map (itemWords vb)).sum ≤ 10 * maxRC vc
    simp

theorem argMoves_words (h : Homes) (vb tb w : VBlock) :
    ((spillArgMoves h vb tb).map (itemWords w)).sum ≤ 40 * vb.branchArgs.size := by
  simp only [spillArgMoves, List.map_append, List.sum_append]
  refine Nat.le_trans (Nat.add_le_add (sum_flatMap_le (c := 20) fun x _ => ?_)
    (sum_flatMap_le (c := 20) fun x _ => ?_)) ?_
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, itemWords, spillHome,
      moveWords_stack_l, moveWords_stack_r]
    omega
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, itemWords, spillHome,
      moveWords_stack_l, moveWords_stack_r]
    omega
  · simp only [List.length_zipIdx, List.length_zip, Array.length_toList]
    omega

theorem restores_words (vb : VBlock) : (spillRestores.map (itemWords vb)).sum = restW := by
  have : ∀ L : List Reg,
      ((L.map fun r => RItem.move (.save r) (.reg r)).map (itemWords vb)).sum = 10 * L.length := by
    intro L
    induction L with
    | nil => rfl
    | cons r L ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      simp only [itemWords, moveWords]
      omega
  exact this calleeSaved

/-- **One instruction's items** (`spillInst`): within its weight. -/
theorem inst_words (h : Homes) (k : Nat) (i : MInst) (vb : VBlock) (hk : vb.insts[k]? = some i) :
    ((spillInst h k i).map (itemWords vb)).sum ≤ szInstW i := by
  unfold spillInst
  split
  · have := szWords_le i
    simp [itemWords, hk]
    omega
  · rename_i ops hops
    have hsz := operands_size_le hops
    have hW : szWords i + 20 * regCount i ≤ szInstW i := by unfold szInstW; omega
    have hpl : (ops.zip (spillLocs ops i.clobbers)).toList.length ≤ ops.size := by
      simp only [Array.length_toList, Array.size_zip]; exact Nat.min_le_left _ _
    have hop : itemWords vb (.op k (spillLocs ops i.clobbers)) = szWords i := by
      simp [itemWords, hk, instWords_eq]
    have hF1 : ∀ x : Operand × Loc,
        itemWords vb (RItem.move (spillHome h x.1.vreg x.1.cls) x.2) ≤ 10 :=
      fun x => by simp [itemWords, spillHome, moveWords_stack_l]
    have hF2 : ∀ x : Operand × Loc,
        itemWords vb (RItem.move x.2 (spillHome h x.1.vreg x.1.cls)) ≤ 10 :=
      fun x => by simp [itemWords, spillHome, moveWords_stack_r]
    have hL := slotMoves_le vb _ hF1 ((ops.zip (spillLocs ops i.clobbers)).toList.filter
      (·.1.kind == .use))
    have hS := slotMoves_le vb _ hF2 (keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList)
    have hfl := List.length_filter_le (fun x : Operand × Loc => x.1.kind == .use)
      (ops.zip (spillLocs ops i.clobbers)).toList
    have hkl := keptPairs_length i (ops.zip (spillLocs ops i.clobbers)).toList
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, hop]
    have hT : ((if i.isTerminator = true then [] else
        (keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList).map
          fun x => RItem.move x.2 (spillHome h x.1.vreg x.1.cls)).map (itemWords vb)).sum ≤
        10 * (keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList).length := by
      split
      · simp
      · exact hS
    -- the restores before a `Rets`
    split
    · simp only [restores_words, szInstW]
      simp only [szInstW] at hW
      omega
    · simp only [List.map_nil, List.sum_nil]
      omega

/-- The branch arguments' parallel copy before a block's last instruction (`spillAlloc`'s
`moves`, when the block has a single successor). -/
theorem moves_words (h : Homes) (vc : VCode) (succs : Array (Array Nat)) (bi : Nat) (vb : VBlock) :
    ((match succs[bi]? with
      | some #[t] => match vc.blocks[t]? with
        | some tb => spillArgMoves h vb tb
        | none => []
      | _ => []).map (itemWords vb)).sum ≤ 40 * vb.branchArgs.size := by
  -- the `#[t]` pattern has no equation lemmas: reduce each case by `show`
  rcases succs[bi]? with _ | ⟨_ | ⟨t, _ | ⟨c, l⟩⟩⟩
  · show (([] : List RItem).map (itemWords vb)).sum ≤ _
    simp
  · show (([] : List RItem).map (itemWords vb)).sum ≤ _
    simp
  · show ((match vc.blocks[t]? with
        | some tb => spillArgMoves h vb tb
        | none => []).map (itemWords vb)).sum ≤ _
    split
    · exact argMoves_words h vb _ vb
    · simp
  · show (([] : List RItem).map (itemWords vb)).sum ≤ _
    simp

/-- **One block's items**: the entry block's saves and the entry stores (`pre`), then per
instruction the moves `mv k` before it (only before the last one) and `spillInst`. -/
theorem block_words (vc : VCode) (h : Homes) (vb : VBlock) (pre : List RItem)
    (hpre : (pre.map (itemWords vb)).sum ≤ restW + 10 * maxRC vc) (mv : MInst × Nat → List RItem)
    (hmv : ∀ p, ((mv p).map (itemWords vb)).sum ≤
      if p.2 + 1 = vb.insts.size then 40 * vb.branchArgs.size else 0) :
    7 + ((pre ++ (vb.insts.toList.zipIdx).flatMap fun p =>
      mv p ++ spillInst h p.2 p.1).map (itemWords vb)).sum ≤ vbW (maxRC vc) vb := by
  rw [List.map_append, List.sum_append, sum_flatMap]
  have hc : (if 0 + 1 ≤ vb.insts.size then 40 * vb.branchArgs.size else 0) ≤
      40 * vb.branchArgs.size := by split <;> omega
  have hw : wtA vb.insts = (vb.insts.toList.map szInstW).sum := rfl
  refine Nat.le_trans (Nat.add_le_add_left (Nat.add_le_add hpre
    (sum_zipIdx_le _ szInstW vb.insts.size (40 * vb.branchArgs.size) _ 0 fun p hp => ?_)) 7) ?_
  · obtain ⟨i, k⟩ := p
    obtain ⟨-, hk, hi⟩ := List.mem_zipIdx hp
    have hk' : vb.insts[k]? = some i := by
      simp only [Nat.zero_add, Array.length_toList] at hk
      rw [hi]; simp only [Nat.sub_zero, Array.getElem_toList]
      exact Array.getElem?_eq_getElem hk
    show ((mv (i, k) ++ spillInst h k i).map (itemWords vb)).sum ≤ _
    rw [List.map_append, List.sum_append]
    exact Nat.add_le_add (hmv (i, k)) (inst_words h k i vb hk')
  · unfold vbW
    omega

theorem spillAlloc_blocks_size (vc : VCode) : (spillAlloc vc).blocks.size = vc.blocks.size := by
  unfold spillAlloc
  rcases vc.cfg with _ | ⟨s, p⟩ <;> exact Array.size_mapIdx

/-- **The spill allocation's word bound** is at most the VCode measure `vcW` with `maxRC`
bounding every instruction's register operands. -/
theorem spillWordBound_le (vcp : VCode) : spillWordBound vcp ≤ vcW (maxRC vcp) vcp := by
  unfold spillWordBound rfWords vcW
  apply sum_map_le_of_getElem?
  · simp [spillAlloc_blocks_size]
  · intro bi x vb hx hvb
    obtain ⟨vb', items⟩ := x
    rw [Array.getElem?_toList, Array.getElem?_zip_eq_some] at hx
    rw [Array.getElem?_toList] at hvb
    obtain ⟨h1, h2⟩ := hx
    dsimp only at h1 h2
    rw [hvb] at h1
    obtain rfl := Option.some.inj h1
    unfold spillAlloc at h2
    rcases hc : vcp.cfg with e | ⟨succs, preds⟩
    all_goals
      rw [hc] at h2
      change (Array.mapIdx _ vcp.blocks)[bi]? = some items at h2
      rw [Array.getElem?_mapIdx, hvb, Option.map_some] at h2
      obtain rfl := Option.some.inj h2
      dsimp only
      refine block_words vcp (spillHomes vcp) vb _ ?_ _ ?_
      · rw [List.map_append, List.sum_append]
        refine Nat.add_le_add ?_ (entry_words _ _ _ _ _ _)
        by_cases hb0 : (bi == 0) = true
        · rw [ite_eq_left hb0, saves_words]
          exact Nat.le_refl _
        · rw [ite_eq_right hb0]
          exact Nat.zero_le _
      · intro p
        by_cases hk : (p.2 + 1 == vb.insts.size && !vb.branchArgs.isEmpty) = true
        · rw [ite_eq_left hk]
          simp only [Bool.and_eq_true, beq_iff_eq] at hk
          rw [ite_eq_left hk.1]
          first
          | exact moves_words (spillHomes vcp) vcp succs bi vb
          | exact moves_words (spillHomes vcp) vcp #[] bi vb
        · rw [ite_eq_right hk]
          exact Nat.zero_le _

/-! ## Monotonicity in the operand bound -/

/-- `vcW` is monotone in the bound `M` on the register operands. -/
theorem vcW_mono {M M' : Nat} (h : M ≤ M') (vc : VCode) : vcW M vc ≤ vcW M' vc := by
  unfold vcW
  exact sum_map_le' fun vb _ => by unfold vbW; have := Nat.mul_le_mul_left 10 h; omega

/-! ## Through `prepare` -/

/-- A block's weight and that of the edge blocks its branch targets may become. -/
def gW (M : Nat) (vb : VBlock) : Nat := vbW M vb + jumpBW M * tgA vb.insts

/-- The weight of an array of blocks. -/
def sumW (M : Nat) (A : Array VBlock) : Nat := (A.toList.map (vbW M)).sum

theorem sumW_push (M : Nat) (A : Array VBlock) (b : VBlock) :
    sumW M (A.push b) = sumW M A + vbW M b := by
  simp [sumW, Array.toList_push, List.sum_append]

theorem vbW_jump (M : Nat) (lab l : Label) :
    vbW M { label := lab, insts := #[.jump l] } = jumpBW M := by
  simp [vbW, jumpBW, wtA, wtL, szInstW, szWords, regCount, MInst.targets]

/-- Retargeting keeps an instruction's weight and register operands. -/
theorem setTargets_w {i i' : MInst} {ls : List Label} (h : i.setTargets ls = some i') :
    szInstW i' = szInstW i ∧ regCount i' = regCount i := by
  unfold MInst.setTargets at h
  split at h
  all_goals (try split at h)
  all_goals (cases h <;> simp_all [szInstW, szWords, regCount, MInst.targets])

theorem back_split {xs : Array MInst} {t : MInst} (hb : xs.back? = some t) :
    ∃ ys, xs.toList = ys ++ [t] := by
  rw [← Array.getLast?_toList, List.getLast?_eq_some_iff] at hb
  exact hb

/-- Retargeting a block's terminator keeps its weight. -/
theorem vbW_retarget (M : Nat) {vb : VBlock} {t t' : MInst} {ls : List Label}
    (hb : vb.insts.back? = some t) (ht : t.setTargets ls = some t') :
    vbW M { vb with insts := vb.insts.pop.push t' } = vbW M vb := by
  obtain ⟨ys, hys⟩ := back_split hb
  have e : (vb.insts.pop.push t').toList = ys ++ [t'] := by
    rw [Array.toList_push, Array.toList_pop, hys, List.dropLast_concat]
  unfold vbW wtA wtL
  simp only [e, hys, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    (setTargets_w ht).1]

theorem targets_le_tgA {xs : Array MInst} {t : MInst} (hb : xs.back? = some t) :
    t.targets.length ≤ tgA xs := by
  obtain ⟨ys, hys⟩ := back_split hb
  unfold tgA tgL
  simp only [hys, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  omega

/-- One successor of the splitting loop's inner loop: an edge block or none. -/
theorem innerStep_cases (ps : Array (Array Nat)) (st : Nat × Array VBlock × Array Label)
    (x : Nat × Label) :
    Proof.Prep.innerStep ps st x = (st.1 + 1, st.2.1.push { label := st.1, insts := #[.jump x.2] },
      st.2.2.push st.1) ∨ Proof.Prep.innerStep ps st x = (st.1, st.2.1, st.2.2.push x.2) := by
  unfold Proof.Prep.innerStep
  split
  · exact .inl rfl
  · exact .inr rfl

/-- The splitting loop's inner loop adds at most one edge block (a `jump`) per successor. -/
theorem innerFold_w (ps : Array (Array Nat)) (X : Nat) (h5 : 5 ≤ X) : ∀ (xs : List (Nat × Label))
    (next : Nat) (E : Array VBlock) (ls : Array Label),
    (∀ M, sumW M (xs.foldl (Proof.Prep.innerStep ps) (next, E, ls)).2.1 ≤
      sumW M E + jumpBW M * xs.length) ∧
    ((∀ b ∈ E.toList, ∀ m ∈ b.insts.toList, regCount m ≤ X) →
      ∀ b ∈ (xs.foldl (Proof.Prep.innerStep ps) (next, E, ls)).2.1.toList, ∀ m ∈ b.insts.toList,
        regCount m ≤ X)
  | [], next, E, ls => by simp
  | x :: xs, next, E, ls => by
    simp only [List.foldl_cons, List.length_cons]
    rcases innerStep_cases ps (next, E, ls) x with e | e <;> rw [e] <;> dsimp only
    · obtain ⟨h1, h2⟩ := innerFold_w ps X h5 xs (next + 1)
        (E.push { label := next, insts := #[.jump x.2] }) (ls.push next)
      refine ⟨fun M => ?_, fun hE => h2 fun b hb m hm => ?_⟩
      · have := h1 M
        rw [sumW_push, vbW_jump] at this
        rw [Nat.mul_add, Nat.mul_one]
        omega
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact hE b hb m hm
        · simp only [List.mem_singleton] at hm
          subst hm
          exact h5
    · obtain ⟨h1, h2⟩ := innerFold_w ps X h5 xs next E (ls.push x.2)
      refine ⟨fun M => ?_, h2⟩
      have := h1 M
      rw [Nat.mul_add, Nat.mul_one]
      omega

/-- The splitting loop's invariant after `k` kept blocks: the weight of the blocks and edge
blocks so far is at most `gW` of those `k` blocks, and every instruction's register operands
are at most `X`. -/
def PW (V1 : Array VBlock) (X k : Nat) (st : Nat × Array VBlock × Array VBlock) : Prop :=
  (∀ M, sumW M st.2.1 + sumW M st.2.2 ≤ ((V1.toList.take k).map (gW M)).sum) ∧
  ∀ b ∈ st.2.1.toList ++ st.2.2.toList, ∀ m ∈ b.insts.toList, regCount m ≤ X

/-- **`prepare`'s weight**: the blocks and edge blocks it builds before reordering weigh at most
`gW` of the input's blocks, and keep every instruction's register operands below `maxRC`. -/
theorem prepare_w {vc vcp : VCode} (h : prepare vc = .ok vcp) :
    ∃ (ss2 ps2 : Array (Array Nat)) (B E : Array VBlock),
      ({ vc with blocks := B ++ E } : VCode).cfg = .ok (ss2, ps2) ∧
      vcp = { vc with blocks := (rpo ss2).map fun i => (B ++ E)[i]! } ∧
      (∀ M, sumW M B + sumW M E ≤ (vc.blocks.toList.map (gW M)).sum) ∧
      ∀ b ∈ B.toList ++ E.toList, ∀ m ∈ b.insts.toList, regCount m ≤ maxRC vc := by
  unfold prepare at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i r0 hc0
  split at h
  · cases h
  rename_i r1 hc1
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  rename_i st hfor
  split at h
  · cases h
  rename_i r2 hc2
  simp only [pure, Except.pure, Except.ok.injEq] at h
  have HV1 : (Proof.Prep.keep vc.blocks (reachable r0.1)).toList.Sublist vc.blocks.toList := by
    rw [Proof.Prep.keep_toList]; exact Proof.Prep.kept_sublist _ _
  have h5 := five_le_maxRC vc
  rw [← Array.forIn_toList] at hfor
  have := Proof.Prep.forIn_inv _ _
    (fun k st => PW (Proof.Prep.keep vc.blocks (reachable r0.1)) (maxRC vc) k st)
    ?_ ?_ _ st ?_ hfor
  · obtain ⟨hW, hR⟩ := this
    exact ⟨r2.1, r2.2, st.2.1, st.2.2, hc2, h.symm, fun M => Nat.le_trans (hW M)
      (Nat.le_trans (sum_sublist_le _ (List.take_sublist _ _)) (sum_sublist_le _ HV1)), hR⟩
  · intro k x b b' hx hb hf
    rw [Array.toList_zipIdx, List.getElem?_zipIdx] at hx
    obtain ⟨vb, hvb, rfl⟩ : ∃ vb,
        (Proof.Prep.keep vc.blocks (reachable r0.1)).toList[k]? = some vb ∧ x = (vb, 0 + k) := by
      cases e : (Proof.Prep.keep vc.blocks (reachable r0.1)).toList[k]? with
      | none => rw [e] at hx; cases hx
      | some vb => rw [e] at hx; simp only [Option.map_some, Option.some.injEq] at hx
                   exact ⟨vb, rfl, hx.symm⟩
    simp only [Nat.zero_add] at hf ⊢
    have htake : (Proof.Prep.keep vc.blocks (reachable r0.1)).toList.take (k + 1) =
        (Proof.Prep.keep vc.blocks (reachable r0.1)).toList.take k ++ [vb] := by
      rw [List.take_add_one, hvb]; rfl
    have hvbV : vb ∈ vc.blocks.toList := HV1.subset (List.mem_of_getElem? hvb)
    obtain ⟨hW, hR⟩ := hb
    split at hf
    · -- no splitting
      simp only [pure, Except.pure, Except.ok.injEq, ForInStep.yield.injEq] at hf
      subst hf
      refine ⟨fun M => ?_, fun b hb m hm => ?_⟩
      · rw [htake, List.map_append, List.sum_append]
        have := hW M
        simp only [sumW_push, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, gW]
        omega
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
        rcases hb with (hb | rfl) | hb
        · exact hR b (List.mem_append_left _ hb) m hm
        · exact regCount_le_maxRC hvbV hm
        · exact hR b (List.mem_append_right _ hb) m hm
    · split at hf
      · rename_i t ht
        split at hf
        · cases hf
        rename_i v hv
        split at hf
        · rename_i t' ht'
          simp only [pure, Except.pure, Except.ok.injEq, ForInStep.yield.injEq] at hf
          subst hf
          rw [← Array.forIn_toList, Proof.Prep.forIn_yield_foldl _ _ (Proof.Prep.innerStep r1.2) _
            (fun a c => by simp only [Proof.Prep.innerStep]; split <;> rfl)] at hv
          simp only [pure, Except.pure, Except.ok.injEq] at hv
          subst hv
          obtain ⟨i1, i2⟩ := innerFold_w r1.2 (maxRC vc) h5
            ((r1.1[k]! : Array Nat).zip t.targets.toArray).toList b.1 b.2.2 #[]
          have hlen : ((r1.1[k]! : Array Nat).zip t.targets.toArray).toList.length ≤
              tgA vb.insts := by
            simp only [Array.length_toList, Array.size_zip, List.size_toArray]
            exact Nat.le_trans (Nat.min_le_right _ _) (targets_le_tgA ht)
          refine ⟨fun M => ?_, fun b' hb m hm => ?_⟩
          · rw [htake, List.map_append, List.sum_append]
            have := hW M
            have := i1 M
            have := Nat.mul_le_mul_left (jumpBW M) hlen
            simp only [sumW_push, vbW_retarget M ht ht', List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil, gW]
            omega
          · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
            rcases hb with (hb | rfl) | hb
            · exact hR b' (List.mem_append_left _ hb) m hm
            · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hm
              rcases hm with hm | rfl
              · exact regCount_le_maxRC hvbV (Proof.Prep.pop_mem hm)
              · rw [(setTargets_w ht').2]
                exact regCount_le_maxRC hvbV (Array.mem_toList_iff.mpr (Array.mem_of_back? ht))
            · exact i2 (fun b hb => hR b (List.mem_append_right _ hb)) b' hb m hm
        · simp [throw, throwThe, MonadExceptOf.throw] at hf
      · simp [throw, throwThe, MonadExceptOf.throw] at hf
  · intro x c c' hf
    split at hf
    · cases hf
    · split at hf
      · split at hf
        · cases hf
        · split at hf
          · cases hf
          · simp [throw, throwThe, MonadExceptOf.throw] at hf
      · simp [throw, throwThe, MonadExceptOf.throw] at hf
  · exact ⟨fun M => by simp [sumW], fun b hb => by simp at hb⟩

/-- `rpo` of a CFG of `V`: indices of `V`, each once. -/
theorem rpo_facts {vc : VCode} {V : Array VBlock} {ss ps : Array (Array Nat)}
    (hc : ({ vc with blocks := V } : VCode).cfg = .ok (ss, ps)) :
    (∀ i ∈ (rpo ss).toList, i < V.size) ∧ (rpo ss).toList.Nodup := by
  have cs := Proof.Prep.cfg_spec hc
  by_cases h0 : ss.size = 0
  · have e : rpo ss = #[] := by unfold rpo; simp [h0]
    rw [e]
    simp
  · obtain ⟨h1, h2, -⟩ := Proof.Prep.rpo_spec (Proof.Prep.succsIn_of cs) h0
    exact ⟨fun i hi => cs.size ▸ h1 i hi, h2⟩

theorem sum_range_getElem! (A : Array VBlock) (f : VBlock → Nat) :
    ((List.range A.size).map fun i => f A[i]!).sum = (A.toList.map f).sum := by
  congr 1
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [getElem!_pos A j h1]

/-- **`prepare` keeps the operand bound**: every instruction of its output is one of its input,
one retargeted (same `regCount`), or an edge block's `jump`. -/
theorem maxRC_prepare {vc vcp : VCode} (hp : prepare vc = .ok vcp) : maxRC vcp ≤ maxRC vc := by
  obtain ⟨ss2, ps2, B, E, hc2, rfl, -, hRC⟩ := prepare_w hp
  obtain ⟨hR, -⟩ := rpo_facts hc2
  rw [maxRC_le_iff]
  refine ⟨five_le_maxRC vc, fun vb hvb i hi => ?_⟩
  have hvb' : vb ∈ ((rpo ss2).map fun i => (B ++ E)[i]!).toList := hvb
  rw [Array.mem_toList_iff, Array.mem_map] at hvb'
  obtain ⟨j, hj, rfl⟩ := hvb'
  have hj2 : j < (B ++ E).size := hR j (by simpa using hj)
  rw [getElem!_pos (B ++ E) j hj2] at hi
  exact hRC _ (by rw [← Array.toList_append]; exact Array.getElem_mem_toList hj2) i hi

/-- **`prepare`'s weight**: at most the input's, plus an edge block (`jumpBW M`) per branch
target of the input. -/
theorem vcW_prepare {vc vcp : VCode} (hp : prepare vc = .ok vcp) (M : Nat) :
    vcW M vcp ≤ vcW M vc + jumpBW M * vcTg vc := by
  obtain ⟨ss2, ps2, B, E, hc2, rfl, hW, -⟩ := prepare_w hp
  obtain ⟨hR, hN⟩ := rpo_facts hc2
  have e1 : vcW M { vc with blocks := (rpo ss2).map fun i => (B ++ E)[i]! } =
      ((rpo ss2).toList.map fun i => vbW M (B ++ E)[i]!).sum := by
    simp only [vcW, Array.toList_map, List.map_map, Function.comp_def]
  have e2 : (vc.blocks.toList.map (gW M)).sum = vcW M vc + jumpBW M * vcTg vc := by
    have e : vc.blocks.toList.map (gW M) =
        vc.blocks.toList.map fun vb => vbW M vb + jumpBW M * tgA vb.insts := rfl
    rw [e, sum_map_add', sum_map_mul']
    rfl
  have h1 := sum_nodup_le (fun i => vbW M (B ++ E)[i]!) hN
    (S := List.range (B ++ E).size) fun x hx => List.mem_range.mpr (hR x hx)
  rw [sum_range_getElem! (B ++ E) (vbW M), Array.toList_append, List.map_append,
    List.sum_append] at h1
  have := hW M
  unfold sumW at this
  omega

end E2E
