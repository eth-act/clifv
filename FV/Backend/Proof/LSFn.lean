import FV.Backend.LinearScan
import FV.Backend.Proof.PrepareComplete

/-!
# The Lean allocator's function view (V4b-3, #275): what `Fn.make` computes

`Fn.make vc = .ok fn` numbers the instructions of `vc` globally, blocks in order (`FnOk`):
instruction `k` of block `b` is global instruction `fn.start[b] + k` (`FnOk.inst`), with its
operand view and block (`fn.blk`); `fn.start` is the prefix sum of the block sizes; every vreg an
operand, parameter or branch argument mentions is below `fn.nv`; `fn.clsOf` is `vc.classes`.
`FnOk.decode`: every global index below the total is such an instruction. `mem_preds`: the CFG's
predecessor lists invert its successor lists.
-/

namespace Backend.Proof.LS

open Backend Backend.LinearScan

/-- What `Fn.make vc = .ok fn` establishes. -/
structure FnOk (vc : VCode) (fn : Fn) : Prop where
  vc_eq : fn.vc = vc
  cfg : vc.cfg = .ok (fn.succs, fn.preds)
  start_size : fn.start.size = vc.blocks.size + 1
  start_zero : fn.start[0]? = some 0
  start_succ : ∀ (b : Nat) (vb : VBlock), vc.blocks[b]? = some vb →
    fn.start[b + 1]? = some (fn.start.getD b 0 + vb.insts.size)
  total : fn.insts.size = fn.start.getD vc.blocks.size 0
  ops_size : fn.ops.size = fn.insts.size
  blk_size : fn.blk.size = fn.insts.size
  inst : ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst), vc.blocks[b]? = some vb → vb.insts[k]? = some i →
    fn.insts[fn.start.getD b 0 + k]? = some i ∧ fn.blk[fn.start.getD b 0 + k]? = some b ∧
    ∃ ops, i.operands = .ok ops ∧ fn.ops[fn.start.getD b 0 + k]? = some ops
  nv_ops : ∀ (g : Nat) (os : Array Operand), fn.ops[g]? = some os → ∀ o ∈ os.toList, o.vreg < fn.nv
  nv_regs : ∀ (b : Nat) (vb : VBlock), vc.blocks[b]? = some vb →
    ∀ r ∈ vb.params.toList ++ vb.branchArgs.toList, ∃ n c, r = .vreg n c ∧ n < fn.nv
  nv_cls : vc.classes.size ≤ fn.nv
  cls : ∀ (v : Nat) (c : RegClass), vc.classes[v]? = some c → fn.clsOf v = c

/-! ## `Fn.make` -/

private theorem starts_getElem? : ∀ (L : List Nat) (a b : Nat), b ≤ L.length →
    (starts L a)[b]? = some (a + (L.take b).sum)
  | [], a, 0, _ => by simp [starts]
  | [], _, _ + 1, h => by simp at h
  | n :: L, a, 0, _ => by simp [starts]
  | n :: L, a, b + 1, h => by
    simp only [starts, List.getElem?_cons_succ, List.take_succ_cons, List.sum_cons]
    rw [starts_getElem? L (a + n) b (by simp at h; omega)]
    congr 1; omega

private theorem length_starts : ∀ (L : List Nat) (a : Nat), (starts L a).length = L.length + 1
  | [], _ => rfl
  | _ :: L, a => by simp [starts, length_starts L]

private theorem getElem?_flatMap_off {α β : Type} (f : α → List β) (len : α → Nat)
    (hl : ∀ x, (f x).length = len x) :
    ∀ (L : List α) (b k : Nat) (x : α), L[b]? = some x → k < len x →
      (L.flatMap f)[((L.map len).take b).sum + k]? = (f x)[k]?
  | [], _, _, _, h, _ => by simp at h
  | y :: L, 0, k, x, h, hk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [List.flatMap_cons, List.getElem?_append_left (by rw [hl]; simpa using hk)]
    simp
  | y :: L, b + 1, k, x, h, hk => by
    simp only [List.getElem?_cons_succ] at h
    rw [List.flatMap_cons, List.map_cons, List.take_succ_cons, List.sum_cons, Nat.add_assoc,
      List.getElem?_append_right (by rw [hl]; omega), hl, Nat.add_sub_cancel_left]
    exact getElem?_flatMap_off f len hl L b k x h hk

private theorem foldl_ge {α : Type} (f : Nat → α → Nat) (hf : ∀ n x, n ≤ f n x) :
    ∀ (l : List α) (init : Nat), init ≤ l.foldl f init
  | [], _ => Nat.le_refl _
  | x :: l, init => Nat.le_trans (hf init x) (foldl_ge f hf l (f init x))

private theorem le_foldl_of_mem {α : Type} (f : Nat → α → Nat) (hf : ∀ n x, n ≤ f n x)
    {c : Nat} {x : α}
    (hx : ∀ n, c ≤ f n x) : ∀ (l : List α) (init : Nat), x ∈ l → c ≤ l.foldl f init
  | [], _, h => by simp at h
  | y :: l, init, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (hx init) (foldl_ge f hf l _)
    · exact le_foldl_of_mem f hf hx l _ h

private theorem amax_ge {α : Type} (g : α → Nat) (xs : Array α) (n : Nat) :
    n ≤ xs.foldl (fun n x => max n (g x)) n := by
  rw [← Array.foldl_toList]; exact foldl_ge _ (fun _ _ => Nat.le_max_left _ _) _ _

private theorem amax_mem {α : Type} (g : α → Nat) (xs : Array α) (n : Nat) {x : α}
    (hx : x ∈ xs.toList) :
    g x ≤ xs.foldl (fun n x => max n (g x)) n := by
  rw [← Array.foldl_toList]
  exact le_foldl_of_mem (fun n x => max n (g x)) (fun _ _ => Nat.le_max_left _ _)
    (fun _ => Nat.le_max_right _ _) _ _ hx

/-- `Fn.make`'s vreg bound over the operands. -/
private theorem nv_ge (ops : List (Array Operand)) (n : Nat) :
    n ≤ ops.foldl (fun n os => os.foldl (fun n o => max n (o.vreg + 1)) n) n :=
  foldl_ge _ (fun n os => amax_ge (fun o : Operand => o.vreg + 1) os n) _ _

private theorem nv_mem {ops : List (Array Operand)} {os : Array Operand} (hos : os ∈ ops)
    {o : Operand} (ho : o ∈ os.toList) (n : Nat) :
    o.vreg + 1 ≤ ops.foldl (fun n os => os.foldl (fun n o => max n (o.vreg + 1)) n) n :=
  le_foldl_of_mem (fun n os => os.foldl (fun n o => max n (o.vreg + 1)) n)
    (fun n os => amax_ge (fun o : Operand => o.vreg + 1) os n)
    (fun n => amax_mem (fun o : Operand => o.vreg + 1) os n ho) _ _ hos

private theorem nv0_ge (B : Array VBlock) (n : Nat) :
    n ≤ B.foldl (fun n b => (b.params ++ b.branchArgs).foldl
      (fun n r => max n ((vregOf r).getD 0 + 1)) n) n := by
  rw [← Array.foldl_toList]
  exact foldl_ge _ (fun n b => amax_ge (fun r => (vregOf r).getD 0 + 1) _ n) _ _

private theorem nv0_mem {B : Array VBlock} {vb : VBlock} (hvb : vb ∈ B.toList) {r : Reg}
    (hr : r ∈ (vb.params ++ vb.branchArgs).toList) (n : Nat) :
    (vregOf r).getD 0 + 1 ≤ B.foldl (fun n b => (b.params ++ b.branchArgs).foldl
      (fun n r => max n ((vregOf r).getD 0 + 1)) n) n := by
  rw [← Array.foldl_toList]
  exact le_foldl_of_mem (fun n (b : VBlock) => (b.params ++ b.branchArgs).foldl
      (fun n r => max n ((vregOf r).getD 0 + 1)) n)
    (fun n b => amax_ge (fun r => (vregOf r).getD 0 + 1) _ n)
    (fun n => amax_mem (fun r => (vregOf r).getD 0 + 1) _ n hr) _ _ hvb

theorem fnOk_of_make {vc : VCode} {fn : Fn} (h : Fn.make vc = .ok fn) : FnOk vc fn := by
  unfold Fn.make at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i p hc
  obtain ⟨succs, preds⟩ := p
  simp only at h
  split at h
  · cases h
  rename_i ops hops
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hall
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hall
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨hlen, hops⟩ := Prep.lmapM_ok hops
  -- the prefix sums
  have hstart : ∀ b, b ≤ vc.blocks.size →
      (starts (vc.blocks.toList.map (·.insts.size)) 0).toArray.getD b 0 =
        ((vc.blocks.toList.map (·.insts.size)).take b).sum := by
    intro b hb
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      starts_getElem? _ _ _ (by simpa using hb)]
    simp
  have htotal : (vc.blocks.toList.map (·.insts.size)).sum =
      (starts (vc.blocks.toList.map (·.insts.size)) 0).toArray.getD vc.blocks.size 0 := by
    rw [hstart _ (Nat.le_refl _), List.take_of_length_le (by simp)]
  -- the block of each instruction
  have hzip : (vc.blocks.toList.zipIdx.map fun p => p.1.insts.size) =
      vc.blocks.toList.map (·.insts.size) := by
    rw [show (fun p : VBlock × Nat => p.1.insts.size) =
      (fun vb : VBlock => vb.insts.size) ∘ Prod.fst from rfl, ← List.map_map,
      List.zipIdx_map_fst]
  have hblkLen : ∀ p : VBlock × Nat,
      ((fun x : VBlock × Nat => match x with | (b, i) => List.replicate b.insts.size i) p).length =
        p.1.insts.size := by
    rintro ⟨b, i⟩; simp
  have hinstLen : ∀ vb : VBlock,
      ((fun x : VBlock => x.insts.toList) vb).length = vb.insts.size := by
    intro vb; simp
  refine
    { vc_eq := rfl
      cfg := hc
      start_size := by simp [length_starts]
      start_zero := by simp [starts_getElem? _ 0 0 (Nat.zero_le _)]
      start_succ := ?_
      total := ?_
      ops_size := by simp [hlen]
      blk_size := ?_
      inst := ?_
      nv_ops := ?_
      nv_regs := ?_
      nv_cls := ?_
      cls := ?_ }
  · intro b vb hb
    have hbl : b < vc.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
    simp only
    rw [hstart b (Nat.le_of_lt hbl), List.getElem?_toArray,
      starts_getElem? _ _ _ (by simp; omega), List.take_add_one, List.sum_append]
    simp [hb]
  · simp only
    rw [← htotal, List.size_toArray, List.length_flatMap,
      List.map_congr_left (fun vb _ => hinstLen vb)]
  · simp only [List.size_toArray, List.length_flatMap, List.length_replicate, Array.length_toList]
    rw [hzip]
  · intro b vb k i hb hk
    have hbl : b < vc.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
    have hks : k < vb.insts.size := (Array.getElem?_eq_some_iff.mp hk).1
    simp only
    rw [hstart b (Nat.le_of_lt hbl)]
    have hi : (vc.blocks.toList.flatMap fun x => x.insts.toList)[
        ((vc.blocks.toList.map (·.insts.size)).take b).sum + k]? = some i := by
      rw [getElem?_flatMap_off _ _ hinstLen vc.blocks.toList b k vb (by simpa using hb) hks]
      simpa using hk
    obtain ⟨os, hos, hos'⟩ := hops _ i hi
    refine ⟨by rw [List.getElem?_toArray]; exact hi, ?_, os, hos,
      by rw [List.getElem?_toArray]; exact hos'⟩
    rw [List.getElem?_toArray, ← hzip,
      getElem?_flatMap_off _ _ hblkLen vc.blocks.toList.zipIdx b k (vb, b)
        (by simp [List.getElem?_zipIdx, hb]) hks]
    simp [hks]
  · intro g os hg o ho
    simp only at hg ⊢
    rw [List.getElem?_toArray] at hg
    exact nv_mem (List.mem_of_getElem? hg) ho _
  · intro b vb hb r hr
    have hvb : vb ∈ vc.blocks.toList := by
      rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? hb
    have hr' : r ∈ (vb.params ++ vb.branchArgs).toList := by simpa using hr
    have hsome := (Array.all_eq_true'.mp hall) vb (Array.mem_toList_iff.mp hvb)
    have hsome' := (Array.all_eq_true'.mp hsome) r (Array.mem_toList_iff.mp hr')
    have hle := Nat.le_trans (nv0_mem hvb hr' vc.classes.size) (nv_ge ops _)
    cases r with
    | vreg n c => exact ⟨n, c, rfl, Nat.lt_of_succ_le hle⟩
    | _ => simp [vregOf] at hsome'
  · exact Nat.le_trans (nv0_ge vc.blocks _) (nv_ge ops _)
  · intro v c hv
    have hvl : v < vc.classes.size := (Array.getElem?_eq_some_iff.mp hv).1
    have hnv : vc.classes.size ≤ _ := Nat.le_trans (nv0_ge vc.blocks _) (nv_ge ops _)
    have hlt := Nat.lt_of_lt_of_le hvl hnv
    simp only [Fn.clsOf, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hlt, ↓reduceDIte]
    simp [hv]

section
variable {vc : VCode} {fn : Fn} (hf : FnOk vc fn)
include hf

theorem FnOk.nblocks : fn.nblocks = vc.blocks.size := by
  simp [Fn.nblocks, hf.vc_eq]

private theorem FnOk.getD_zero : fn.start.getD 0 0 = 0 := by
  simp [Array.getD_eq_getD_getElem?, hf.start_zero]

private theorem FnOk.getD_succ {b : Nat} {vb : VBlock} (hb : vc.blocks[b]? = some vb) :
    fn.start.getD (b + 1) 0 = fn.start.getD b 0 + vb.insts.size := by
  rw [Array.getD_eq_getD_getElem? (i := b + 1), hf.start_succ b vb hb, Option.getD_some]

/-- `start` is monotone. -/
theorem FnOk.start_mono {b b' : Nat} (h : b ≤ b') (hb' : b' ≤ vc.blocks.size) :
    fn.start.getD b 0 ≤ fn.start.getD b' 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have hlt : b + d < vc.blocks.size := by omega
    rw [← Nat.add_assoc, hf.getD_succ (vb := vc.blocks[b + d]) (by simp [hlt])]
    exact Nat.le_trans (ih (by omega) (by omega)) (Nat.le_add_right _ _)

/-- Every global instruction index is instruction `k` of some block `b`. -/
theorem FnOk.decode {g : Nat} (hg : g < fn.insts.size) :
    ∃ b vb k, vc.blocks[b]? = some vb ∧ k < vb.insts.size ∧ g = fn.start.getD b 0 + k ∧
      fn.blk[g]? = some b := by
  have key : ∀ n, n ≤ vc.blocks.size → g < fn.start.getD n 0 → ∃ b vb k,
      vc.blocks[b]? = some vb ∧ k < vb.insts.size ∧ g = fn.start.getD b 0 + k ∧
        fn.blk[g]? = some b := by
    intro n
    induction n with
    | zero => intro _ h; rw [hf.getD_zero] at h; omega
    | succ n ih =>
      intro hn h
      by_cases hlt : g < fn.start.getD n 0
      · exact ih (by omega) hlt
      · have hb : vc.blocks[n]? = some vc.blocks[n] := Array.getElem?_eq_getElem (by omega)
        rw [hf.getD_succ hb] at h
        have hk : g - fn.start.getD n 0 < vc.blocks[n].insts.size := by omega
        refine ⟨n, vc.blocks[n], g - fn.start.getD n 0, hb, hk, by omega, ?_⟩
        have := (hf.inst n _ _ _ hb (Array.getElem?_eq_getElem hk)).2.1
        rwa [Nat.add_sub_cancel' (by omega)] at this
  exact key _ (Nat.le_refl _) (hf.total ▸ hg)

/-- A global index determines block and local index. -/
theorem FnOk.inj {b b' : Nat} {vb vb' : VBlock} {k k' : Nat} (hb : vc.blocks[b]? = some vb)
    (hb' : vc.blocks[b']? = some vb') (hk : k < vb.insts.size) (hk' : k' < vb'.insts.size)
    (h : fn.start.getD b 0 + k = fn.start.getD b' 0 + k') : b = b' ∧ k = k' := by
  have hbl : b < vc.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hbl' : b' < vc.blocks.size := (Array.getElem?_eq_some_iff.mp hb').1
  rcases Nat.lt_trichotomy b b' with hlt | rfl | hlt
  · have h1 := hf.getD_succ hb
    have h2 := hf.start_mono (b := b + 1) (b' := b') hlt (Nat.le_of_lt hbl')
    omega
  · exact ⟨rfl, by omega⟩
  · have h1 := hf.getD_succ hb'
    have h2 := hf.start_mono (b := b' + 1) (b' := b) hlt (Nat.le_of_lt hbl)
    omega

theorem FnOk.params {b : Nat} {vb : VBlock} (hb : vc.blocks[b]? = some vb) :
    fn.params b = vb.params.toList.filterMap vregOf := by
  simp [Fn.params, hf.vc_eq, hb]

theorem FnOk.args {b : Nat} {vb : VBlock} (hb : vc.blocks[b]? = some vb) :
    fn.args b = vb.branchArgs.toList.filterMap vregOf := by
  simp [Fn.args, hf.vc_eq, hb]

end

/-! ## The CFG -/

/-- One predecessor-list update of `VCode.cfg`: push `i` onto the list of every `s ∈ ss`. -/
private def predStep (P : Array (Array Nat)) (x : Array Nat × Nat) : Array (Array Nat) :=
  x.1.toList.foldl (fun P s => P.modify s fun l => l.push x.2) P

private theorem mem_getD_modify_push {P : Array (Array Nat)} {s t i y : Nat}
    (hy : y ∈ (P.getD t #[]).toList) : y ∈ ((P.modify s fun l => l.push i).getD t #[]).toList := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify] at hy ⊢
  split
  · subst_vars; cases h : P[t]? <;> simp_all
  · exact hy

private theorem inner_spec (i : Nat) :
    ∀ (ls : List Nat) (P : Array (Array Nat)),
      (ls.foldl (fun P s => P.modify s fun l => l.push i) P).size = P.size ∧
      (∀ t y, y ∈ (P.getD t #[]).toList →
        y ∈ ((ls.foldl (fun P s => P.modify s fun l => l.push i) P).getD t #[]).toList) ∧
      (∀ t ∈ ls, t < P.size →
        i ∈ ((ls.foldl (fun P s => P.modify s fun l => l.push i) P).getD t #[]).toList)
  | [], P => by simp
  | s :: ls, P => by
    obtain ⟨h1, h2, h3⟩ := inner_spec i ls (P.modify s fun l => l.push i)
    simp only [List.foldl_cons, Array.size_modify] at h1 h2 h3 ⊢
    refine ⟨h1, fun t y hy => h2 t y (mem_getD_modify_push hy), fun t ht hlt => ?_⟩
    rcases List.mem_cons.mp ht with rfl | ht
    · refine h2 t i ?_
      simp [Array.getD_eq_getD_getElem?, Array.getElem_modify, hlt]
    · exact h3 t ht hlt

private theorem outer_spec :
    ∀ (L : List (Array Nat × Nat)) (P : Array (Array Nat)),
      (L.foldl predStep P).size = P.size ∧
      (∀ t y, y ∈ (P.getD t #[]).toList → y ∈ ((L.foldl predStep P).getD t #[]).toList) ∧
      (∀ x ∈ L, ∀ t ∈ x.1.toList, t < P.size → x.2 ∈ ((L.foldl predStep P).getD t #[]).toList)
  | [], P => by simp
  | x :: L, P => by
    have hg : (predStep P x).size = P.size ∧
        (∀ t y, y ∈ (P.getD t #[]).toList → y ∈ ((predStep P x).getD t #[]).toList) ∧
        (∀ t ∈ x.1.toList, t < P.size → x.2 ∈ ((predStep P x).getD t #[]).toList) :=
      inner_spec x.2 x.1.toList P
    obtain ⟨g1, g2, g3⟩ := hg
    obtain ⟨h1, h2, h3⟩ := outer_spec L (predStep P x)
    simp only [List.foldl_cons]
    refine ⟨by rw [h1, g1], fun t y hy => h2 t y (g2 t y hy), fun y hy t ht hlt => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h2 t _ (g3 t ht hlt)
    · exact h3 y hy t ht (by rw [g1]; exact hlt)

/-- The CFG's predecessor lists invert its successor lists. -/
theorem mem_preds {vc : VCode} {succs preds : Array (Array Nat)}
    (h : vc.cfg = .ok (succs, preds)) {b s : Nat} {ss : Array Nat} (hb : succs[b]? = some ss)
    (hs : s ∈ ss.toList) : b ∈ (preds.getD s #[]).toList := by
  have hspec := Prep.cfg_spec h
  -- `s` is a block index
  have hslt : s < vc.blocks.size := by
    have hbl : b < vc.blocks.size := by
      rw [← hspec.size]; exact (Array.getElem?_eq_some_iff.mp hb).1
    obtain ⟨t, ts, -, -, hts, hsz, hl⟩ := hspec.blk b vc.blocks[b] (by simp [hbl])
    rw [hb] at hts; cases hts
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
    have hj' : j < t.targets.length := by rw [← hsz]; simpa using hj
    obtain ⟨k, hk, hlab⟩ := hl j t.targets[j] (by simp [hj'])
    obtain ⟨hk', -⟩ := Prep.lab_some hlab
    simp only [Array.getElem_toList]
    rw [Array.getElem?_eq_getElem (by simpa using hj)] at hk
    cases hk
    exact hk'
  unfold VCode.cfg at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i succs' hsuccs
  split at h
  · cases h
  rename_i r hr
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [← Array.forIn_toList, Prep.forIn_yield_foldl _ _ predStep _ (fun x P => by
    rw [← Array.forIn_toList, List.forIn_pure_yield_eq_foldl]; rfl)] at hr
  simp only [pure, Except.pure, Except.ok.injEq] at hr
  subst hr
  refine (outer_spec _ _).2.2 (ss, b) ?_ s hs (by simpa using hslt)
  rw [Array.mem_toList_iff, Array.mem_zipIdx_iff_getElem?]
  exact hb

end Backend.Proof.LS
