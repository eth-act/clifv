import FV.E2E.SizeDefs
import FV.E2E.EmitCondsLower

/-!
# The size of `lowerFunction`'s output from the ISLE runs (V6c)

`size_lower`: given the driver's contract `IselSz f` (every ISLE run of the driver emits at most
the weight `stmtSzB`/`termSzB` and the branch targets `tgStmtK`/`termTgB` of its CLIF
instruction), the VCode `lowerFunction f` builds has

* every instruction's register operands below `mIn f` (`maxRC`),
* weight `vcW (mIn f)` below the input-side `vcIn (mIn f) f`, and
* branch targets `vcTg` below `tgIn f`.

The walk is `vc_emit`'s (`EmitCondsLower`), on sums instead of memberships: `vcBlocksOf` lists
one renamed raw block per CLIF block, then the renamed edge blocks block by block. A raw block's
code is the entry `pre` (the `Args`, at most one pair per parameter, and the stack-parameter
loads), the statements' segments (a run started from nothing emitted, and a result `mov` per
`extraOf` entry), and the terminator's segment (`fixTry`: a `try_call`'s last `call` becomes the
`tryCall`, one word more and a target per successor). The alias renaming keeps every weight
(`szInstW_mapRegs`). An edge block is one `jump` with the branch arguments of its successor,
and there is at most one per entry of `edgeArgsIn` (`edges_le`). An ISLE-emitted instruction
`m` has `20 · regCount m ≤ szInstW m`, at most the run's weight bound, so its register operands
are below that bound over 20 (`mIn`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Cov Backend.Proof.Driver

/-! ## Weights of instructions and lists -/

theorem szInstW_mapRegs (R : Reg → Reg) (m : MInst) : szInstW (m.mapRegs R) = szInstW m := by
  cases m <;> simp [MInst.mapRegs, szInstW, szWords, regCount, MInst.targets]

theorem regCount_mapRegs (R : Reg → Reg) (m : MInst) : regCount (m.mapRegs R) = regCount m := by
  cases m <;> simp [MInst.mapRegs, regCount]

theorem regCount_le_szInstW (m : MInst) : 20 * regCount m ≤ szInstW m := by
  unfold szInstW; omega

theorem wtL_cons (m : MInst) (ms : List MInst) : wtL (m :: ms) = szInstW m + wtL ms := by
  simp [wtL]

theorem wtL_append (a b : List MInst) : wtL (a ++ b) = wtL a + wtL b := by
  simp [wtL]

theorem tgL_append (a b : List MInst) : tgL (a ++ b) = tgL a + tgL b := by
  simp [tgL]

theorem wtL_map_mapRegs (R : Reg → Reg) (ms : List MInst) :
    wtL (ms.map (·.mapRegs R)) = wtL ms := by
  simp [wtL, Function.comp_def, szInstW_mapRegs]

theorem tgL_map_mapRegs (R : Reg → Reg) (ms : List MInst) :
    tgL (ms.map (·.mapRegs R)) = tgL ms := by
  simp [tgL, Function.comp_def, targets_mapRegs]

theorem wtL_flatten : ∀ ls : List (List MInst), wtL ls.flatten = (ls.map wtL).sum
  | [] => rfl
  | l :: ls => by simp only [List.flatten_cons, wtL_append, wtL_flatten ls, List.map_cons, List.sum_cons]

theorem tgL_flatten : ∀ ls : List (List MInst), tgL ls.flatten = (ls.map tgL).sum
  | [] => rfl
  | l :: ls => by simp only [List.flatten_cons, tgL_append, tgL_flatten ls, List.map_cons, List.sum_cons]

theorem szInstW_le_wtL {m : MInst} : ∀ {ms : List MInst}, m ∈ ms → szInstW m ≤ wtL ms
  | [], h => by cases h
  | a :: ms, h => by
    rw [wtL_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := szInstW_le_wtL h; omega

theorem wtL_le_mul {k : Nat} : ∀ {ms : List MInst}, (∀ m ∈ ms, szInstW m ≤ k) → wtL ms ≤ k * ms.length
  | [], _ => by simp [wtL]
  | a :: ms, h => by
    rw [wtL_cons, List.length_cons, Nat.mul_succ]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := wtL_le_mul (fun m hm => h m (List.mem_cons_of_mem _ hm))
    omega

theorem tgL_eq_zero : ∀ {ms : List MInst}, (∀ m ∈ ms, m.targets = []) → tgL ms = 0
  | [], _ => rfl
  | a :: ms, h => by
    simp only [tgL, List.map_cons, List.sum_cons] at *
    rw [h a (List.mem_cons_self ..)]
    have := tgL_eq_zero (fun m hm => h m (List.mem_cons_of_mem _ hm))
    simpa [tgL] using this

/-- A register operand bound from a weight bound: `20 · regCount m ≤ szInstW m ≤ wtL ms`. -/
theorem regCount_le_of_mem {m : MInst} {ms : List MInst} {b : Nat} (hm : m ∈ ms) (h : wtL ms ≤ b) :
    regCount m ≤ b / 20 := by
  have h1 := regCount_le_szInstW m
  have h2 := szInstW_le_wtL hm
  exact (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)

/-! ## Sums -/

theorem sum_range_le {α : Type} (h : α → Nat) :
    ∀ (xs : List α) (g : Nat → Nat), (∀ j x, xs[j]? = some x → g j ≤ h x) →
      ((List.range xs.length).map g).sum ≤ (xs.map h).sum
  | [], _, _ => by simp
  | x :: xs, g, hg => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons,
      List.map_cons, List.sum_cons]
    have h1 := hg 0 x rfl
    have h2 := sum_range_le h xs (g ∘ Nat.succ) (fun j y hj => hg (j + 1) y (by simpa using hj))
    omega

theorem sum_zipIdx_zip_le {α β : Type} (F : (α × β) × Nat → Nat) (G : α × Nat → Nat) :
    ∀ (xs : List α) (ys : List β) (n : Nat),
      (∀ i x y, xs[i]? = some x → ys[i]? = some y → F ((x, y), n + i) ≤ G (x, n + i)) →
      (((xs.zip ys).zipIdx n).map F).sum ≤ ((xs.zipIdx n).map G).sum
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | x :: xs, y :: ys, n, hF => by
    simp only [List.zip_cons_cons, List.zipIdx_cons, List.map_cons, List.sum_cons]
    have h1 := hF 0 x y rfl rfl
    have h2 := sum_zipIdx_zip_le F G xs ys (n + 1) (fun i x' y' hx hy => by
      have := hF (i + 1) x' y' (by simpa using hx) (by simpa using hy)
      rwa [show n + (i + 1) = n + 1 + i by omega] at this)
    simp only [Nat.add_zero] at h1
    omega

theorem sum_zipIdx_fst {α : Type} (g : α → Nat) :
    ∀ (xs : List α) (n : Nat), ((xs.zipIdx n).map fun p => g p.1).sum = (xs.map g).sum
  | [], _ => rfl
  | x :: xs, n => by
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_zipIdx_fst g xs (n + 1)]

theorem sum_zip_le {α β : Type} (F : α × β → Nat) (G : α → Nat) :
    ∀ (xs : List α) (ys : List β), (∀ x y, (x, y) ∈ xs.zip ys → F (x, y) ≤ G x) →
      ((xs.zip ys).map F).sum ≤ (xs.map G).sum
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | x :: xs, y :: ys, hF => by
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
    have h1 := hF x y (List.mem_cons_self ..)
    have h2 := sum_zip_le F G xs ys (fun x' y' h => hF x' y' (List.mem_cons_of_mem _ h))
    omega

theorem sum_filterMap_zip_le {α β γ : Type} (W : γ → Nat) (w : Nat → Nat)
    (F : α × β → Option γ) (G : α → Option Nat)
    (hF : ∀ x y e, F (x, y) = some e → ∃ n, G x = some n ∧ W e ≤ w n) :
    ∀ (xs : List α) (ys : List β),
      (((xs.zip ys).filterMap F).map W).sum ≤ ((xs.filterMap G).map w).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | x :: xs, y :: ys => by
    have ih := sum_filterMap_zip_le W w F G hF xs ys
    simp only [List.zip_cons_cons, List.filterMap_cons]
    cases hx : F (x, y) with
    | none =>
      cases G x with
      | none => exact ih
      | some n => simp only [List.map_cons, List.sum_cons]; omega
    | some e =>
      obtain ⟨n, hn, hle⟩ := hF x y e hx
      simp only [hn, List.map_cons, List.sum_cons]
      omega

theorem sum_map_flatMap {α β : Type} (E : α → List β) (h : β → Nat) :
    ∀ l : List α, ((l.flatMap E).map h).sum = (l.map fun a => ((E a).map h).sum).sum
  | [] => rfl
  | a :: l => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      sum_map_flatMap E h l]

theorem sum_map_add {α : Type} (a b : α → Nat) :
    ∀ l : List α, (l.map fun x => a x + b x).sum = (l.map a).sum + (l.map b).sum
  | [] => rfl
  | x :: l => by simp only [List.map_cons, List.sum_cons, sum_map_add a b l]; omega

theorem sum_map_one {α : Type} : ∀ l : List α, (l.map fun _ => 1).sum = l.length
  | [] => rfl
  | _ :: l => by simp only [List.map_cons, List.sum_cons, sum_map_one l, List.length_cons]; omega

/-! ## Maxima -/

theorem foldl_max_ge_init {α : Type} (g : α → Nat) :
    ∀ (l : List α) (i : Nat), i ≤ l.foldl (fun m x => max m (g x)) i
  | [], _ => Nat.le_refl _
  | x :: l, i => Nat.le_trans (Nat.le_max_left i (g x)) (foldl_max_ge_init g l _)

theorem foldl_max_ge_mem {α : Type} (g : α → Nat) :
    ∀ (l : List α) (i : Nat) (x : α), x ∈ l → g x ≤ l.foldl (fun m x => max m (g x)) i
  | [], _, _, h => by cases h
  | y :: l, i, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right i (g x)) (foldl_max_ge_init g l _)
    · exact foldl_max_ge_mem g l _ x h

theorem foldl_le {α : Type} (M : Nat) (step : Nat → α → Nat) :
    ∀ (l : List α) (i : Nat), i ≤ M → (∀ m x, x ∈ l → m ≤ M → step m x ≤ M) →
      l.foldl step i ≤ M
  | [], _, hi, _ => hi
  | x :: l, i, hi, h =>
    foldl_le M step l _ (h i x (List.mem_cons_self ..) hi)
      (fun m y hy hm => h m y (List.mem_cons_of_mem _ hy) hm)

theorem five_le_mIn (f : Clif.Function) : 5 ≤ mIn f := foldl_max_ge_init _ _ _

/-- `mIn f` bounds a block's parameters and its runs' weight bounds over 20. -/
theorem mIn_block {f : Clif.Function} {B : Clif.Block} (hB : B ∈ f.blocks) :
    B.params.length ≤ mIn f ∧ (∀ s ∈ B.body, stmtSzB s.inst / 20 ≤ mIn f) ∧
      termSzB B.term / 20 ≤ mIn f := by
  have h := foldl_max_ge_mem (fun B : Clif.Block => max B.params.length
    (max ((B.body.map fun s => stmtSzB s.inst / 20).foldl max 0) (termSzB B.term / 20)))
    f.blocks 5 B hB
  have h2 : ∀ s ∈ B.body, stmtSzB s.inst / 20 ≤
      (B.body.map fun s => stmtSzB s.inst / 20).foldl max 0 := fun s hs =>
    foldl_max_ge_mem (fun x : Nat => x) _ 0 _ (List.mem_map_of_mem hs)
  refine ⟨Nat.le_trans (Nat.le_max_left _ _) h, fun s hs => ?_, ?_⟩
  · exact Nat.le_trans (h2 s hs) (Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_right _ _) h))
  · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) h)

theorem maxRC_le {vc : VCode} {M : Nat} (h5 : 5 ≤ M)
    (h : ∀ vb ∈ vc.blocks.toList, ∀ m ∈ vb.insts.toList, regCount m ≤ M) : maxRC vc ≤ M := by
  unfold maxRC
  rw [← Array.foldl_toList]
  refine foldl_le M _ _ _ h5 (fun m vb hvb hm => ?_)
  rw [← Array.foldl_toList]
  exact foldl_le M _ _ _ hm (fun m' i hi hm' => Nat.max_le.mpr ⟨hm', h vb hvb i hi⟩)

/-! ## The driver's own instructions -/

theorem extraOf_facts {results : List Nat} {rss : List (List Reg)} :
    ∀ m ∈ extraOf results rss, szInstW m = movW ∧ m.targets = [] ∧ regCount m = 5 := by
  intro m hm
  obtain ⟨s, a, b, rfl⟩ := mem_extraOf hm
  exact ⟨rfl, rfl, rfl⟩

theorem extraOf_length (results : List Nat) (rss : List (List Reg)) :
    (extraOf results rss).length ≤ results.length :=
  Nat.le_trans (List.length_filterMap_le _ _) (by simp [List.length_zip, Nat.min_le_left])

/-- The entry block's code before its statements: `Args` and parameter loads. -/
theorem pre_facts (f : Clif.Function) (R : Reg → Reg) {bi : Nat} {B : Clif.Block}
    (hB : f.blocks[bi]? = some B) :
    wtL (pre f R bi) ≤ (if bi = 0 then entryIn B else 0) ∧ tgL (pre f R bi) = 0 ∧
      ∀ m ∈ pre f R bi, regCount m ≤ max 5 B.params.length := by
  unfold pre
  split
  · rename_i B0 hB0
    rw [hB] at hB0
    cases hB0
    have hlen : (entryParams f B).length ≤ B.params.length := by
      simp only [entryParams, List.length_zip]; omega
    have hr : (entryRegs f R B).length ≤ B.params.length :=
      Nat.le_trans (List.length_filterMap_le _ _) hlen
    have hl : (entryLoads f R B).length ≤ B.params.length :=
      Nat.le_trans (List.length_filterMap_le _ _) hlen
    have hload : ∀ m ∈ entryLoads f R B, szInstW m = 105 ∧ m.targets = [] ∧ regCount m = 5 := by
      intro m hm
      simp only [entryLoads, List.mem_filterMap] at hm
      obtain ⟨q, -, hq⟩ := hm
      unfold entryLoadOf at hq
      split at hq
      · cases hq; exact ⟨rfl, rfl, rfl⟩
      · cases hq
    refine ⟨?_, ?_, ?_⟩
    · rw [wtL_cons]
      have h1 := wtL_le_mul (fun m hm => Nat.le_of_eq (hload m hm).1)
      have h2 : szInstW (.args (entryRegs f R B)) = 1 + 20 * (entryRegs f R B).length := by
        simp [szInstW, szWords, regCount, MInst.targets]
      simp only [↓reduceIte, entryIn]
      rw [h2]
      have := Nat.mul_le_mul_left 105 hl
      have := Nat.mul_le_mul_left 20 hr
      omega
    · simp only [tgL, List.map_cons, List.sum_cons]
      have := tgL_eq_zero (fun m hm => (hload m hm).2.1)
      simpa [tgL, MInst.targets] using this
    · intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact Nat.le_trans hr (Nat.le_max_right _ _)
      · rw [(hload m hm).2.2]; exact Nat.le_max_left _ _
  · exact ⟨Nat.zero_le _, rfl, fun m hm => by cases hm⟩

/-! ## `try_call`s -/

theorem tryInfoOf_handlers {sig : Clif.Signature} {items : List (Option Nat)} {ls : List Label}
    {info : TryInfo} (h : tryInfoOf sig items ls = some info) :
    info.handlers.length + 1 = ls.length := by
  unfold tryInfoOf at h
  split at h
  · cases h
  · rename_i hne
    cases h
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
    simp [List.length_zip]
    omega

theorem tryTargets_length {f : Clif.Function} {ds : List Clif.TryDest} {nl : Nat}
    {ls : List Label} {nl' : Nat} (h : tryTargets f ds nl = some (ls, nl')) :
    ls.length = ds.length := by
  unfold tryTargets at h
  split at h
  · cases h; simp
  · cases h

/-- `tryFix` adds a word and the `tryCall`'s targets to the weight, its targets to the branch
targets, and keeps the register operands. -/
theorem tryFix_facts (info : TryInfo) (ms : List MInst) :
    wtL (tryFix info ms) ≤ wtL ms + 1 + (info.handlers.length + 1) ∧
      tgL (tryFix info ms) ≤ tgL ms + (info.handlers.length + 1) ∧
      ∀ m ∈ tryFix info ms, ∃ m' ∈ ms, regCount m = regCount m' := by
  unfold tryFix
  split
  · rename_i c hlast
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
    rw [List.dropLast_concat]
    refine ⟨?_, ?_, ?_⟩
    · simp [szInstW, szWords, regCount, MInst.targets, wtL]
      omega
    · simp [MInst.targets, tgL]
    · intro m hm
      rcases List.mem_append.mp hm with hm | hm
      · exact ⟨m, List.mem_append_left _ hm, rfl⟩
      · rw [List.mem_singleton] at hm
        subst hm
        exact ⟨.call c, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
  · exact ⟨by omega, by omega, fun m hm => ⟨m, hm, rfl⟩⟩

theorem termIn_of_not_try {t : Clif.Terminator} (h : t.isTry = false) :
    termIn t = termSzB t ∧ tryDestsIn t = 0 := by
  cases t <;> simp_all [termIn, tryDestsIn, Clif.Terminator.isTry]

theorem termIn_of_try {t : Clif.Terminator} {et : Clif.ExnTable} (h : IsTryWith t et) :
    termIn t = termSzB t + 1 + et.dests.length ∧ tryDestsIn t = et.dests.length := by
  rcases h with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp [termIn, tryDestsIn] <;> omega

/-! ## Raw and edge blocks -/

theorem seg_eq {f : Clif.Function} {R : Reg → Reg} {bl : List BLow} {bi j : Nat} {B : Clif.Block}
    {L : BLow} {stm : Clif.Stmt} {sl : SLow} (hB : f.blocks[bi]? = some B) (hL : bl[bi]? = some L)
    (hj : B.body[j]? = some stm) (hsl : L.sl[j]? = some sl) :
    seg f R bl bi j = (sl.st'.emitted.toList ++ extraOf stm.results sl.rss).map (·.mapRegs R) := by
  unfold seg; rw [hB, hL]; simp only [hj, hsl]

theorem rawBlock_branchArgs (f : Clif.Function) (bl : List BLow) (bi : Nat) (B : Clif.Block) :
    (rawBlock f bl bi B).branchArgs.size = jumpArgsIn B.term := by
  unfold rawBlock
  cases B.term <;> simp [jumpArgsIn]

/-- The edge blocks of a block, summed by any measure bounded per branch-argument count. -/
theorem edges_le {f : Clif.Function} {B : Clif.Block} {L : BLow} (W : VBlock → Nat)
    (w : Nat → Nat) (hW : ∀ e tl, e.insts = #[.jump tl] → W e ≤ w e.branchArgs.size) :
    ((edgeBlocks f B L).map W).sum ≤ ((edgeArgsIn B.term).map w).sum := by
  have hbr : ∀ bcs : List Clif.BlockCall, ∀ ls : List Label,
      ((((bcs.zip ls).filterMap fun (p : Clif.BlockCall × Label) =>
        if p.1.args.isEmpty then none else (blockIdx? f p.1.block).map fun tl =>
          ({ label := p.2, insts := #[.jump tl],
             branchArgs := (p.1.args.map fun a => Reg.vreg a .int).toArray } : VBlock))).map W).sum ≤
        ((bcs.filterMap fun bc => if bc.args.isEmpty then none else some bc.args.length).map w).sum :=
    sum_filterMap_zip_le W w _ _ (fun bc l e he => by
      simp only at he
      split at he
      · cases he
      · rename_i hne
        simp only [Option.map_eq_some_iff] at he
        obtain ⟨tl, -, rfl⟩ := he
        refine ⟨bc.args.length, by simp [hne], ?_⟩
        exact Nat.le_trans (hW _ tl rfl) (by simp))
  have htry : ∀ (et : Clif.ExnTable) (T : TryLow),
      ((((et.dests.zip L.targets).filterMap fun (x : Clif.TryDest × Label) => match x with
        | (td, l) => (blockIdx? f td.block).map fun tl =>
          ({ label := l, insts := #[.jump tl],
             branchArgs := (td.args.map (tryEdgeArg T.regs.1 T.regs.2)).toArray } : VBlock))).map W).sum ≤
        ((et.dests.map (·.args.length)).map w).sum := by
    intro et T
    refine Nat.le_trans (sum_filterMap_zip_le W w _ (fun td : Clif.TryDest => some td.args.length)
      (fun td l e he => ?_) et.dests L.targets) (Nat.le_of_eq ?_)
    · simp only [Option.map_eq_some_iff] at he
      obtain ⟨tl, -, rfl⟩ := he
      exact ⟨_, rfl, Nat.le_trans (hW _ tl rfl) (by simp)⟩
    · simp
  unfold edgeBlocks
  split
  · rename_i ht _
    rw [ht]; exact htry _ _
  · rename_i ht _
    rw [ht]; exact htry _ _
  · simp
  · rename_i hj _ _
    refine Nat.le_trans (hbr (dests B.term) L.targets) ?_
    cases h : B.term with
    | jump bc => exact (hj bc h).elim
    | _ => simp [dests, edgeArgsIn]

/-! ## `lowerFunction`'s output -/

/-- **The size of `lowerFunction`'s output from the ISLE runs**: given the driver's contract
`IselSz f`, every instruction of `lowerFunction f`'s VCode has at most `mIn f` register operands,
its weight (with `mIn f` bounding the operands) is at most `vcIn (mIn f) f`, and its branch
targets at most `tgIn f`. -/
theorem size_lower {f : Clif.Function} {vc : VCode} (hI : IselSz f)
    (hl : lowerFunction f = .ok vc) :
    maxRC vc ≤ mIn f ∧ vcW (mIn f) vc ≤ vcIn (mIn f) f ∧ vcTg vc ≤ tgIn f := by
  obtain ⟨ctx, ranges, st0, bl, hb, hlb, hvb, -, -⟩ := lowerFunction_run hl
  obtain ⟨hS, hT, hY⟩ := hI ctx ranges st0 hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  have hemp := lowBlocks_emptied hlb
  -- a statement's segment: its run (from nothing emitted) and the result `mov`s
  have hseg : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (j : Nat) (stm : Clif.Stmt) (sl : SLow),
      f.blocks[bi]? = some B → bl[bi]? = some L → B.body[j]? = some stm →
      L.sl[j]? = some sl →
      wtL (sl.st'.emitted.toList ++ extraOf stm.results sl.rss) ≤ stmtIn stm ∧
      tgL (sl.st'.emitted.toList ++ extraOf stm.results sl.rss) = 0 ∧
      ∀ m ∈ sl.st'.emitted.toList ++ extraOf stm.results sl.rss, regCount m ≤ mIn f := by
    intro bi B L j stm sl hB hL hj hsl
    obtain ⟨-, hc, -, -⟩ := hspec bi B L hB hL
    obtain ⟨info, hi, hic, -⟩ := hcf.stmt bi B j stm hB hj
    obtain ⟨tr, hrun⟩ := hc j sl hsl
    rw [hstart bi L hL] at hrun
    obtain ⟨hw, htg⟩ := hS _ info stm.inst _ _ _ _ hi hic hrun
    rw [hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)] at hw htg
    have hw' : wtL sl.st'.emitted.toList ≤ stmtSzB stm.inst :=
      Nat.le_trans hw (Nat.le_of_eq (Nat.zero_add _))
    have htg' : tgL sl.st'.emitted.toList = 0 := Nat.le_zero.mp htg
    have hmax := (mIn_block (List.mem_of_getElem? hB)).2.1 stm (List.mem_of_getElem? hj)
    have hx := extraOf_facts (results := stm.results) (rss := sl.rss)
    refine ⟨?_, ?_, ?_⟩
    · rw [wtL_append]
      have h1 := wtL_le_mul (fun m hm => Nat.le_of_eq (hx m hm).1)
      have h2 := Nat.mul_le_mul_left movW (extraOf_length stm.results sl.rss)
      unfold stmtIn
      omega
    · rw [tgL_append, tgL_eq_zero (fun m hm => (hx m hm).2.1), htg']
    · intro m hm
      rcases List.mem_append.mp hm with hm | hm
      · exact Nat.le_trans (regCount_le_of_mem hm hw') hmax
      · rw [(hx m hm).2.2]; exact five_le_mIn f
  -- the terminator's segment: its run, and a `try_call`'s `tryCall`
  have hterm : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B →
      bl[bi]? = some L →
      wtL (fixTry L.tl L.tst'.emitted.toList) ≤ termIn B.term ∧
      tgL (fixTry L.tl L.tst'.emitted.toList) ≤ termTgB B.term + tryDestsIn B.term ∧
      ∀ m ∈ fixTry L.tl L.tst'.emitted.toList, regCount m ≤ mIn f := by
    intro bi B L hB hL
    obtain ⟨-, -, htst, nl0, nl', hlt⟩ := hspec bi B L hB hL
    obtain ⟨hn, hy⟩ := lowTerm_spec hlt
    have hph := hcf.term bi B hB
    rw [← hstart bi L hL] at hph
    have hti := (Array.getElem?_eq_some_iff.mp hph).1
    have hmax := (mIn_block (List.mem_of_getElem? hB)).2.2
    cases ht : B.term.isTry with
    | false =>
      obtain ⟨htl, hd, out, tr, hc⟩ := hn ht
      obtain ⟨hw, htg⟩ := hT _ _ _ _ _ _ _ _ hti hph ht hd hc
      rw [htst] at hw htg
      have hw' : wtL L.tst'.emitted.toList ≤ termSzB B.term :=
        Nat.le_trans hw (Nat.le_of_eq (Nat.zero_add _))
      have htg' : tgL L.tst'.emitted.toList ≤ termTgB B.term :=
        Nat.le_trans htg (Nat.le_of_eq (Nat.zero_add _))
      obtain ⟨hi1, hi2⟩ := termIn_of_not_try ht
      rw [htl, hi1, hi2]
      simp only [fixTry, Nat.add_zero]
      exact ⟨hw', htg', fun m hm => Nat.le_trans (regCount_le_of_mem hm hw') hmax⟩
    | true =>
      obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := by
        cases hB' : B.term <;> rw [hB'] at ht <;> simp [Clif.Terminator.isTry] at ht
        · exact ⟨_, .inl ⟨_, _, rfl⟩⟩
        · exact ⟨_, .inr ⟨_, _, rfl⟩⟩
      obtain ⟨T, hT', hd, -, htt, -, hi, out, tr, hc⟩ := hy et het
      obtain ⟨hw, htg⟩ := hY _ _ _ _ _ _ _ _ _ hti hph hd hc
      have hw' : wtL L.tst'.emitted.toList ≤ termSzB B.term :=
        Nat.le_trans hw (Nat.le_of_eq (Nat.zero_add _))
      have htg' : tgL L.tst'.emitted.toList ≤ termTgB B.term :=
        Nat.le_trans htg (Nat.le_of_eq (Nat.zero_add _))
      obtain ⟨hi1, hi2⟩ := termIn_of_try het
      have hlen : T.info.handlers.length + 1 = et.dests.length := by
        rw [tryInfoOf_handlers hi, tryTargets_length htt]
      obtain ⟨f1, f2, f3⟩ := tryFix_facts T.info L.tst'.emitted.toList
      rw [hT', hi1, hi2]
      simp only [fixTry]
      refine ⟨by omega, by omega, fun m hm => ?_⟩
      obtain ⟨m', hm', he⟩ := f3 m hm
      rw [he]
      exact Nat.le_trans (regCount_le_of_mem hm' hw') hmax
  -- a raw block
  have hraw : ∀ (R : Reg → Reg) (bi : Nat) (B : Clif.Block) (L : BLow),
      f.blocks[bi]? = some B → bl[bi]? = some L →
      vbW (mIn f) (fixBlock R (rawBlock f bl bi B)) ≤ blockIn (mIn f) bi B ∧
      tgA (fixBlock R (rawBlock f bl bi B)).insts ≤ termTgB B.term + tryDestsIn B.term ∧
      ∀ m ∈ (fixBlock R (rawBlock f bl bi B)).insts.toList, regCount m ≤ mIn f := by
    intro R bi B L hB hL
    have hins : (fixBlock R (rawBlock f bl bi B)).insts.toList = pre f R bi ++
        ((List.range B.body.length).map (seg f R bl bi)).flatten ++ tseg R bl bi :=
      rawBlock_insts f R bl bi B
    obtain ⟨hpar, -, -⟩ := mIn_block (List.mem_of_getElem? hB)
    obtain ⟨p1, p2, p3⟩ := pre_facts f R hB
    obtain ⟨hsl, -, -, -⟩ := hspec bi B L hB hL
    have hsegE : ∀ j stm, B.body[j]? = some stm → ∃ sl, L.sl[j]? = some sl ∧
        seg f R bl bi j = (sl.st'.emitted.toList ++ extraOf stm.results sl.rss).map (·.mapRegs R) := by
      intro j stm hj
      have hjl : j < L.sl.length := by rw [hsl]; exact (List.getElem?_eq_some_iff.mp hj).1
      exact ⟨L.sl[j], List.getElem?_eq_getElem hjl, seg_eq hB hL hj (List.getElem?_eq_getElem hjl)⟩
    have hts : tseg R bl bi = (fixTry L.tl L.tst'.emitted.toList).map (·.mapRegs R) := by
      unfold tseg; rw [hL]
    obtain ⟨t1, t2, t3⟩ := hterm bi B L hB hL
    have s1 : ((List.range B.body.length).map (wtL ∘ seg f R bl bi)).sum ≤ (B.body.map stmtIn).sum :=
      sum_range_le stmtIn B.body _ (fun j stm hj => by
        obtain ⟨sl, hsl', he⟩ := hsegE j stm hj
        show wtL (seg f R bl bi j) ≤ _
        rw [he, wtL_map_mapRegs]; exact (hseg bi B L j stm sl hB hL hj hsl').1)
    have s2 : ((List.range B.body.length).map (tgL ∘ seg f R bl bi)).sum ≤
        (B.body.map fun _ => 0).sum :=
      sum_range_le _ B.body _ (fun j stm hj => by
        obtain ⟨sl, hsl', he⟩ := hsegE j stm hj
        show tgL (seg f R bl bi j) ≤ _
        rw [he, tgL_map_mapRegs]; exact Nat.le_of_eq (hseg bi B L j stm sl hB hL hj hsl').2.1)
    have s2' : (B.body.map fun _ => (0 : Nat)).sum = 0 := by
      clear s2; induction B.body with
      | nil => rfl
      | cons _ _ ih => simp only [List.map_cons, List.sum_cons, ih]
    refine ⟨?_, ?_, ?_⟩
    · have hba : (fixBlock R (rawBlock f bl bi B)).branchArgs.size = jumpArgsIn B.term := by
        simp only [fixBlock, Array.size_map]; exact rawBlock_branchArgs f bl bi B
      unfold vbW blockIn
      rw [show wtA (fixBlock R (rawBlock f bl bi B)).insts =
        wtL (fixBlock R (rawBlock f bl bi B)).insts.toList from rfl, hins, wtL_append, wtL_append,
        wtL_flatten, List.map_map, hts, wtL_map_mapRegs, hba]
      omega
    · rw [show tgA (fixBlock R (rawBlock f bl bi B)).insts =
        tgL (fixBlock R (rawBlock f bl bi B)).insts.toList from rfl, hins, tgL_append, tgL_append,
        tgL_flatten, List.map_map, hts, tgL_map_mapRegs]
      omega
    · intro m hm
      rw [hins] at hm
      rcases List.mem_append.mp hm with hm | hm
      · rcases List.mem_append.mp hm with hm | hm
        · exact Nat.le_trans (p3 m hm) (Nat.max_le.mpr ⟨five_le_mIn f, hpar⟩)
        · simp only [List.mem_flatten, List.mem_map, List.mem_range] at hm
          obtain ⟨sg, ⟨j, hj, rfl⟩, hm⟩ := hm
          obtain ⟨sl, hsl', he⟩ := hsegE j B.body[j] (List.getElem?_eq_getElem hj)
          rw [he, List.mem_map] at hm
          obtain ⟨m1, hm1, rfl⟩ := hm
          rw [regCount_mapRegs]
          exact (hseg bi B L j _ sl hB hL (List.getElem?_eq_getElem hj) hsl').2.2 m1 hm1
      · rw [hts, List.mem_map] at hm
        obtain ⟨m1, hm1, rfl⟩ := hm
        rw [regCount_mapRegs]
        exact t3 m1 hm1
  -- the edge blocks of a block
  have hedge : ∀ (R : Reg → Reg) (B : Clif.Block) (L : BLow),
      ((edgeBlocks f B L).map fun e => vbW (mIn f) (fixBlock R e)).sum ≤
        ((edgeArgsIn B.term).map (edgeIn (mIn f))).sum ∧
      ((edgeBlocks f B L).map fun e => tgA (fixBlock R e).insts).sum ≤ (edgeArgsIn B.term).length := by
    intro R B L
    refine ⟨edges_le _ _ (fun e tl he => ?_), ?_⟩
    · simp [vbW, edgeIn, fixBlock, he, wtA, wtL, MInst.mapRegs, szInstW, szWords, regCount,
        MInst.targets]
    · rw [← sum_map_one]
      exact edges_le _ _ (fun e tl he => by simp [fixBlock, he, tgA, tgL, MInst.mapRegs, MInst.targets])
  -- `vcBlocksOf`: the raw blocks, then the edge blocks
  have hsplit : ∀ g : VBlock → Nat, (vc.blocks.toList.map g).sum =
      ((f.blocks.zip bl).zipIdx.map fun p => g (fixBlock (lowerFunction.resolve
        (aliasArr (aliasOf f bl)) ((aliasArr (aliasOf f bl)).size + 1)) (rawBlock f bl p.2 p.1.1))).sum +
      ((f.blocks.zip bl).map fun p => ((edgeBlocks f p.1 p.2).map fun e => g (fixBlock
        (lowerFunction.resolve (aliasArr (aliasOf f bl)) ((aliasArr (aliasOf f bl)).size + 1)) e)).sum).sum := by
    intro g
    rw [hvb]
    simp only [vcBlocksOf, List.toList_toArray, List.map_append, List.sum_append, List.map_map,
      sum_map_flatMap]
    rfl
  refine ⟨maxRC_le (five_le_mIn f) (fun vb hvb' m hm => ?_), ?_, ?_⟩
  · rw [hvb] at hvb'
    obtain ⟨R, -, ⟨bi, B, L, hB, hL, rfl⟩ | ⟨B, L, e, -, he, rfl⟩⟩ := mem_vcBlocksOf hvb'
    · exact (hraw R bi B L hB hL).2.2 m hm
    · obtain ⟨tl, hi⟩ := edgeBlocks_insts he
      simp [fixBlock, hi, MInst.mapRegs] at hm
      subst hm
      exact five_le_mIn f
  · unfold vcW vcIn
    rw [hsplit]
    refine Nat.add_le_add (sum_zipIdx_zip_le _ _ f.blocks bl 0 (fun i B L hB hL => ?_))
      (sum_zip_le _ (fun B => ((edgeArgsIn B.term).map (edgeIn (mIn f))).sum) f.blocks bl
        (fun B L _ => (hedge _ B L).1))
    simp only [Nat.zero_add]
    exact (hraw _ i B L hB hL).1
  · unfold vcTg
    rw [hsplit]
    have htg : tgIn f = (f.blocks.map fun B => termTgB B.term + tryDestsIn B.term).sum +
        (f.blocks.map fun B => (edgeArgsIn B.term).length).sum := by
      unfold tgIn; exact sum_map_add _ _ _
    rw [htg, ← sum_zipIdx_fst (fun B => termTgB B.term + tryDestsIn B.term) f.blocks 0]
    refine Nat.add_le_add (sum_zipIdx_zip_le _ _ f.blocks bl 0 (fun i B L hB hL => ?_))
      (sum_zip_le _ (fun B => (edgeArgsIn B.term).length) f.blocks bl
        (fun B L _ => (hedge _ B L).2))
    simp only [Nat.zero_add]
    exact (hraw _ i B L hB hL).2.1
