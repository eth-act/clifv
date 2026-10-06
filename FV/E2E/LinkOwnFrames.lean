import Lean
import FV.E2E.LinkOwnFramesDefs
import FV.Backend.Proof.LowerComplete
import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.DriverCheckSound
import FV.Backend.Proof.PrepareComplete
import FV.Backend.Proof.LowerLoopSim
import FV.Backend.Proof.RegallocLayout
import FV.E2E.RegLevelEmit

/-! # The frame checks of `okB`, proven for every in-scope function (docs/TO-PROVE.md §3, L2)

`okB` (`FV/E2E/LinkCheck.lean`) checks per function `g` with artifacts `a`:

* "outFits": the stack-passed parameters of every callee of `g` in the program fit `g`'s outgoing
  argument area (`intBase`). `outFits_of_lower` proves it from the input condition `outScopeB`
  (`FV/E2E/LinkOwnFramesDefs.lean`): the lowering's outgoing area holds the stack arguments of
  every extern `g` calls directly (`CallsStack`, `TryStack`), which `intBase` rounds up.
* "calleeFrame/slotFits": a function without CLIF slots has no slot region (the allocator's frame
  is the whole frame), and every slot lies inside the frame at its `slotLayout` offset above
  `slotBase`. `frame_of_lower` proves both for every output of the pipeline: `lowerRFunc` places
  the slot region at `slotBase = size` and rounds `size + slotBytes` up to the frame size, and
  `slotBytes` is `slotLayout`'s end, past every slot (`slotLayout_fits`; `slotLayout` sorts the
  slots with core's `Array.qsort`, a permutation: `mem_qsort`).
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

/-! ## `Array.qsort` keeps its elements -/

open Lean Elab Term Meta in
/-- Core's private `Array.qpartition.loop` / `Array.qsort.sort` (and their `eq_def`s), by name
relative to `Init.Data.Array.QSort.Basic`'s private prefix. -/
elab "qs_priv% " s:str : term => do
  let base := Name.mkNum `_private.Init.Data.Array.QSort.Basic 0
  let n := s.getString.splitOn "." |>.foldl (fun n c => Name.mkStr n c) base
  mkConstWithFreshMVarLevels n

theorem qpartition_loop_perm {α : Type} {n : Nat} (lt : α → α → Bool) (lo hi : Nat) (hhi : hi < n)
    (pivot : α) :
    ∀ (m : Nat) (as : Vector α n) (i k : Nat) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi), hi - k = m →
      ((qs_priv% "Array.qpartition.loop") lt lo hi hhi pivot as i k ilo ik w).2.Perm as := by
  intro m
  induction m with
  | zero =>
    intro as i k ilo ik w hm
    rw [(qs_priv% "Array.qpartition.loop.eq_def")]
    split
    · omega
    · exact Vector.swap_perm (by omega) (by omega)
  | succ m ih =>
    intro as i k ilo ik w hm
    rw [(qs_priv% "Array.qpartition.loop.eq_def")]
    split
    · split
      · exact (ih _ _ _ _ _ _ (by omega)).trans (Vector.swap_perm (by omega) (by omega))
      · exact ih _ _ _ _ _ _ (by omega)
    · omega

theorem ite_swap_perm {α : Type} {n : Nat} {c : Prop} [Decidable c] {xs : Vector α n} {i j : Nat}
    {h1 : i < n} {h2 : j < n} : (if c then xs.swap i j h1 h2 else xs).Perm xs := by
  split
  · exact Vector.swap_perm h1 h2
  · exact .rfl

theorem qpartition_perm {α : Type} {n : Nat} (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat)
    (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    (Array.qpartition as lt lo hi w hlo hhi).2.Perm as := by
  unfold Array.qpartition
  dsimp only
  exact (qpartition_loop_perm _ _ _ _ _ _ _ _ _ _ _ _ rfl).trans
    (ite_swap_perm.trans (ite_swap_perm.trans ite_swap_perm))

theorem qsort_sort_perm {α : Type} (lt : α → α → Bool) {n : Nat} :
    ∀ (m : Nat) (as : Vector α n) (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n),
      hi - lo ≤ m → ((qs_priv% "Array.qsort.sort") lt as lo hi w hlo hhi).Perm as := by
  intro m
  induction m with
  | zero =>
    intro as lo hi w hlo hhi hm
    rw [(qs_priv% "Array.qsort.sort.eq_def")]
    split
    · omega
    · exact .rfl
  | succ m ih =>
    intro as lo hi w hlo hhi hm
    rw [(qs_priv% "Array.qsort.sort.eq_def")]
    split
    · have hq := qpartition_perm as lt lo hi w hlo hhi
      revert hq
      split
      rename_i mid hmid as' heq
      intro hq
      rw [heq] at hq
      split
      · exact hq
      · exact ((ih _ _ _ _ _ _ (by omega)).trans (ih _ _ _ _ _ _ (by omega))).trans hq
    · exact .rfl

/-- `Array.qsort` keeps every element. -/
theorem mem_qsort {α : Type} {as : Array α} {lt : α → α → Bool} {x : α} (hx : x ∈ as) :
    x ∈ as.qsort lt := by
  unfold Array.qsort
  split
  · exact hx
  · dsimp only
    refine (Vector.Perm.toArray
      (qsort_sort_perm lt _ as.toVector _ _ _ _ _ (Nat.le_refl _))).mem_iff.2 ?_
    simpa using hx

/-! ## `slotLayout` places every slot below its end -/

theorem mem_of_lookup {k v : Nat} {l : List (Nat × Nat)} (h : l.lookup k = some v) : (k, v) ∈ l := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.1 h
  simp

theorem alignTo_ge (n a : Nat) (ha : 0 < a) : n ≤ alignTo n a := by
  unfold alignTo
  have := Nat.div_add_mod (n + a - 1) a
  have := Nat.mod_lt (n + a - 1) ha
  have : (n + a - 1) / a * a = a * ((n + a - 1) / a) := Nat.mul_comm _ _
  omega

/-- A fold placing each slot at or past the running end (`slotLayout`'s) keeps every slot placed
so far inside `[0, end)` at the offset `lookup` finds for its id (the first entry of the id,
which is at most the slot's own offset: offsets only grow). -/
theorem slotFold_fits (f : Array (Nat × Nat) × Nat → Nat × Clif.StackSlot → Array (Nat × Nat) × Nat)
    (hf : ∀ st p, ∃ start, st.2 ≤ start ∧ f st p = (st.1.push (p.1, start), start + p.2.size)) :
    ∀ (l : List (Nat × Clif.StackSlot)) (st : Array (Nat × Nat) × Nat)
      (done : List (Nat × Clif.StackSlot)),
      (∀ q ∈ st.1.toList, q.2 ≤ st.2) →
      (∀ p ∈ done, ∃ off, st.1.toList.lookup p.1 = some off ∧ off + p.2.size ≤ st.2) →
      ∀ r, l.foldl f st = r → ∀ p ∈ done ++ l,
        ∃ off, r.1.toList.lookup p.1 = some off ∧ off + p.2.size ≤ r.2 := by
  intro l
  induction l with
  | nil =>
    intro st done _ h2 r hr p hp
    subst hr
    simp only [List.append_nil] at hp
    exact h2 p hp
  | cons a l ih =>
    intro st done h1 h2 r hr p hp
    obtain ⟨start, hle, hst⟩ := hf st a
    rw [List.foldl_cons, hst] at hr
    refine ih _ (done ++ [a]) ?_ ?_ r hr p (by simpa using hp)
    · intro q hq
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | rfl
      · have := h1 q hq; dsimp only; omega
      · dsimp only; omega
    · intro p hp
      simp only [Array.toList_push]
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · obtain ⟨off, hl, ho⟩ := h2 p hp
        exact ⟨off, by rw [List.lookup_append, hl]; rfl, by omega⟩
      · cases hl : st.1.toList.lookup p.1 with
        | some off =>
          have := h1 _ (mem_of_lookup hl)
          exact ⟨off, by rw [List.lookup_append, hl]; rfl, by omega⟩
        | none =>
          refine ⟨start, ?_, Nat.le_refl _⟩
          rw [List.lookup_append, hl]
          simp

/-- **Every slot lies below `slotLayout`'s end**, at the offset `slotLayout` gives its id. -/
theorem slotLayout_fits (slots : List (Nat × Clif.StackSlot)) :
    ∀ p ∈ slots, ∃ off, (slotLayout slots).1.lookup p.1 = some off ∧
      off + p.2.size ≤ (slotLayout slots).2 := by
  intro p hp
  have hm : p ∈ (slots.toArray.qsort (fun a b => a.1 < b.1)).toList :=
    Array.mem_toList_iff.2 (mem_qsort (List.mem_toArray.2 hp))
  unfold slotLayout
  dsimp only
  exact slotFold_fits _ (fun _ _ => ⟨_, alignTo_ge _ _ (by omega), rfl⟩) _ (#[], 0) []
    (by simp) (by simp) _ rfl p (by simpa using hm)

/-! ## The VCode's slot region and outgoing area -/

/-- `lowerFunction`'s slot region is `slotLayout`'s, and `prepare` keeps it. -/
theorem slotBytes_of_lower {g : Clif.Function} {vc vcp : VCode} (hl : lowerFunction g = .ok vc)
    (hp : prepare vc = .ok vcp) : vcp.slotBytes = (slotLayout g.slots).2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hvcp⟩ := Prep.prepare_facts hp
  obtain ⟨_, _, _, _, d, _, _, _, _, hvc⟩ := loop_run hl
  rw [hvcp]
  dsimp only
  rw [hvc]
  rfl

/-- `prepare` keeps the outgoing argument area. -/
theorem outgoing_of_prepare {vc vcp : VCode} (hp : prepare vc = .ok vcp) :
    vcp.outgoing = vc.outgoing := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hvcp⟩ := Prep.prepare_facts hp
  rw [hvcp]

/-! ## outFits -/

theorem outFitsB_mono {sig : Clif.Signature} {a b : Nat} (h : outFitsB sig a = true)
    (hab : a ≤ b) : outFitsB sig b = true := by
  unfold outFitsB at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro i hi
  have hi' := h i hi
  revert hi'
  cases (locsOf sig)[i]? with
  | none => simp
  | some l =>
    cases l with
    | reg r => simp
    | stack off =>
      cases sig.params[i]? with
      | none => simp
      | some p => simp only [decide_eq_true_eq]; omega

/-- The externs `g` calls directly fit an outgoing area holding the stack arguments of its
`call`s and `try_call`s. -/
theorem callStack_le {g : Clif.Function} {out : Nat} (hc : CallsStack g out)
    (ht : TryStack g out) : callStack g ≤ out := by
  unfold callStack
  suffices hall : ∀ fn ∈ calledRefs g, (((g.extern? fn).map fun e => stackBytes e.sig).getD 0) ≤ out by
    generalize calledRefs g = l at hall ⊢
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.foldr_cons]
      exact Nat.max_le.2 ⟨ih (fun fn h => hall fn (.tail _ h)), hall a (.head _)⟩
  intro fn hfn
  cases he : g.extern? fn with
  | none => simp
  | some e =>
    simp only [Option.map_some, Option.getD_some]
    unfold calledRefs at hfn
    simp only [List.mem_flatMap, List.mem_append, List.mem_filterMap] at hfn
    obtain ⟨B, hB, h | h⟩ := hfn
    · obtain ⟨st, hst, hm⟩ := h
      split at hm
      · rename_i fn' args heq
        cases hm
        exact (hc B hB st hst fn args e heq he).1
      · cases hm
    · split at h
      · rename_i fn' args et heq
        simp only [List.mem_singleton] at h
        subst h
        exact (ht B hB _ _ _ heq e he).1
      · simp at h

/-- **okB's "outFits"**, for every in-scope function satisfying the input condition
`outScopeB`. -/
theorem outFits_of_lower {P : Clif.Program} {g : Clif.Function} {vc vcp : VCode}
    (hd : dominatedB g = true) (hs : lowerScopeB g = true) (hos : outScopeB P g = true)
    (hl : lowerFunction g = .ok vc) (hp : Backend.prepare vc = .ok vcp) (rf : RFunc) :
    g.externs.all (fun e => !(P.func? e.2.name).isSome ||
      outFitsB e.2.sig (RAFrame.compute vcp rf).intBase) = true := by
  have hck := lowerCheck_complete (dominated_of hd) (lowerScope_of hs) hl
  have hle : callStack g ≤ (RAFrame.compute vcp rf).intBase := by
    show callStack g ≤ alignTo vcp.outgoing 16
    rw [outgoing_of_prepare hp]
    exact Nat.le_trans (callStack_le (callsStack_of_check hck) (tryStack_of_check hck))
      (alignTo_ge _ 16 (by decide))
  unfold outScopeB at hos
  rw [List.all_eq_true] at hos ⊢
  intro e he
  have := hos e he
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at this ⊢
  rcases this with h | h
  · exact .inl h
  · exact .inr (outFitsB_mono h hle)

/-! ## calleeFrame/slotFits -/

/-- **okB's "calleeFrame/slotFits"**, for every output of the pipeline. -/
theorem frame_of_lower {g : Clif.Function} {a : Art} (hl : lowerFunction g = .ok a.vc)
    (hp : Backend.prepare a.vc = .ok a.vcp) (hr : lowerRFunc a.vcp a.rf = .ok a.af) :
    ((!g.slots.isEmpty || (RAFrame.compute a.vcp a.rf).size == a.af.frameSize) &&
      slotFitsB g a) = true := by
  obtain ⟨hfs, hsb, -⟩ := lowerRFunc_ok hr
  obtain ⟨hfs, hsb, -⟩ := hfs
  have hsl := slotBytes_of_lower hl hp
  have htot : (RAFrame.compute a.vcp a.rf).total =
      alignTo ((RAFrame.compute a.vcp a.rf).size + a.vcp.slotBytes) 16 := rfl
  rw [Bool.and_eq_true]
  constructor
  · cases hs : g.slots with
    | cons _ _ => simp
    | nil =>
      have h0 : a.vcp.slotBytes = 0 := by rw [hsl, hs]; rfl
      have hm : (RAFrame.compute a.vcp a.rf).size % 16 = 0 := alignTo16_mod _
      simp only [List.isEmpty_nil, Bool.not_true, Bool.false_or, beq_iff_eq]
      rw [hfs, htot, h0]
      unfold alignTo
      omega
  · unfold slotFitsB
    rw [List.all_eq_true]
    intro p hp
    obtain ⟨off, hlk, hle⟩ := slotLayout_fits g.slots p hp
    simp only [hlk, decide_eq_true_eq]
    rw [hfs, hsb, htot, hsl]
    have := alignTo_ge ((RAFrame.compute a.vcp a.rf).size + (slotLayout g.slots).2) 16 (by decide)
    omega

end E2E.LinkCheck
