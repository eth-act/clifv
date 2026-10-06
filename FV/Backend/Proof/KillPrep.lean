import FV.Backend.Proof.SpillAvail
import FV.Backend.Proof.PrepareSound
import FV.Backend.Proof.SpillEdges
import FV.Backend.Proof.SpillStep4Cfg

/-!
# `killFreeB` across `prepare` (V4 step 4, `SpillKillFree`)

`killFreeB_prepare`: on `lowerFunction`'s VCode (`LowOk`), `prepare` keeps `Spill.killFreeB`.
`prepare` drops unreachable blocks, retargets terminators (`MInst.setTargets`, which keeps
operands, clobbers, `isTerminator`, `keptDefs`, `normalDead`), adds edge blocks `jump l` (no
operands) and reorders the blocks. So the killed vregs of the output are killed in the input and
every use of the output is one of the input. A block of the output with a killed branch argument
is a block of the input (edge blocks have no branch arguments) whose only predecessor edge comes
from a `try_call` (the only terminator with defs live on an edge); that edge is not split (its
target has one predecessor edge, `NoSplit`), so in the output the block's only predecessor is the
retargeted `try_call` block (`EdgesOk.tryEdge`), at the same successor index.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof

namespace KillPrep

/-! ## Retargeting keeps the instruction facts -/

theorem setTargets_inv {i i' : MInst} {ls : List Label} (h : i.setTargets ls = some i') :
    i'.operands = i.operands ∧ i'.clobbers = i.clobbers ∧ i'.isTerminator = i.isTerminator ∧
      i'.keptDefs = i.keptDefs ∧ i'.normalDead = i.normalDead := by
  refine ⟨(Driver.setTargets_facts h).1, ?_⟩
  unfold MInst.setTargets at h
  split at h
  all_goals (try split at h)
  all_goals (try (cases h; done))
  all_goals (cases h)
  all_goals (try exact ⟨rfl, rfl, rfl, rfl⟩)
  rename_i hl
  simp only [beq_iff_eq] at hl
  refine ⟨rfl, rfl, rfl, ?_⟩
  simp [MInst.normalDead, hl]

theorem sameInst_inv {i i' : MInst} (h : Driver.SameInst i i') :
    i'.operands = i.operands ∧ i'.clobbers = i.clobbers ∧ i'.isTerminator = i.isTerminator ∧
      i'.keptDefs = i.keptDefs ∧ i'.normalDead = i.normalDead := by
  rcases h with rfl | h
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact setTargets_inv h

theorem unstored_same {i i' : MInst} (h : Driver.SameInst i i') : unstored i' = unstored i := by
  obtain ⟨h1, -, h3, h4, -⟩ := sameInst_inv h
  simp only [unstored, storedDefs, h1, h3, h4]

theorem useVregs_same {i i' : MInst} (h : Driver.SameInst i i') : useVregs i' = useVregs i := by
  obtain ⟨h1, -⟩ := sameInst_inv h
  simp only [useVregs, h1]

theorem unstored_jump (l : Label) : unstored (.jump l) = [] := rfl

theorem useVregs_jump (l : Label) : useVregs (.jump l) = [] := rfl

theorem termEdgeDefs_same {vb vb' : VBlock} {t t' : MInst} (ht : vb.insts.back? = some t)
    (ht' : vb'.insts.back? = some t') (hs : Driver.SameInst t t') (j : Nat) :
    termEdgeDefs vb' j = termEdgeDefs vb j := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sameInst_inv hs
  simp only [termEdgeDefs, ht, ht', keptPairs, h1, h2, h3, h4, h5]

theorem setTargets_tryCall {info : CallInfo} {ti : TryInfo} {ls : List Label} {i' : MInst}
    (h : (MInst.tryCall info ti).setTargets ls = some i') : ∃ ti', i' = .tryCall info ti' := by
  simp only [MInst.setTargets] at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · cases h

/-- A terminator with defs live on an edge is a `try_call`. -/
theorem tryCall_of_termEdgeDefs {vb : VBlock} {t : MInst} {j : Nat} (ht : vb.insts.back? = some t)
    (hne : termEdgeDefs vb j ≠ []) (htg : t.targets ≠ []) : ∃ info ti, t = .tryCall info ti := by
  have hb : t.isBranch = false := by
    cases hbr : t.isBranch
    · rfl
    · exfalso; apply hne
      have hk : t.keptDefs = some 0 := by
        unfold MInst.keptDefs; split
        · simp [MInst.isBranch] at hbr
        · simp [MInst.isBranch] at hbr
        · simp [hbr]
      unfold termEdgeDefs
      rw [ht]
      simp only
      split
      · rfl
      split
      · rfl
      simp only [keptPairs, hk, List.take_zero]
      split <;> simp
  clear hne ht
  cases t <;> simp_all [MInst.isBranch, MInst.targets]

/-! ## Entry stores -/

theorem entryStored_one {vc : VCode} {succs preds : Array (Array Nat)} {s b : Nat}
    (hp : preds[s]? = some #[b]) :
    entryStored vc succs preds s =
      match vc.blocks[b]?, succs[b]? with
      | some vb, some ss =>
        match List.idxOf? s ss.toList with
        | some j => (termEdgeDefs vb j).map (·.1.vreg)
        | none => []
      | _, _ => [] := by
  unfold entryStored; rw [hp]; rfl

theorem entryStored_ne {vc : VCode} {succs preds : Array (Array Nat)} {s : Nat}
    (hn : ∀ b, preds[s]? ≠ some #[b]) : entryStored vc succs preds s = [] := by
  unfold entryStored
  rcases hp : preds[s]? with _ | ⟨_ | ⟨b, _ | ⟨b', l⟩⟩⟩
  · rfl
  · rfl
  · exact absurd hp (hn b)
  · rfl

theorem entryStored_inv {vc : VCode} {succs preds : Array (Array Nat)} {s v : Nat}
    (h : v ∈ entryStored vc succs preds s) :
    ∃ b vb ss j, preds[s]? = some #[b] ∧ vc.blocks[b]? = some vb ∧ succs[b]? = some ss ∧
      ss.toList.idxOf? s = some j ∧ v ∈ (termEdgeDefs vb j).map (·.1.vreg) := by
  by_cases hb : ∃ b, preds[s]? = some #[b]
  · obtain ⟨b, hp⟩ := hb
    rw [entryStored_one hp] at h
    rcases hvb : vc.blocks[b]? with _ | vb <;> rcases hss : succs[b]? with _ | ss <;>
      simp only [hvb, hss] at h
    · cases h
    · cases h
    · cases h
    rcases hj : ss.toList.idxOf? s with _ | j <;> simp only [hj] at h
    · cases h
    · exact ⟨b, vb, ss, j, hp, hvb, hss, hj, h⟩
  · rw [entryStored_ne fun b e => hb ⟨b, e⟩] at h
    cases h

theorem entryStored_of {vc : VCode} {succs preds : Array (Array Nat)} {s b j : Nat} {vb : VBlock}
    {ss : Array Nat} (hp : preds[s]? = some #[b]) (hvb : vc.blocks[b]? = some vb)
    (hss : succs[b]? = some ss) (hj : ss.toList.idxOf? s = some j) :
    entryStored vc succs preds s = (termEdgeDefs vb j).map (·.1.vreg) := by
  rw [entryStored_one hp]
  simp only [hvb, hss, hj]

theorem idxOf?_of_unique {l : List Nat} {s j : Nat} (hj : l[j]? = some s)
    (hu : ∀ j', l[j']? = some s → j' = j) : l.idxOf? s = some j := by
  cases h : l.idxOf? s with
  | none => exact absurd (List.mem_of_getElem? hj) (List.idxOf?_eq_none_iff.mp h)
  | some i =>
    obtain ⟨hi, hget, -⟩ := List.idxOf?_eq_some_iff.mp h
    rw [hu i (List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩)]

theorem mem_getElem! {ss : Array (Array Nat)} {b s : Nat} (h : s ∈ (ss[b]! : Array Nat).toList) :
    ∃ (sb : Array Nat) (j : Nat), ss[b]? = some sb ∧ sb[j]? = some s := by
  cases hb : ss[b]? with
  | none =>
    have e : (ss[b]! : Array Nat) = #[] := by simp [getElem!_def, hb]; rfl
    rw [e] at h; simp at h
  | some sb =>
    have e : (ss[b]! : Array Nat) = sb := by simp [getElem!_def, hb]
    rw [e] at h
    obtain ⟨j, hj, e'⟩ := List.getElem_of_mem h
    exact ⟨sb, j, rfl, by rw [← e']; simp⟩

/-! ## `prepare` splits only edges into blocks with several predecessor edges -/

theorem innerStep_ls (ps : Array (Array Nat)) (st : Nat × Array VBlock × Array Label)
    (x : Nat × Label) : (Prep.innerStep ps st x).2.2 =
      st.2.2.push (if (ps[x.1]! : Array Nat).size > 1 then st.1 else x.2) := by
  by_cases h : (ps[x.1]! : Array Nat).size > 1 <;> simp [Prep.innerStep, h]

theorem inner_prefix (ps : Array (Array Nat)) : ∀ (xs : List (Nat × Label))
    (st : Nat × Array VBlock × Array Label) (j : Nat), j < st.2.2.size →
    (xs.foldl (Prep.innerStep ps) st).2.2[j]? = st.2.2[j]?
  | [], _, _, _ => rfl
  | x :: xs, st, j, hj => by
    rw [List.foldl_cons, inner_prefix ps xs _ j (by rw [innerStep_ls]; simp; omega), innerStep_ls,
      Array.getElem?_push]
    simp [Nat.ne_of_lt hj]

theorem inner_keep (ps : Array (Array Nat)) : ∀ (xs : List (Nat × Label))
    (st : Nat × Array VBlock × Array Label) (j : Nat) (x : Nat × Label), xs[j]? = some x →
    ¬ (ps[x.1]! : Array Nat).size > 1 →
    (xs.foldl (Prep.innerStep ps) st).2.2[st.2.2.size + j]? = some x.2
  | [], _, _, _, hx, _ => by simp at hx
  | y :: xs, st, 0, x, hx, hn => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
    subst hx
    rw [List.foldl_cons, Nat.add_zero, inner_prefix ps xs _ _ (by rw [innerStep_ls]; simp),
      innerStep_ls]
    simp [hn]
  | y :: xs, st, j + 1, x, hx, hn => by
    rw [List.foldl_cons]
    have := inner_keep ps xs (Prep.innerStep ps st y) j x (by simpa using hx) hn
    rw [innerStep_ls, Array.size_push] at this
    rw [show st.2.2.size + (j + 1) = st.2.2.size + 1 + j by omega]
    exact this

/-- A retargeted block keeps every target whose block has at most one predecessor edge
(`prepare` splits an edge only into a block with several). -/
def NoSplit (V1 B : Array VBlock) (ss1 ps1 : Array (Array Nat)) : Prop :=
  ∀ (k : Nat) (hk : k < V1.size) (hkB : k < B.size) (t t' : MInst) (m s : Nat) (l : Label),
    V1[k].insts.back? = some t → B[k].insts.back? = some t' → t.targets[m]? = some l →
    (ss1[k]! : Array Nat)[m]? = some s → ¬ (ps1[s]! : Array Nat).size > 1 → t'.targets[m]? = some l

open Prep in
/-- **`prepare`, step by step** (`Prep.prepare_facts`), with `NoSplit`. -/
theorem prepare_facts_ns {vc vcp : VCode} (h : prepare vc = .ok vcp) :
    ∃ (ss0 ps0 ss1 ps1 ss2 ps2 : Array (Array Nat)) (next : Nat) (B E : Array VBlock),
      vc.cfg = .ok (ss0, ps0) ∧
      ({ vc with blocks := keep vc.blocks (reachable ss0) } : VCode).cfg = .ok (ss1, ps1) ∧
      SInv (keep vc.blocks (reachable ss0)) (next0Of (keep vc.blocks (reachable ss0)))
        (keep vc.blocks (reachable ss0)).size (next, B, E) ∧
      ({ vc with blocks := B ++ E } : VCode).cfg = .ok (ss2, ps2) ∧
      vcp = { vc with blocks := (rpo ss2).map fun i => (B ++ E)[i]! } ∧
      NoSplit (keep vc.blocks (reachable ss0)) B ss1 ps1 := by
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
  have hcs1 := cfg_spec hc1
  rw [← Array.forIn_toList] at hfor
  have := forIn_inv _ _ (fun k st => SInv (keep vc.blocks (reachable r0.1))
      (next0Of (keep vc.blocks (reachable r0.1))) k st ∧
      ∀ (j : Nat) (hj : j < (keep vc.blocks (reachable r0.1)).size) (hjB : j < st.2.1.size)
        (t t' : MInst) (m s : Nat) (l : Label),
        (keep vc.blocks (reachable r0.1))[j].insts.back? = some t → st.2.1[j].insts.back? = some t' →
        t.targets[m]? = some l → (r1.1[j]! : Array Nat)[m]? = some s →
        ¬ (r1.2[s]! : Array Nat).size > 1 → t'.targets[m]? = some l) ?_ ?_ _ st ?_ hfor
  · rw [Array.length_toList, Array.size_zipIdx] at this
    exact ⟨r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, st.1, st.2.1, st.2.2, hc0, hc1, this.1, hc2, h.symm,
      fun k hk hkB => this.2 k hk hkB⟩
  · intro k x b b' hx hb hf
    obtain ⟨hb, hbn⟩ := hb
    rw [Array.toList_zipIdx, List.getElem?_zipIdx] at hx
    obtain ⟨vb, hvb, rfl⟩ : ∃ vb, (keep vc.blocks (reachable r0.1)).toList[k]? = some vb ∧ x = (vb, 0 + k) := by
      cases e : (keep vc.blocks (reachable r0.1)).toList[k]? with
      | none => rw [e] at hx; cases hx
      | some vb => rw [e] at hx; simp only [Option.map_some, Option.some.injEq] at hx
                   exact ⟨vb, rfl, hx.symm⟩
    simp only [Nat.zero_add] at hf ⊢
    obtain ⟨hk, hvb'⟩ := List.getElem?_eq_some_iff.mp hvb
    rw [Array.length_toList] at hk
    have hvbk : (keep vc.blocks (reachable r0.1))[k] = vb := by rw [← hvb', Array.getElem_toList]
    split at hf
    · -- no splitting
      simp only [pure, Except.pure, Except.ok.injEq, ForInStep.yield.injEq] at hf
      subst hf
      refine ⟨⟨hb.next, hb.edges, by simp [hb.size], fun j h1 h2 => ?_⟩, ?_⟩
      · simp only [Array.size_push] at h2
        by_cases hj : j < b.2.1.size
        · simp only [Array.getElem_push, hj, dite_true]
          exact hb.rw j h1 hj
        · have : j = k := by have := hb.size; omega
          subst this
          simp only [Array.getElem_push, hj, dite_false]
          exact .inl hvbk.symm
      · intro j h1 h2 t t' m s l ht ht' hl hs hp
        simp only [Array.size_push] at h2
        by_cases hj : j < b.2.1.size
        · simp only [Array.getElem_push, hj, dite_true] at ht'
          exact hbn j h1 hj t t' m s l ht ht' hl hs hp
        · have : j = k := by have := hb.size; omega
          subst this
          simp only [Array.getElem_push, hj, dite_false] at ht'
          rw [hvbk, ht'] at ht
          cases ht
          exact hl
    · rename_i hge
      split at hf
      · rename_i t ht
        split at hf
        · cases hf
        rename_i v hv
        split at hf
        · rename_i t' ht'
          simp only [pure, Except.pure, Except.ok.injEq, ForInStep.yield.injEq] at hf
          subst hf
          rw [← Array.forIn_toList, forIn_yield_foldl _ _ (innerStep r1.2) _
            (fun a c => by simp only [innerStep]; split <;> rfl)] at hv
          simp only [pure, Except.pure, Except.ok.injEq] at hv
          subst hv
          obtain ⟨r1', r2', r3', r4', -, r6'⟩ := innerFold r1.2 (next0Of (keep vc.blocks (reachable r0.1)))
            ((r1.1[k]! : Array Nat).zip t.targets.toArray).toList b.1 b.2.2 #[] hb.next hb.edges
          -- the successors of the kept block
          obtain ⟨t0, ts, hb0, -, hts, htsz, -⟩ := hcs1.blk k vb (by
            show (keep vc.blocks (reachable r0.1))[k]? = some vb
            rw [← Array.getElem?_toList]; exact hvb)
          rw [ht] at hb0
          cases hb0
          have hts' : (r1.1[k]! : Array Nat) = ts := by
            simp only [getElem!_def, hts]
          rw [hts'] at hge
          have h2 : 2 ≤ t.targets.length := by omega
          refine ⟨⟨r1', r2', by simp [hb.size], fun j h1 h2' => ?_⟩, ?_⟩
          · simp only [Array.size_push] at h2'
            by_cases hj : j < b.2.1.size
            · simp only [Array.getElem_push, hj, dite_true]
              exact rwOk_ext r3' (hb.rw j h1 hj)
            · have : j = k := by have := hb.size; omega
              subst this
              simp only [Array.getElem_push, hj, dite_false]
              rw [hvbk]
              refine .inr ⟨t, t', _, ht, h2, ht', rfl, fun m l' hm => ?_⟩
              rw [Array.getElem?_toList] at hm
              have hmlt := (Array.getElem?_eq_some_iff.mp hm).1
              rw [r4'] at hmlt
              simp only [Array.size_empty, Nat.zero_add] at hmlt
              obtain ⟨y, hy⟩ : ∃ y, (((r1.1[j]! : Array Nat).zip t.targets.toArray).toList)[m]? = some y :=
                ⟨_, List.getElem?_eq_getElem hmlt⟩
              obtain ⟨l'', hl1, hl2⟩ := r6' m y hy
              simp only [Array.size_empty, Nat.zero_add] at hl1
              rw [hm] at hl1
              cases hl1
              have hty : t.targets[m]? = some y.2 := by
                rw [Array.toList_zip] at hy
                have := (List.getElem?_zip_eq_some.mp hy).2
                simpa using this
              rcases hl2 with e | ⟨e, he⟩
              · exact .inl (by rw [hty, e])
              · exact .inr ⟨e, y.2, he, hty⟩
          · intro j h1 h2' t1 t1' m s l ht1 ht1' hl hs hp
            simp only [Array.size_push] at h2'
            by_cases hj : j < b.2.1.size
            · simp only [Array.getElem_push, hj, dite_true] at ht1'
              exact hbn j h1 hj t1 t1' m s l ht1 ht1' hl hs hp
            · have : j = k := by have := hb.size; omega
              subst this
              simp only [Array.getElem_push, hj, dite_false] at ht1'
              rw [hvbk, ht] at ht1
              cases ht1
              have e : t' = t1' := by simpa using ht1'
              subst e
              rw [(Prep.setTargets_targets ht').1, Array.getElem?_toList]
              have hy : (((r1.1[j]! : Array Nat).zip t.targets.toArray).toList)[m]? = some (s, l) := by
                rw [Array.toList_zip]
                exact List.getElem?_zip_eq_some.mpr ⟨by simpa using hs, by simpa using hl⟩
              have := inner_keep r1.2 _ (b.1, b.2.2, #[]) m (s, l) hy hp
              simpa using this
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
  · refine ⟨⟨?_, fun e he => by simp at he, rfl, fun j _ h => by simp at h⟩, fun j _ h => by simp at h⟩
    simp only [Array.size_empty, Nat.zero_add, next0Of, keep]

end KillPrep

open KillPrep in
/-- **`prepare` keeps `killFreeB`** on the lowered VCode (`LowOk`: `lowOk_of`). -/
theorem killFreeB_prepare {vc vcp : VCode} (hv : LowOk vc) (hk : killFreeB vc = true)
    (hp : prepare vc = .ok vcp) : killFreeB vcp = true := by
  have hed := edgesOk_prepare hv hp
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, hc1, hS, hc2, rfl, hns⟩ :=
    prepare_facts_ns hp
  have cs0 := Prep.cfg_spec hc0
  have cs1 : Prep.CfgSpec (Prep.keep vc.blocks (reachable ss0)) ss1 := Prep.cfg_spec hc1
  have cs2 : Prep.CfgSpec (B ++ E) ss2 := Prep.cfg_spec hc2
  have hd := hv.prepDomain
  obtain ⟨h10, -, hn1, hn2, hR, hRn, -⟩ := basics hv cs0 cs2 hS
  obtain ⟨-, -, -, -, -, -, -, -, -, hRre⟩ := Prep.facts_basic hd cs0 cs2 hS
  have hs0 : ss0.size ≠ 0 := by rw [cs0.size]; have := hv.nonempty; omega
  -- every instruction of the output: an edge block's `jump`, or one of `vc` up to retargeting
  have hI : ∀ vb' ∈ ((rpo ss2).map fun i => (B ++ E)[i]!).toList, ∀ i' ∈ vb'.insts.toList,
      (unstored i' = [] ∧ useVregs i' = []) ∨ ∃ vb ∈ vc.blocks.toList, ∃ i ∈ vb.insts.toList,
        unstored i' = unstored i ∧ useVregs i' = useVregs i := by
    intro vb' hvb' i' hi'
    rcases Prep.insts3 hd cs0 cs2 hS hvb' hi' with ⟨vb, hvb, hi⟩ | ⟨vb, hvb, i, hi, ls, hset⟩ |
      ⟨l, rfl⟩
    · exact .inr ⟨vb, hvb, i', hi, rfl, rfl⟩
    · have hsame : Driver.SameInst i i' :=
        .inr (by rw [(Prep.setTargets_targets hset).1]; exact hset)
      exact .inr ⟨vb, hvb, i, hi, unstored_same hsame, useVregs_same hsame⟩
    · exact .inl ⟨rfl, rfl⟩
  have hK : ∀ v, v ∈ killedOf { vc with blocks := (rpo ss2).map fun i => (B ++ E)[i]! } →
      v ∈ killedOf vc := by
    intro v hv'
    simp only [killedOf, List.mem_flatMap] at hv' ⊢
    obtain ⟨vb', hvb', i', hi', hu⟩ := hv'
    rcases hI vb' hvb' i' hi' with ⟨h1, -⟩ | ⟨vb, hvb, i, hi, h1, -⟩
    · rw [h1] at hu; cases hu
    · exact ⟨vb, hvb, i, hi, h1 ▸ hu⟩
  unfold killFreeB at hk ⊢
  simp only [Bool.and_eq_true] at hk ⊢
  obtain ⟨hU, hA⟩ := hk
  refine ⟨?_, ?_⟩
  · -- no instruction reads a killed vreg
    refine List.all_eq_true.mpr fun vb' hvb' => List.all_eq_true.mpr fun i' hi' =>
      List.all_eq_true.mpr fun v hv' => ?_
    rcases hI vb' hvb' i' hi' with ⟨-, h2⟩ | ⟨vb, hvb, i, hi, -, h2⟩
    · rw [h2] at hv'; cases hv'
    · rw [h2] at hv'
      have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hU vb hvb) i hi) v hv'
      have hn : v ∉ killedOf vc := by simpa using this
      simpa using fun h => hn (hK v h)
  · -- a killed branch argument
    rw [hc0] at hA
    simp only at hA
    split
    · rfl
    rename_i ss3 ps3 hc3
    have cs3 := Prep.cfg_spec hc3
    refine List.all_eq_true.mpr fun b hb => ?_
    split
    · rfl
    rename_i vb hvb
    refine List.all_eq_true.mpr fun a ha => ?_
    cases hka : (killedOf { vc with blocks := (rpo ss2).map fun i => (B ++ E)[i]! }).contains
      a.homeNum
    · rfl
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true]
    have hkill : a.homeNum ∈ killedOf vc := hK _ (by simpa using hka)
    change ((rpo ss2).map fun i => (B ++ E)[i]!)[b]? = some vb at hvb
    obtain ⟨k, hk, hkB, -, rfl⟩ := (cls3 hv cs0 cs1 cs2 hS hvb).resolve_right
      fun ⟨_, _, he, _⟩ => by rw [(e_blk hS he).2.2.1] at ha; cases ha
    -- the block is a block `b0` of `vc`, not retargeted (it has branch arguments)
    obtain ⟨b0, hb0, e0, hmk⟩ := Prep.keep_src hk
    have hb0' := Array.getElem?_eq_getElem hb0
    have hlb0 : vc.blocks[b0].label = b0 := hv.labels b0 _ hb0'
    have hBk : B[k] = (Prep.keep vc.blocks (reachable ss0))[k] := by
      rcases hS.rw k hk hkB with h | ⟨t, -, -, h1, h2, -⟩
      · exact h
      · exfalso
        obtain ⟨-, -, hba⟩ := b_fields hS hk hkB
        rw [e0] at h1 hba
        rw [hba, hv.multi hb0' h1 h2] at ha
        cases ha
    rw [hBk, e0] at ha ⊢
    -- `killFreeB vc` at `b0`: the argument is stored by `b0`'s entry stores, not killed in it
    have hA0 := List.all_eq_true.mp hA b0 (List.mem_range.mpr hb0)
    simp only [hb0'] at hA0
    have hA1 := List.all_eq_true.mp hA0 a ha
    have hkc : (killedOf vc).contains a.homeNum = true := by simpa using hkill
    simp only [hkc, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true] at hA1
    obtain ⟨hst, hno⟩ := hA1
    refine ⟨?_, hno⟩
    have hst' : a.homeNum ∈ entryStored vc ss0 ps0 b0 := by simpa using hst
    -- the only predecessor `p` of `b0`, a `try_call`, successor number `j`
    obtain ⟨p, vp, sp, j, hpp, hvp, hsp, hj, hmem⟩ := entryStored_inv hst'
    obtain ⟨hjlt, hjget, -⟩ := List.idxOf?_eq_some_iff.mp hj
    have hspj : sp[j]? = some b0 := by
      rw [Array.getElem?_eq_getElem (by simpa using hjlt)]; simpa using hjget
    obtain ⟨t, tsp, ht, -, hts, htsz, hlt⟩ := cs0.blk p vp hvp
    rw [hsp] at hts; cases hts
    have hjl : j < t.targets.length := by
      rw [← htsz]; exact (Array.getElem?_eq_some_iff.mp hspj).1
    have htj : t.targets[j]? = some b0 := by
      obtain ⟨k', hk', hlab⟩ := hlt j _ (List.getElem?_eq_getElem hjl)
      rw [hspj] at hk'; cases hk'
      obtain ⟨hb0'', hlb⟩ := Prep.lab_some hlab
      rw [List.getElem?_eq_getElem hjl, ← hlb, hv.labels b0 _ (Array.getElem?_eq_getElem hb0'')]
    obtain ⟨info, ti, rfl⟩ := tryCall_of_termEdgeDefs ht
      (fun h => by rw [h] at hmem; simp at hmem) (fun h => by rw [h] at htj; simp at htj)
    -- `p` is reachable
    have hr0 : Prep.Reach ss0 b0 := (Prep.reachable_spec (Prep.succsIn_of cs0) hs0).2.2.2 b0 hmk
    have hrp : Prep.Reach ss0 p := by
      cases hr0 with
      | entry => exact absurd (List.mem_of_getElem? htj) (hv.noEntry p vp _ hvp ht)
      | step hr hs =>
        obtain ⟨sb, j', hsb, hj'⟩ := mem_getElem! hs
        obtain ⟨rfl, -⟩ := preds_single hc0 hsb hj' hpp
        exact hr
    obtain ⟨kp, hkp, hpl, ekp, hr1⟩ := Prep.reach01 cs0 cs1 hd.labels hv.nonempty hrp
    obtain ⟨-, hr2⟩ := Prep.reach12 hS cs1 cs2 hn1 h10 hr1
    have hvp' : vc.blocks[p] = vp :=
      Option.some.inj ((Array.getElem?_eq_getElem hpl).symm.trans hvp)
    obtain ⟨hkpB, t0, t', ht0, ht', -, -, -, -, -, hsame, -, -⟩ := Prep.blk2 hS cs1 hkp
    rw [ekp, hvp', ht] at ht0
    cases ht0
    -- in the kept blocks, `kp → k` is the only edge into `k`: it is not split
    have hlabk : Prep.lab (Prep.keep vc.blocks (reachable ss0)) b0 = some k :=
      Prep.lab_of hn1 hk (by rw [e0, hlb0])
    obtain ⟨t1, ts1, ht1, -, hts1, -, hl1⟩ := cs1.blk kp _ (Array.getElem?_eq_getElem hkp)
    rw [ekp, hvp', ht] at ht1
    cases ht1
    obtain ⟨k', hk', hlab'⟩ := hl1 j b0 htj
    rw [hlabk] at hlab'
    cases hlab'
    have hps1 : ps1[k]? = some #[kp] := by
      refine preds_one hc1 hk hts1 hk' fun q sq j2 hq hj2 => ?_
      obtain ⟨vbq, tq, lq, hvbq, htq, htqj, hlabq⟩ := succ3 cs1 hq hj2
      obtain ⟨hkq, hlq⟩ := Prep.lab_some hlabq
      have hqV : q < (Prep.keep vc.blocks (reachable ss0)).size :=
        (Array.getElem?_eq_some_iff.mp hvbq).1
      obtain ⟨bq, hbq, eq, -⟩ := Prep.keep_src hqV
      have hvbq' : vbq = vc.blocks[bq] := by
        rw [← eq]; exact (Option.some.inj ((Array.getElem?_eq_getElem hqV).symm.trans hvbq)).symm
      subst hvbq'
      have hlq' : b0 = lq := by rw [← hlq, e0, hlb0]
      subst hlq'
      obtain ⟨tq', sq0, htq', -, hsq0, -, hlq0⟩ := cs0.blk bq _ (Array.getElem?_eq_getElem hbq)
      rw [htq] at htq'
      cases htq'
      obtain ⟨u, hu, hlabu⟩ := hlq0 j2 _ htqj
      have hub : b0 = u := by
        rw [Prep.lab_of hd.labels hb0 hlb0] at hlabu; exact Option.some.inj hlabu
      subst hub
      obtain ⟨rfl, -⟩ := preds_single hc0 hsq0 hu hpp
      obtain ⟨-, huj⟩ := preds_single hc0 hsp hspj hpp
      refine ⟨Prep.lbl_inj hn1 hqV hkp (by rw [eq, ekp]), ?_⟩
      rw [hsq0] at hsp
      cases hsp
      exact huj j2 hu
    have hss1 : (ss1[kp]! : Array Nat)[j]? = some k := by
      rw [show (ss1[kp]! : Array Nat) = ts1 by simp [getElem!_def, hts1]]; exact hk'
    have hnot : ¬ (ps1[k]! : Array Nat).size > 1 := by
      rw [show (ps1[k]! : Array Nat) = #[kp] by simp [getElem!_def, hps1]]; simp
    have htj' := hns kp hkp hkpB _ t' j k b0 (by rw [ekp, hvp', ht]) ht' htj hss1 hnot
    obtain ⟨ti', rfl⟩ : ∃ ti', t' = .tryCall info ti' := by
      rcases hsame with h | h
      · exact ⟨ti, h⟩
      · exact setTargets_tryCall h
    -- in the output: the block `q` of `kp` is the only predecessor of `b`, successor number `j`
    obtain ⟨q, hq, hRq, -⟩ := Prep.lab3 hR hn2 hRn (hRre kp hr2)
    have hq3 : ((rpo ss2).map fun i => (B ++ E)[i]!)[q]? = some B[kp] := by
      obtain ⟨hi, e⟩ := Prep.v3_get hR hq
      rw [e]; congr 1; simp only [hRq]; exact Array.getElem_append_left hkpB
    obtain ⟨t3, ts3, ht3, -, hts3, -, hl3⟩ := cs3.blk q _ hq3
    rw [ht'] at ht3
    cases ht3
    obtain ⟨u, hu, hlabu⟩ := hl3 j b0 htj'
    have hub : u = b := by
      have hb3 : b < ((rpo ss2).map fun i => (B ++ E)[i]!).size :=
        (Array.getElem?_eq_some_iff.mp hvb).1
      have := Prep.lab_of (Prep.lbls3 hR hn2 hRn) hb3 (l := b0) (by
        rw [Option.some.inj ((Array.getElem?_eq_getElem hb3).symm.trans hvb),
          (b_fields hS hk hkB).1, e0, hlb0])
      rw [this] at hlabu; exact (Option.some.inj hlabu).symm
    subst hub
    have hps3 : ps3[u]? = some #[q] :=
      ((hed ss3 ps3 hc3).tryEdge q B[kp] info ti' ts3 u hq3 ht').2 hts3
        (by simpa using Array.mem_of_getElem? hu)
    obtain ⟨-, huj3⟩ := preds_single hc3 hts3 hu hps3
    have hidx : ts3.toList.idxOf? u = some j :=
      idxOf?_of_unique (by simpa using hu) (fun j' h => huj3 j' (by simpa using h))
    rw [entryStored_of (vc := { vc with blocks := (rpo ss2).map fun i => (B ++ E)[i]! })
      hps3 hq3 hts3 hidx, termEdgeDefs_same (vb := vp) ht ht' hsame j]
    simpa using hmem

/-- **`killFreeB` of the pipeline's output from `killFreeB` of the lowered VCode** (`Dominated`,
`LowerScope`, `ArityOk` input: `lowOk_of`). -/
theorem killFreeB_prepare_of {f : Clif.Function} {vc vcp : VCode} (hd : Driver.Dominated f)
    (hs : Driver.LowerScope f) (ha : ArityOk f) (hl : lowerFunction f = .ok vc)
    (hk : killFreeB vc = true) (hp : prepare vc = .ok vcp) : killFreeB vcp = true :=
  killFreeB_prepare (lowOk_of hd hs ha hl) hk hp

end Backend.Proof.Spill
