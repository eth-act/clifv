import FV.Opt.Proof.CompleteSimpRunDef
import FV.Opt.Proof.CompleteSimpInv

/-!
# Completeness of simplify: the block loop

`Opt.simpFold` folds `Opt.stepBlock` over the reverse postorder of `f`. In a checked function every
block is reachable, so it occurs in the reverse postorder exactly once, after its dominators (their
RPO numbers are smaller: `Wf.rank`). Hence (`simpFold_runDone`), if each step keeps `RunBInv` when
its block is unprocessed and its dominators are processed (`Opt.stepBlock_inv`,
`FV/Opt/Proof/CompleteSimpRun.lean`), the run ends with every block processed and `RunDone` holds.
`binv_init`: the initial state satisfies `RunBInv` (nothing is output, every source value is bad);
`binv_runDone`: `RunBInv` with every block processed is `RunDone`.
-/

namespace Opt

open Clif

section Fold

variable {f : Function} {info : Info} {allowed skelOk : Inst → Bool} {st : SState} {S : Subst}
  {out : Array Block} {logs : Array (Option BlockLog)}

theorem CurV_end (f : Function) (logs : Array (Option BlockLog)) (n : Nat) :
    CurV f logs n [] = V0 f logs n := by
  simp [CurV, outsOf, emitV_nil]

theorem StmtsFact.get {idom : Array (Option Nat)} {V : Nat → Option Block} {B : ValueId → Prop}
    {d : Nat} : ∀ {ss : List Stmt} {lgs : List StmtLog} {k : Nat} (i : Nat) {s : Stmt} {lg : StmtLog},
      StmtsFact idom V B st S d ss lgs k → ss[i]? = some s → lgs[i]? = some lg →
      ∃ k', SLogFact idom V B st S d s k' lg
  | _ :: _, _ :: _, k, 0, _, _, ⟨h1, _⟩, hs, hl => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs hl
    subst hs; subst hl; exact ⟨k, h1⟩
  | _ :: _, _ :: _, _, i + 1, _, _, ⟨_, h2⟩, hs, hl => by
    simp only [List.getElem?_cons_succ] at hs hl
    exact StmtsFact.get i h2 hs hl
  | [], _, _, _, _, _, _, hs, _ => by simp at hs
  | _ :: _, [], _, _, _, _, h, _, _ => h.elim

/-- **`RunBInv` with every block processed is `RunDone`.** -/
theorem binv_runDone (_hc : Checked f info) (h : RunBInv f info allowed skelOk st S out logs)
    (hall : ∀ d, d < f.blocks.length → ∃ lg, logs[d]? = some (some lg)) :
    RunDone f info allowed skelOk st S out logs := by
  have hV := CurV_end f logs f.blocks.length
  have rinv := h.rinv
  have substOk := h.substOk
  have outs := h.outs
  have done := h.done
  rw [hV] at rinv substOk outs done
  refine { rinv, srcTy := h.srcTy, leafAv := h.leafAv, defsLeaf := h.defsLeaf, doneAv := h.doneAv,
           substOk, outs, done, size := h.size, all := hall, outEq := ⟨h.outSize, h.outEq⟩,
           keysRes := h.keysRes, callInd := ?_ }
  intro d lg b0 hlg hb0 s0 hs0 hci
  obtain ⟨b0', bo, hb0', -, hsf, -, -⟩ := done d lg hlg
  rw [hb0] at hb0'; cases hb0'
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hs0
  have hlen := hsf.length
  obtain ⟨lg', hlg'⟩ : ∃ lg', lg.stmts[i]? = some lg' :=
    ⟨_, List.getElem?_eq_getElem (by have := (List.getElem?_eq_some_iff.1 hi).1; omega)⟩
  obtain ⟨s', rfl⟩ := h.ciDone d lg b0 hlg hb0 i s0 lg' hi hlg' hci
  obtain ⟨k', -, e1, -, -⟩ := hsf.get i hi hlg'
  refine ⟨s', List.mem_flatMap.2 ⟨_, List.mem_of_getElem? hlg', by simp [StmtLog.out]⟩, ?_⟩
  rw [e1]; rfl

theorem logs_init {d : Nat} {lg : BlockLog} :
    (Array.replicate f.blocks.toArray.size (none : Option BlockLog))[d]? ≠ some (some lg) := by
  rw [Array.getElem?_replicate]
  split <;> simp

theorem CurV_init : CurV f (Array.replicate f.blocks.toArray.size none) f.blocks.length [] =
    fun _ => none := by
  rw [CurV_end]
  funext d
  unfold V0
  split
  · rename_i lg h; exact absurd h logs_init
  · split
    · rename_i hd; subst hd; simp
    · rfl

theorem not_done_init (hc : Checked f info) (y : ValueId) :
    ¬ Done f (Array.replicate f.blocks.toArray.size none) f.blocks.length 0 y := by
  rintro ⟨d, t, hd, ⟨lg, hlg⟩ | ⟨rfl, -⟩⟩
  · exact logs_init hlg
  · exact absurd (hc.def_lt hd) (Nat.lt_irrefl _)

theorem bad_init (hc : Checked f info) (y : ValueId) :
    Bad f (Array.replicate f.blocks.toArray.size none) f.blocks.length 0 {} y ↔ y ≤ maxValue f := by
  unfold Bad
  simp only [Std.HashMap.contains_empty, Bool.false_eq_true, or_false]
  exact ⟨fun h => h.1, fun h => ⟨h, not_done_init hc y⟩⟩

theorem not_defAt_init {x : ValueId} {d t : Nat} :
    ¬ DefAt (CurV f (Array.replicate f.blocks.toArray.size none) f.blocks.length []) x d t := by
  rw [CurV_init]
  rintro ⟨b, hb, -⟩
  cases hb

/-- **The initial state satisfies `RunBInv`.** -/
theorem binv_init {rematConst : Bool} (hc : Checked f info) :
    RunBInv f info allowed skelOk (initSState f info rematConst) {} f.blocks.toArray
      (Array.replicate f.blocks.toArray.size none) := by
  have hleaf : ∀ x d, (initAvail f).get? x = some d → x ≤ maxValue f := fun x d h =>
    hc.leaf_le ((hm_contains_iff _ _).2 (by rw [h]; rfl))
  have hknown : ∀ x, (initSState f info rematConst).known x = true → x ≤ maxValue f := by
    intro x hx
    rcases known_iff.1 hx with h | h
    · simp [initSState] at h
    · exact hc.leaf_le h
  refine { rinv := ?_, srcTy := fun _ _ h => h, leafAv := fun _ _ h => h,
           availSrc := fun _ _ h _ => .inl h, defsSrc := ?_, defsLeaf := ?_, doneAv := ?_,
           substOk := ?_, outs := ?_, done := ?_, size := by simp, altsNB := ?_, keysRes := ?_,
           availBig := ?_, ciDone := ?_, defNB := ?_, outSize := by simp, outEq := ?_ }
  · refine { m := ?_, partialsBig := fun _ => by simp [initSState], memo := ?_, alts := ?_ }
    · refine { fn := rfl, maxLt := by simp [initSState], knownLt := ?_, typesFresh := ?_,
               defsTy := ?_, altsKnown := ?_, availDef := ?_, defAvail := ?_, newBig := ?_,
               badLe := ?_, uniq := ?_ }
      · intro x hx
        exact Nat.lt_succ_of_le (hknown x hx)
      · intro x hx
        have hx' : maxValue f + 1 ≤ x := hx
        show info.types.get? x = none
        cases h : info.types.get? x with
        | none => rfl
        | some t => exact absurd hx' (Nat.not_le.2 (Nat.lt_succ_of_le (hc.types_le h)))
      · intro x n h; simp [initSState] at h
      · intro x ms h; simp [initSState] at h
      · intro x d h hb
        exact absurd ((bad_init hc x).2 (hleaf x d h)) hb
      · intro x d t h; exact absurd h not_defAt_init
      · intro x n h; simp [initSState] at h
      · intro x h; exact (bad_init hc x).1 h
      · intro x d t d' t' h; exact absurd h not_defAt_init
    · intro n w h; simp [initSState] at h
    · intro x ms h; simp [initSState] at h
  · intro y n h; simp [initSState] at h
  · intro y _; simp [initSState]
  · intro y h; exact absurd h (not_done_init hc y)
  · intro y w h; simp at h
  · intro d b h; rw [CurV_init] at h; cases h
  · intro d lg h; exact absurd h logs_init
  · intro x ms h; simp [initSState] at h
  · intro y h; simp at h
  · intro x d h hx; exact absurd hx (Nat.not_lt.2 (hleaf x d h))
  · intro d lg b0 h; exact absurd h logs_init
  · intro y d t h; exact absurd h not_defAt_init
  · intro d lg h; exact absurd h logs_init

/-- An ancestor of a block in the dominator tree of a checked function is a block. -/
theorem Checked.anc_lt (hc : Checked f info) {a b : Nat} (h : Anc info.cfg.idom a b)
    (hb : b < f.blocks.length) : a < f.blocks.length := by
  induction h with
  | refl => exact hb
  | up hc' _ ih =>
    refine ih ?_
    have := (build_domFacts f).lt _ _ (by rw [hc.info_eq] at hc'; exact hc')
    simpa [Cfg.size, Cfg.build] using this

/-- The blocks of a checked function are its reverse postorder. -/
theorem Checked.mem_rpo (hc : Checked f info) {d : Nat} (hd : d < f.blocks.length) :
    d ∈ info.cfg.rpo.toList := by
  rw [hc.info_eq]
  exact DomAlgo.build_reachable_mem f (hc.core.2.2.1 d (by simpa [Cfg.size, Cfg.build] using hd))

/-- The RPO number of the block at position `i` of the reverse postorder. -/
theorem Checked.rank_rpo (hc : Checked f info) {i x : Nat} (hi : info.cfg.rpo.toList[i]? = some x) :
    (info.cfg.rpoNum[x]?.join).getD 0 = i := by
  have e := hc.info_eq
  subst e
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.1 hi
  exact congrArg (fun o => Option.getD o 0) (DomAlgo.build_rpoNum_get f i hi')

/-- **The block loop ends with `RunDone`**, given that each step keeps `RunBInv`. -/
theorem simpFold_runDone {rules : SimplifyFn} {skel : SkeletonFn} {rematConst : Bool}
    (hc : Checked f info)
    (hstep : ∀ st S out logs bi, RunBInv f info allowed skelOk st S out logs →
      bi < f.blocks.length → logs[bi]? = some none →
      (∀ d, d ≠ bi → Anc info.cfg.idom d bi → ∃ lg, logs[d]? = some (some lg)) →
      RunBInv f info allowed skelOk
        (stepBlock rules skel allowed skelOk info.cfg f.blocks.toArray (st, S, out, logs) bi).1
        (stepBlock rules skel allowed skelOk info.cfg f.blocks.toArray (st, S, out, logs) bi).2.1
        (stepBlock rules skel allowed skelOk info.cfg f.blocks.toArray (st, S, out, logs) bi).2.2.1
        (stepBlock rules skel allowed skelOk info.cfg f.blocks.toArray (st, S, out, logs) bi).2.2.2) :
    RunDone f info allowed skelOk (simpFold rules skel allowed skelOk rematConst f info).1
      (simpFold rules skel allowed skelOk rematConst f info).2.1
      (simpFold rules skel allowed skelOk rematConst f info).2.2.1
      (simpFold rules skel allowed skelOk rematConst f info).2.2.2 := by
  let step := stepBlock rules skel allowed skelOk info.cfg f.blocks.toArray
  let I : List Nat → SState × Subst × Array Block × Array (Option BlockLog) → Prop := fun pre acc =>
    RunBInv f info allowed skelOk acc.1 acc.2.1 acc.2.2.1 acc.2.2.2 ∧
      ∀ d, d < f.blocks.length → (d ∈ pre → ∃ lg, acc.2.2.2[d]? = some (some lg)) ∧
        (d ∉ pre → acc.2.2.2[d]? = some none)
  have hnd : info.cfg.rpo.toList.Nodup := by rw [hc.info_eq]; exact build_rpo_nodup f
  have hlt : ∀ x ∈ info.cfg.rpo.toList, x < f.blocks.length := by
    intro x hx; rw [hc.info_eq] at hx; exact build_rpo_lt f hx
  have key : ∀ (rest pre : List Nat) acc, pre ++ rest = info.cfg.rpo.toList → I pre acc →
      I info.cfg.rpo.toList (rest.foldl step acc) := by
    intro rest
    induction rest with
    | nil => intro pre acc h hI; simp only [List.append_nil] at h; subst h; exact hI
    | cons bi rest ih =>
      intro pre acc hpre hI
      rw [List.foldl_cons]
      refine ih (pre ++ [bi]) _ (by simp [← hpre]) ?_
      obtain ⟨st, S, out, logs⟩ := acc
      obtain ⟨hB, hP⟩ := hI
      have hbi : bi < f.blocks.length := hlt bi (by rw [← hpre]; simp)
      have hnot : bi ∉ pre := fun h =>
        (List.nodup_append.1 (hpre ▸ hnd)).2.2 bi h bi (by simp) rfl
      have hsz : logs.size = f.blocks.length := hB.size
      have hpreds : ∀ d, d ≠ bi → Anc info.cfg.idom d bi → ∃ lg, logs[d]? = some (some lg) := by
        intro d hne ha
        have hdl := hc.anc_lt ha hbi
        obtain ⟨k, hkd⟩ := List.mem_iff_getElem?.1 (hc.mem_rpo hdl)
        have hbpos : info.cfg.rpo.toList[pre.length]? = some bi := by simp [← hpre]
        have hr := (Anc.rank_le hc.wf.rank ha).2 hne
        simp only [wfData] at hr
        rw [hc.rank_rpo hkd, hc.rank_rpo hbpos] at hr
        have hdk : pre[k]? = some d := by
          rw [← hkd, ← hpre, List.getElem?_append_left hr]
        exact (hP d hdl).1 (List.mem_of_getElem? hdk)
      have hB' := hstep st S out logs bi hB hbi ((hP bi hbi).2 hnot) hpreds
      refine ⟨hB', fun d hd => ?_⟩
      obtain ⟨lg, hlg⟩ : ∃ lg, (step (st, S, out, logs) bi).2.2.2 = logs.set! bi (some lg) := ⟨_, rfl⟩
      show (d ∈ pre ++ [bi] → ∃ lg, (step (st, S, out, logs) bi).2.2.2[d]? = some (some lg)) ∧
        (d ∉ pre ++ [bi] → (step (st, S, out, logs) bi).2.2.2[d]? = some none)
      rw [hlg, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      by_cases hdb : bi = d
      · subst hdb
        simp [hsz, hbi]
      · have hne : d ≠ bi := Ne.symm hdb
        simp only [hdb, ↓reduceIte, List.mem_append, List.mem_singleton, hne, or_false]
        exact hP d hd
  have hfin := key info.cfg.rpo.toList [] (initSState f info rematConst, {}, f.blocks.toArray,
      Array.replicate f.blocks.toArray.size none) (by simp)
    ⟨binv_init hc, fun d hd => ⟨fun h => by simp at h, fun _ => by simp [hd]⟩⟩
  have he : simpFold rules skel allowed skelOk rematConst f info =
      info.cfg.rpo.toList.foldl step (initSState f info rematConst, {}, f.blocks.toArray,
        Array.replicate f.blocks.toArray.size none) := by
    unfold simpFold; rw [Array.foldl_toList]
  rw [he]
  exact binv_runDone hc hfin.1 fun d hd => (hfin.2 d hd).1 (hc.mem_rpo hd)

end Fold

end Opt
