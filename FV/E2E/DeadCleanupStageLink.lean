import FV.E2E.DeadCleanupGotCheck
import FV.E2E.DeadCleanupLinkCalls
import FV.E2E.DeadCleanupPreparedSize
import FV.Backend.Proof.DropSublist
import FV.Backend.Proof.CleanupStageAvail

/-!
# The linker's per-function facts through the production cleanup stage

The production cleanup stage's prepared code is `stagePrepared f vc raw` for `prepare vc = .ok raw`
(`cleanupStage_prepare_ok`): a block map `T` of `raw` (`stagePrepared_eq`, `stagePrepared_delMap`)
whose every block deletes only instructions that are pure (`DeadCleanup`) or skippable
(`skipDel`, Cranelift's skip of unused instructions), in order (`stageBlock_drop`). GOT loads and
entry arguments are neither, so the GOT facts, call sites and entry arguments of `raw` survive,
as for `preparedCleanup` (`FV/E2E/DeadCleanupGotCheck.lean`, `DeadCleanupLinkCalls.lean`).
-/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- What the stage may delete: pure (cleanup) or skippable (the skip) instructions. -/
def stageDel (i : MInst) : Bool := pureForm i || skipDel i

/-- Every block of the stage's prepared code deletes only `stageDel` instructions, in order. -/
theorem stageBlock_drop {f : Clif.Function} {vc raw : VCode} (hd : Prep.PrepDomain vc)
    (hp : prepare vc = .ok raw) {rb : VBlock} (hrb : rb ∈ raw.blocks.toList) :
    DropSublist stageDel
      ((preparedCleanupBlock (skipStage f vc) ∘ skipBlock (stageMask f vc)) rb).insts.toList
      rb.insts.toList :=
  (dropSublist_of_pure (preparedCleanupBlock_pureSublist _ _)).trans
    (skipPrepared_drop (f := f) hd hp hrb)

section
variable {T : VBlock → VBlock} {raw : VCode}

private def gotQ (t : Nat) (i : MInst) : Option String :=
  match i with
  | .loadExtNameGot (.vreg t' .int) n => if t' = t then some n else none
  | _ => none

private theorem gotQ_del (t : Nat) (i : MInst) (h : stageDel i = true) : gotQ t i = none := by
  cases i <;> simp_all [gotQ, stageDel, pureForm, skipDel]

private theorem findSome_mem (f : MInst → Option String) (bs : List VBlock)
    (h : ∀ b ∈ bs, (T b).insts.toList.findSome? f = b.insts.toList.findSome? f) :
    (bs.flatMap fun b => (T b).insts.toList).findSome? f =
      (bs.flatMap fun b => b.insts.toList).findSome? f := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.findSome?_append,
      h b (List.mem_cons_self ..), ih (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))]

/-- Blocks of `raw` delete only `stageDel` instructions under `T`. -/
def StageDrop (T : VBlock → VBlock) (raw : VCode) : Prop :=
  ∀ rb ∈ raw.blocks.toList, DropSublist stageDel (T rb).insts.toList rb.insts.toList

theorem stage_gotSym (hK : StageDrop T raw) (t : Nat) :
    gotSym (mapBlocks T raw) t = gotSym raw t := by
  unfold gotSym
  rw [mapBlocks_blocks]
  simp only [Array.toList_map, List.flatMap_map]
  exact findSome_mem (gotQ t) raw.blocks.toList
    (fun b hb => (hK b hb).findSome (gotQ t) (gotQ_del t))

private theorem gotBefore_drop {xs ys : List MInst} (h : DropSublist stageDel xs ys)
    {k : Nat} {i : MInst} (hi : xs[k]? = some i) {load : MInst}
    (hp : stageDel load = false)
    (hold : ∀ j : Nat, ys[j]? = some i → ∃ l < j, ys[l]? = some load) :
    ∃ l < k, xs[l]? = some load := by
  obtain ⟨pre, post, he, hpre⟩ := h.prefix hi
  have hsource : ys[pre.length]? = some i := by simp [he]
  obtain ⟨l, hl, hlo⟩ := hold pre.length hsource
  have hload : load ∈ pre := by
    rw [he, List.getElem?_append_left hl] at hlo
    exact List.mem_of_getElem? hlo
  have hkept := hpre.mem hload hp
  obtain ⟨l', hl'⟩ := List.mem_iff_getElem?.mp hkept
  have hlt := (List.getElem?_eq_some_iff.mp hl').1
  simp only [List.length_take] at hlt
  refine ⟨l', by omega, ?_⟩
  rw [List.getElem?_take] at hl'
  split at hl'
  · exact hl'
  · cases hl'

theorem stage_gotB (hK : StageDrop T raw) (t : Nat) (n : String) (hg : gotB raw t n = true) :
    gotB (mapBlocks T raw) t n = true := by
  unfold gotB at hg ⊢
  apply (array_all_iff _ _).2
  intro q vb hq
  rw [mapBlocks_blocks, Array.getElem?_map] at hq
  obtain ⟨rb, hrb, he⟩ := Option.map_eq_some_iff.mp hq
  subst vb
  have hblock := (array_all_iff _ _).1 hg q rb hrb
  simp only [Bool.and_eq_true] at hblock
  obtain ⟨hdefs, hsites⟩ := hblock
  have hrel := hK rb (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hrb))
  rw [Bool.and_eq_true]
  constructor
  · apply (array_all_iff _ _).2
    intro k i hi
    have hmem := hrel.sublist.subset (List.mem_of_getElem? (by simpa using hi))
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
    exact (array_all_iff _ _).1 hdefs j i (by simpa using hj)
  · apply List.all_eq_true.mpr
    intro k hk
    have before (i : MInst) (hi : (T rb).insts[k]? = some i)
        (hold : ∀ j : Nat, rb.insts[j]? = some i → gotBefore t n rb j = true) :
        gotBefore t n (T rb) k = true := by
      have h := gotBefore_drop hrel (by simpa using hi)
        (show stageDel (.loadExtNameGot (.vreg t .int) n) = false from rfl) (by
          intro j hj
          have hbefore := hold j (by simpa using hj)
          simpa only [gotBefore, List.any_eq_true, List.mem_range, decide_eq_true_eq,
            ← Array.getElem?_toList] using hbefore)
      simpa only [gotBefore, List.any_eq_true, List.mem_range, decide_eq_true_eq,
        ← Array.getElem?_toList] using h
    cases hi : (T rb).insts[k]? with
    | none => simp [gotSiteB, hi]
    | some i =>
      cases i with
      | call info =>
        by_cases hd : info.dest = .reg (.vreg t .int)
        · have hb := before (.call info) hi (by
            intro j hj
            have hjb := (Array.getElem?_eq_some_iff.mp hj).1
            have hs := List.all_eq_true.mp hsites j (List.mem_range.mpr hjb)
            simpa [gotSiteB, hj, hd] using hs)
          simp [gotSiteB, hi, hd, hb]
        · simp [gotSiteB, hi, hd]
      | tryCall info ti =>
        by_cases hd : info.dest = .reg (.vreg t .int)
        · have hb := before (.tryCall info ti) hi (by
            intro j hj
            have hjb := (Array.getElem?_eq_some_iff.mp hj).1
            have hs := List.all_eq_true.mp hsites j (List.mem_range.mpr hjb)
            simpa [gotSiteB, hj, hd] using hs)
          simp [gotSiteB, hi, hd, hb]
        · simp [gotSiteB, hi, hd]
      | _ => simp [gotSiteB, hi]

theorem stage_gotOf (hK : StageDrop T raw) {t : Nat} {n : String} (hg : gotOf raw t = some n) :
    gotOf (mapBlocks T raw) t = some n := by
  unfold gotOf at hg ⊢
  rw [stage_gotSym hK]
  cases hs : gotSym raw t with
  | none => simp [hs] at hg
  | some n' =>
    simp only [hs] at hg
    change (if gotB (mapBlocks T raw) t n' then some n' else none) = some n
    by_cases hb : gotB raw t n' = true
    · simp only [hb, ite_true, Option.some.injEq] at hg
      subst n
      simp [stage_gotB hK t n' hb]
    · simp [hb] at hg

theorem stage_sites (hT : DelMap T) (hK : StageDrop T raw) {P : Clif.Program} {g : Clif.Function}
    {may : Clif.Function → Bool}
    (h : LinkCheck.allInsts raw (LinkCheck.siteB (LinkCheck.siteOk P g may raw)) = true) :
    LinkCheck.allInsts (mapBlocks T raw)
      (LinkCheck.siteB (LinkCheck.siteOk P g may (mapBlocks T raw))) = true := by
  unfold LinkCheck.allInsts at h ⊢
  simp only [Array.all_eq_true_iff_forall_mem] at h ⊢
  intro b hb i hi
  have hold : LinkCheck.siteB (LinkCheck.siteOk P g may raw) i = true :=
    hT.insts raw (fun b hb i hi =>
      h b (Array.mem_toList_iff.mp hb) i (Array.mem_toList_iff.mp hi)) b
      (Array.mem_toList_iff.mpr hb) i (Array.mem_toList_iff.mpr hi)
  have hsite (info : CallInfo) (hs : LinkCheck.siteOk P g may raw info = true) :
      LinkCheck.siteOk P g may (mapBlocks T raw) info = true := by
    unfold LinkCheck.siteOk at hs ⊢
    cases hd : info.dest with
    | sym n => simpa [hd] using hs
    | reg r =>
      simp only [hd] at hs ⊢
      exact LinkCheck.blrOk_got_mono (fun _ _ => stage_gotOf hK) hs
  cases i with
  | call info => exact hsite info hold
  | tryCall info ti => exact hsite info hold
  | _ => rfl

/-- The stage cannot increase the spill allocation's word bound, hence keeps `spillSizeOkB`. -/
theorem stage_spillSizeOkB (hT : DelMap T) {succs preds : Array (Array Nat)}
    (hc : raw.cfg = .ok (succs, preds))
    (hs : spillSizeOkB raw = true) : spillSizeOkB (mapBlocks T raw) = true := by
  have hm : spillWordBound (mapBlocks T raw) ≤ spillWordBound raw :=
    spillWordBound_map_mono raw (mapBlocks T raw) T (mapBlocks_blocks T raw)
      hT.map.branchArgs hT.map.params hT.map.back hT.sub hc (by rw [hT.cfg]; exact hc)
  have hsize : spillWordBound raw < 2 ^ 24 := of_decide_eq_true hs
  exact decide_eq_true (by omega)

/-- The entry block's leading `args` survives. -/
theorem stage_entry_head (hK : StageDrop T raw) {rb : VBlock} {ds : List (Reg × Reg)}
    (hrb : raw.blocks[0]? = some rb)
    (hi : rb.insts[0]? = some (.args ds)) :
    (mapBlocks T raw).blocks[0]? = some (T rb) ∧ (T rb).insts[0]? = some (.args ds) := by
  refine ⟨by rw [mapBlocks_blocks, Array.getElem?_map, hrb]; rfl, ?_⟩
  have h := (hK rb (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hrb))).head
    (i := .args ds) (by rw [Array.getElem?_toList]; exact hi) rfl
  rwa [Array.getElem?_toList] at h

end

/-! ## The production stage's prepared code -/

theorem stagePrepared_drop {f : Clif.Function} {vc raw : VCode} (hd : Prep.PrepDomain vc)
    (hp : prepare vc = .ok raw) :
    ∀ rb ∈ raw.blocks.toList, DropSublist stageDel
      ((preparedCleanupBlock (skipStage f vc) ∘ skipBlock (stageMask f vc)) rb).insts.toList
      rb.insts.toList :=
  fun _ hrb => stageBlock_drop hd hp hrb

theorem stagePrepared_spillSizeOkB (f : Clif.Function) (vc raw : VCode)
    {succs preds : Array (Array Nat)} (hc : raw.cfg = .ok (succs, preds))
    (hs : spillSizeOkB raw = true) : spillSizeOkB (stagePrepared f vc raw) = true := by
  rw [stagePrepared_eq]; exact stage_spillSizeOkB (stagePrepared_delMap f vc) hc hs

theorem stagePrepared_sites {P : Clif.Program} {g : Clif.Function} {may : Clif.Function → Bool}
    {vc raw : VCode} (hd : Prep.PrepDomain vc) (hp : prepare vc = .ok raw)
    (h : LinkCheck.allInsts raw (LinkCheck.siteB (LinkCheck.siteOk P g may raw)) = true) :
    LinkCheck.allInsts (stagePrepared g vc raw)
      (LinkCheck.siteB (LinkCheck.siteOk P g may (stagePrepared g vc raw))) = true := by
  rw [stagePrepared_eq]
  exact stage_sites (stagePrepared_delMap g vc) (stagePrepared_drop hd hp) h

theorem stagePrepared_gotOf {f : Clif.Function} {vc raw : VCode} (hd : Prep.PrepDomain vc)
    (hp : prepare vc = .ok raw) {t : Nat} {n : String} (hg : gotOf raw t = some n) :
    gotOf (stagePrepared f vc raw) t = some n := by
  rw [stagePrepared_eq]; exact stage_gotOf (stagePrepared_drop hd hp) hg

theorem stagePrepared_entry_head {f : Clif.Function} {vc raw : VCode} (hd : Prep.PrepDomain vc)
    (hp : prepare vc = .ok raw) {rb : VBlock} {ds : List (Reg × Reg)}
    (hrb : raw.blocks[0]? = some rb) (hi : rb.insts[0]? = some (.args ds)) :
    ∃ vb, (stagePrepared f vc raw).blocks[0]? = some vb ∧ vb.insts[0]? = some (.args ds) := by
  rw [stagePrepared_eq]
  obtain ⟨h1, h2⟩ := stage_entry_head (stagePrepared_drop hd hp) hrb hi
  exact ⟨_, h1, h2⟩

end E2E
