import FV.E2E.GotFlow
import FV.Backend.Proof.DeadCleanupPrepareMap

namespace E2E
open Backend Backend.Proof Backend.DeadCleanup

private def gotQuery (t : Nat) (i : MInst) : Option String :=
  match i with
  | .loadExtNameGot (.vreg t' .int) n => if t' = t then some n else none
  | _ => none

private theorem gotQuery_pure (t : Nat) (i : MInst) (hp : pureForm i = true) :
    gotQuery t i = none := by
  cases i <;> simp_all [gotQuery, pureForm]

private theorem findSome_blocks (T : VBlock → VBlock) (f : MInst → Option String)
    (h : ∀ b, (T b).insts.toList.findSome? f = b.insts.toList.findSome? f)
    (bs : List VBlock) :
    (bs.flatMap fun b => (T b).insts.toList).findSome? f =
      (bs.flatMap fun b => b.insts.toList).findSome? f := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.flatMap_cons, List.findSome?_append, h, ih]

/-- GOT loads and their ordering survive, so symbol discovery is unchanged. -/
theorem preparedCleanup_gotSym (vc vcp : VCode) (t : Nat) :
    gotSym (preparedCleanup vc vcp) t = gotSym vcp t := by
  unfold gotSym
  rw [preparedCleanup_blocks]
  simp only [Array.toList_map, List.flatMap_map]
  exact findSome_blocks (preparedCleanupBlock vc) (gotQuery t)
    (fun b => (preparedCleanupBlock_pureSublist vc b).findSome (gotQuery t)
      (gotQuery_pure t)) vcp.blocks.toList

private theorem gotBefore_sublist {xs ys : List MInst} (h : PureSublist xs ys)
    {k : Nat} {i : MInst} (hi : xs[k]? = some i) {load : MInst}
    (hp : pureForm load = false)
    (hold : ∀ j : Nat, ys[j]? = some i → ∃ l < j, ys[l]? = some load) :
    ∃ l < k, xs[l]? = some load := by
  obtain ⟨pre, post, he, hpre⟩ := h.prefix hi
  have hsource : ys[pre.length]? = some i := by simp [he]
  obtain ⟨l, hl, hlo⟩ := hold pre.length hsource
  have hload : load ∈ pre := by
    rw [he, List.getElem?_append_left hl] at hlo
    exact List.mem_of_getElem? hlo
  have hkept := hpre.nonpure_mem hload hp
  obtain ⟨l', hl'⟩ := List.mem_iff_getElem?.mp hkept
  have hlt := (List.getElem?_eq_some_iff.mp hl').1
  simp only [List.length_take] at hlt
  refine ⟨l', by omega, ?_⟩
  rw [List.getElem?_take] at hl'
  split at hl'
  · exact hl'
  · cases hl'

theorem preparedCleanup_gotB (vc vcp : VCode) (t : Nat) (n : String)
    (hg : gotB vcp t n = true) : gotB (preparedCleanup vc vcp) t n = true := by
  unfold gotB at hg ⊢
  apply (array_all_iff _ _).2
  intro q vb hq
  rw [preparedCleanup_blocks, Array.getElem?_map] at hq
  obtain ⟨raw, hraw, he⟩ := Option.map_eq_some_iff.mp hq
  subst vb
  have hblock := (array_all_iff _ _).1 hg q raw hraw
  simp only [Bool.and_eq_true] at hblock
  obtain ⟨hdefs, hsites⟩ := hblock
  have hrel := preparedCleanupBlock_pureSublist vc raw
  rw [Bool.and_eq_true]
  constructor
  · apply (array_all_iff _ _).2
    intro k i hi
    have hmem := hrel.sublist.subset (List.mem_of_getElem? (by simpa using hi))
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
    exact (array_all_iff _ _).1 hdefs j i (by simpa using hj)
  · apply List.all_eq_true.mpr
    intro k hk
    have before (i : MInst) (hi : (preparedCleanupBlock vc raw).insts[k]? = some i)
        (hold : ∀ j : Nat, raw.insts[j]? = some i → gotBefore t n raw j = true) :
        gotBefore t n (preparedCleanupBlock vc raw) k = true := by
      have h := gotBefore_sublist hrel (by simpa using hi)
        (show pureForm (.loadExtNameGot (.vreg t .int) n) = false from rfl) (by
          intro j hj
          have hbefore := hold j (by simpa using hj)
          simpa only [gotBefore, List.any_eq_true, List.mem_range, decide_eq_true_eq,
            ← Array.getElem?_toList] using hbefore)
      simpa only [gotBefore, List.any_eq_true, List.mem_range, decide_eq_true_eq,
        ← Array.getElem?_toList] using h
    cases hi : (preparedCleanupBlock vc raw).insts[k]? with
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

/-- Every GOT fact admitted by the baseline checker remains admitted. -/
theorem preparedCleanup_gotOf (vc vcp : VCode) {t : Nat} {n : String}
    (hg : gotOf vcp t = some n) : gotOf (preparedCleanup vc vcp) t = some n := by
  unfold gotOf at hg ⊢
  rw [preparedCleanup_gotSym]
  cases hs : gotSym vcp t with
  | none => simp [hs] at hg
  | some n' =>
    simp only [hs] at hg
    change (if gotB (preparedCleanup vc vcp) t n' then some n' else none) = some n
    by_cases hb : gotB vcp t n' = true
    · simp only [hb, ite_true, Option.some.injEq] at hg
      subst n
      simp [preparedCleanup_gotB vc vcp t n' hb]
    · simp [hb] at hg

/-! Joint non-vacuity: actual GOT load, an indirect call, and a deleted producer. -/
example : ∃ vc : VCode, gotOf vc 0 = some "callee" ∧
    gotOf (preparedCleanup vc vc) 0 = some "callee" ∧
    (preparedCleanup vc vc).blocks[0]!.insts.size < vc.blocks[0]!.insts.size := by
  let c : CallInfo := ⟨.reg (.vreg 0 .int), [], []⟩
  let vc : VCode := ⟨"got_cleanup", #[⟨0,
    #[.loadExtNameGot (.vreg 0 .int) "callee", deadMvn, .call c, liveReturn], #[], #[]⟩],
    #[.int, .int, .int, .int], 0, 0, #[]⟩
  have hgot : gotOf vc 0 = some "callee" := by
    have hm : deadMvn.operands = .ok
        #[⟨2, .int, .def, .late, .reg⟩, ⟨1, .int, .use, .early, .reg⟩] := rfl
    have hc : (MInst.call c).operands = .ok #[⟨0, .int, .use, .early, .reg⟩] := rfl
    have hr : liveReturn.operands = .ok #[⟨3, .int, .use, .early, .fixed (.x 0)⟩] := rfl
    simp [gotOf, gotSym, gotB, gotDefB, gotSiteB, gotBefore, vc, c,
      hm, hc, hr, List.range_succ, Operand.isDef]
    cases (MInst.loadExtNameGot (.vreg 0 .int) "callee").operands <;>
      simp [deadMvn, liveReturn]
  refine ⟨vc, hgot, preparedCleanup_gotOf vc vc hgot, ?_⟩
  rw [preparedCleanup_blocks]
  simp only [vc, Array.map_singleton, getElem!_def, Array.getElem?_singleton, ite_true]
  rw [preparedCleanupBlock_insts vc (show _ = some liveReturn from rfl) rfl]
  decide

end E2E
