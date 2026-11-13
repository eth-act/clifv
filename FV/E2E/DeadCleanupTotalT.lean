import FV.E2E.EmitTotalT
import FV.E2E.DeadCleanupPreparedSize
import FV.Backend.Proof.DeadCleanupPreparedAvailability
import FV.Backend.Proof.DeadCleanupEdgesOk
import FV.Backend.Proof.DeadCleanupClasses
import FV.Backend.Proof.DeadCleanupPrepare
import FV.Backend.Proof.DeadCleanupDeletion

/-!
# The dead-cleanup pipeline's allocation, emission and layout on the typed scope
(S11e5 Stage C, slice 8, totality half)

`prepare (prune vc)` is `preparedCleanup vc vcp` for `prepare vc = .ok vcp`
(`prune_prepare_ok`): every prepared block loses pure instructions only, keeping its label,
interface and terminator. The run-time facts the typed input scope decides on `prepare`'s raw
output (`lowerOutTB`: `FormsCovered`, `CtlInsts`, `emitCondsB`, `killFreeB`) therefore carry over
to the cleaned code, with no further premise and for every rule set:

* `preparedCleanup_formsCovered`, `preparedCleanup_ctlInsts`, `preparedCleanup_emitCondsB`;
* `spillLocal_cleanupT`: the spill allocator's local facts on the cleaned code (`spillLocal_cleanup`
  over `LowerScopeT`, with the typed spill chain's premises);
* `spillAccepted_cleanupT`: its spill allocation is `AllocChecked` (`spillStep4` with the
  availability of the raw code restricted to the cleaned one, `preparedCleanup_spillAvail`);
  `allocChecked_allocResult_of`: so is the allocation the backend lowers, whatever regalloc2
  answered;
* `backend_total_emit_cleanupT`: `backend_total_emitT` for `prepare (prune vc)`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.DeadCleanup

/-- The blocks of `preparedCleanup vc vcp` are `vcp`'s, cleaned. -/
theorem preparedCleanup_block {vc vcp : VCode} {b : Nat} {vb : VBlock}
    (h : (preparedCleanup vc vcp).blocks[b]? = some vb) :
    ∃ raw, vcp.blocks[b]? = some raw ∧ vb = preparedCleanupBlock vc raw := by
  rw [preparedCleanup_blocks, Array.getElem?_map] at h
  obtain ⟨raw, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨raw, hr, rfl⟩

/-- **Form coverage survives cleanup**: every cleaned instruction is a prepared one. -/
theorem preparedCleanup_formsCovered {cx : FnCtx} {vc vcp : VCode} (h : FormsCovered cx vcp) :
    FormsCovered cx (preparedCleanup vc vcp) := by
  intro b vb k i hb hi
  obtain ⟨raw, hr, rfl⟩ := preparedCleanup_block hb
  have hm : i ∈ raw.insts.toList :=
    (preparedCleanupBlock_sublist vc raw).subset
      (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hi))
  obtain ⟨k', hk'⟩ := List.mem_iff_getElem?.mp hm
  exact h b raw k' i hr (by rw [← Array.getElem?_toList]; exact hk')

/-- `ctlInstOk` depends on the position only for `Args`. -/
theorem ctlInstOk_pos {i : MInst} (h : ∀ ds, i ≠ .args ds) (b k b' k' : Nat) :
    ctlInstOk b k i = ctlInstOk b' k' i := by
  cases i
  case args ds => exact absurd rfl (h ds)
  case condBr _ _ c => cases c <;> rfl
  case trapIf c _ => cases c <;> rfl
  all_goals rfl

private theorem pureSublist_nil_right {xs : List MInst} (h : PureSublist xs []) : xs = [] := by
  cases h; rfl

/-- **The control check survives cleanup**: `Args` is not pure, so it stays the first
instruction of block 0, the only position where it occurs, and the terminator stays last. -/
theorem preparedCleanup_ctlInsts {vc vcp : VCode} (h : CtlInsts vcp) :
    CtlInsts (preparedCleanup vc vcp) := by
  obtain ⟨hi, vb0, ds, h0, ha, hsz⟩ := h
  refine ⟨fun b vb k i hb hik => ?_, ?_⟩
  · obtain ⟨raw, hr, rfl⟩ := preparedCleanup_block hb
    have hk : (preparedCleanupBlock vc raw).insts.toList[k]? = some i := by
      rw [Array.getElem?_toList]; exact hik
    obtain ⟨pre, post, he, hps⟩ := (preparedCleanupBlock_pureSublist vc raw).prefix hk
    have hr' : raw.insts[pre.length]? = some i := by
      rw [← Array.getElem?_toList, he]; simp
    have hok := hi b raw pre.length i hr hr'
    by_cases hA : ∃ ds, i = .args ds
    · obtain ⟨ds, rfl⟩ := hA
      simp only [ctlInstOk, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨hb0, hp0⟩, hds⟩ := hok
      have hpre : pre = [] := List.eq_nil_of_length_eq_zero hp0
      subst hpre
      have htk := pureSublist_nil_right hps
      have hlt : k < (preparedCleanupBlock vc raw).insts.toList.length :=
        (List.getElem?_eq_some_iff.mp hk).1
      have hk0 : k = 0 := by
        rcases List.take_eq_nil_iff.mp htk with h0 | h0
        · exact h0
        · rw [h0] at hlt; simp at hlt
      subst hk0
      simp [ctlInstOk, hb0, hds]
    · rw [ctlInstOk_pos (fun ds e => hA ⟨ds, e⟩) b k b pre.length]
      exact hok
  · have hhead : (preparedCleanupBlock vc vb0).insts.toList[0]? = some (.args ds) :=
      (preparedCleanupBlock_pureSublist vc vb0).head_nonpure
        (by rw [Array.getElem?_toList]; exact ha) rfl rfl
    rw [Array.getElem?_toList] at hhead
    refine ⟨preparedCleanupBlock vc vb0, ds, ?_, hhead, ?_⟩
    · rw [preparedCleanup_blocks, Array.getElem?_map, h0]; rfl
    · have hpos : 0 < (preparedCleanupBlock vc vb0).insts.size :=
        (Array.getElem?_eq_some_iff.mp hhead).1
      refine Nat.lt_of_not_le fun hle => ?_
      have h1 : (preparedCleanupBlock vc vb0).insts.size = 1 := by omega
      have hback := (preparedCleanupBlock_interface vc vb0).2.2.2
      rw [Array.back?_eq_getElem?, Array.back?_eq_getElem?, h1] at hback
      rw [hback] at hhead
      have hok := hi 0 vb0 (vb0.insts.size - 1) (.args ds) h0 hhead
      simp only [ctlInstOk, Bool.and_eq_true, beq_iff_eq] at hok
      omega

/-- **The emission conditions survive cleanup**: the size bound by
`preparedCleanup_spillSizeOkB`, the instruction-wise conditions on a sublist, branch targets
because cleanup keeps every block label. -/
theorem preparedCleanup_emitCondsB {vc vcp : VCode} {ss ps : Array (Array Nat)}
    (hc : vcp.cfg = .ok (ss, ps)) (h : emitCondsB vcp = true) :
    emitCondsB (preparedCleanup vc vcp) = true := by
  simp only [emitCondsB, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨hsz, himm⟩, hna⟩, htg⟩ := h
  refine ⟨⟨⟨preparedCleanup_spillSizeOkB vc vcp hc hsz, ?_⟩, ?_⟩, ?_⟩
  · unfold immsOkB at himm ⊢
    rw [Array.all_eq_true_iff_forall_mem] at himm ⊢
    have hP := preparedCleanup_insts vc vcp (P := fun i => immOkB i = true) (by
      intro vb hvb i hi
      have := himm vb (Array.mem_toList_iff.mp hvb)
      rw [Array.all_eq_true_iff_forall_mem] at this
      exact this i (Array.mem_toList_iff.mp hi))
    intro vb hvb
    rw [Array.all_eq_true_iff_forall_mem]
    intro i hi
    exact hP vb (Array.mem_toList_iff.mpr hvb) i (Array.mem_toList_iff.mpr hi)
  · simp only [VCode.noAlwaysB, List.all_eq_true] at hna ⊢
    exact preparedCleanup_insts vc vcp hna
  · have hlab : ∀ l, (preparedCleanup vc vcp).blocks.any (·.label == l) =
        vcp.blocks.any (·.label == l) := by
      intro l
      rw [preparedCleanup_blocks, Array.any_map]
      congr 1
      funext b
      simp only [Function.comp_def, (preparedCleanupBlock_interface vc b).1]
    unfold branchTargetsOkB at htg ⊢
    simp only [hlab]
    rw [Array.all_eq_true_iff_forall_mem] at htg ⊢
    have hP := preparedCleanup_insts vc vcp
      (P := fun i => (i.targets.all fun l => vcp.blocks.any (·.label == l)) = true) (by
        intro vb hvb i hi
        have := htg vb (Array.mem_toList_iff.mp hvb)
        rw [Array.all_eq_true_iff_forall_mem] at this
        exact this i (Array.mem_toList_iff.mp hi))
    intro vb hvb
    rw [Array.all_eq_true_iff_forall_mem]
    intro i hi
    exact hP vb (Array.mem_toList_iff.mpr hvb) i (Array.mem_toList_iff.mpr hi)

/-- **The spill allocator's local facts on the cleaned float-scope pipeline's output**
(`spillLocal_cleanup` over `LowerScopeTF`). -/
theorem spillLocal_cleanupTF {f : Clif.Function} {vc vcp : VCode} (hd : Dominated f)
    (hs : LowerScopeTF f) (har : ArityOk f) (htc : Compile.tryArgClassOk f = true)
    (hrc : ResClassOk f) (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp)
    (hctl : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i)
    (hform : FormsCovered default vcp) : SpillLocalOk (preparedCleanup vc vcp) := by
  have hp' := prune_prepare_ok hp
  have hdom := prune_prepDomain (prepDomain_ofTF hs hl)
  refine ⟨fun b vb k i hvb hi => ?_,
    classesOk_of (classesOkM_prepare hp' hdom (prune_classes (classesOkM_lowerTF hs hrc hl))),
    edgesOk_prepare (prune_lowOk (lowOk_ofTF hd hs har htc hl)) hp'⟩
  cases hct : i.isCtl
  · have hcov := preparedCleanup_formsCovered (vc := vc) hform b vb k i hvb hi
    rw [hct] at hcov
    exact spillInstOk_of_covered (hcov.resolve_left (by simp))
  · exact spillCtl_of_prepare hp' hdom (prune_insts hctl) b vb k i hvb hi hct

/-- **The spill allocator's local facts on the cleaned typed pipeline's output**
(`spillLocal_cleanup` over `LowerScopeT`; the premises of `spillLocalOk_of_pipelineT`, with the
covered forms on `prepare`'s raw output). -/
theorem spillLocal_cleanupT {f : Clif.Function} {vc vcp : VCode} (hd : Dominated f)
    (hs : LowerScopeT f) (har : ArityOk f) (htc : Compile.tryArgClassOk f = true)
    (hrc : ResClassOk f) (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp)
    (hctl : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i)
    (hform : FormsCovered default vcp) : SpillLocalOk (preparedCleanup vc vcp) :=
  spillLocal_cleanupTF hd hs.toTF har htc hrc hl hp hctl hform

/-- **The spill allocation of the cleaned float-scope pipeline's output is `AllocChecked`**
(`spillAccepted_cleanupT` over `LowerScopeTF`). -/
theorem spillAccepted_cleanupTF {f : Clif.Function} {vc vcp : VCode} (hd : Dominated f)
    (hs : LowerScopeTF f) (har : ArityOk f) (htc : Compile.tryArgClassOk f = true)
    (hrc : ResClassOk f) (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp)
    (hctl : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i)
    (hform : FormsCovered default vcp) (hk : killFreeB vcp = true) :
    AllocChecked (preparedCleanup vc vcp) (spillAlloc (preparedCleanup vc vcp)) := by
  have hdom0 := prepDomain_ofTF hs hl
  obtain ⟨ss, ps, hcfg⟩ := cfg_ok_of_prepare hp hdom0
  exact spillStep4 _ (restrictedD vc (killD vcp))
    ⟨ss, ps, by rw [preparedCleanup_cfg]; exact hcfg⟩
    (spillLocal_cleanupTF hd hs har htc hrc hl hp hctl hform)
    (preparedCleanup_spillAvail hdom0 (classesOkM_lowerTF hs hrc hl) hp _
      (spillAvail_of_killFree hk (edgesOk_prepare (lowOk_ofTF hd hs har htc hl) hp)))

/-- **The spill allocation of the cleaned typed pipeline's output is `AllocChecked`** given
`spillLocal_cleanupT`'s premises and `killFreeB` of `prepare`'s raw output (its availability,
restricted to the cleaned code). -/
theorem spillAccepted_cleanupT {f : Clif.Function} {vc vcp : VCode} (hd : Dominated f)
    (hs : LowerScopeT f) (har : ArityOk f) (htc : Compile.tryArgClassOk f = true)
    (hrc : ResClassOk f) (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp)
    (hctl : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i)
    (hform : FormsCovered default vcp) (hk : killFreeB vcp = true) :
    AllocChecked (preparedCleanup vc vcp) (spillAlloc (preparedCleanup vc vcp)) :=
  spillAccepted_cleanupTF hd hs.toTF har htc hrc hl hp hctl hform hk

/-- **The allocation the backend lowers is `AllocChecked`** once the spill allocation is,
whatever regalloc2 answered. -/
theorem allocChecked_allocResult_of {vcp : VCode} (hsa : AllocChecked vcp (spillAlloc vcp))
    (ra : Except String RFunc) : AllocChecked vcp (allocResult vcp ra) := by
  unfold allocResult
  cases ra with
  | error _ => exact hsa
  | ok rf =>
    simp only
    by_cases hc : (checkAlloc vcp rf).isOk = true
    · simp only [hc, ite_true]
      cases hlr : lowerRFunc vcp rf with
      | ok af =>
        cases h : checkAlloc vcp rf with
        | ok u => exact allocChecked_of_checkAlloc h
        | error e => rw [h] at hc; cases hc
      | error e => exact hsa
    · simp only [hc]; exact hsa

/-- **The cleaned typed pipeline's allocation, emission and layout succeed**
(`backend_total_emitT` for `prepare (prune vc) = .ok (preparedCleanup vc vcp)`): from the same
run-time facts on `prepare`'s raw output `vcp`, for every answer `ra` of the untrusted allocator,
`lowerAllocReady`, `emitFunc` and `layout` succeed on the cleaned code, and the allocation lowered
is `AllocChecked`. -/
theorem backend_total_emit_cleanupTF {f : Clif.Function} {vc vcp : VCode} (hd : Dominated f)
    (hs : LowerScopeTF f) (har : ArityOk f) (htc : Compile.tryArgClassOk f = true)
    (hrc : ResClassOk f) (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hsc : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i)
    (hcov : FormsCovered default vcp) (hk : killFreeB vcp = true) (hctl : CtlInsts vcp)
    (hem : emitCondsB vcp = true) (ra : Except String RFunc) (k : Nat) :
    AllocChecked (preparedCleanup vc vcp)
        (allocResult (preparedCleanup vc vcp) (readyAnswer (preparedCleanup vc vcp) ra)) ∧
    ∃ af, lowerAllocReady (preparedCleanup vc vcp) ra = .ok af ∧
      ∃ fa fb, emitFunc k af = .ok fa ∧ fa.layout = .ok fb := by
  have hp' := prune_prepare_ok hp
  have hdom := prune_prepDomain (prepDomain_ofTF hs hl)
  obtain ⟨ss, ps, hcfg⟩ := cfg_ok_of_prepare hp (prepDomain_ofTF hs hl)
  have hcfg' : (preparedCleanup vc vcp).cfg = .ok (ss, ps) := by
    rw [preparedCleanup_cfg]; exact hcfg
  have hacc := spillAccepted_cleanupTF hd hs har htc hrc hl hp hsc hcov hk
  have hcov' := preparedCleanup_formsCovered (vc := vc) hcov
  have hctl' := preparedCleanup_ctlInsts (vc := vc) hctl
  have hem' := preparedCleanup_emitCondsB (vc := vc) hcfg hem
  exact ⟨allocChecked_allocResult_of hacc _,
    lowerAllocReady_emit_of
      (lowerRFunc_spill_of hcfg' (spillLocal_cleanupTF hd hs har htc hrc hl hp hsc hcov)
        hctl'.1 hctl'.2)
      (fun af ha => emitReady_spill_of hdom hp' hacc hcov' hctl' hem' ha) ra k⟩

/-- **The cleaned typed pipeline's allocation, emission and layout succeed**
(`backend_total_emitT` for `prepare (prune vc) = .ok (preparedCleanup vc vcp)`): from the same
run-time facts on `prepare`'s raw output `vcp`, for every answer `ra` of the untrusted allocator,
`lowerAllocReady`, `emitFunc` and `layout` succeed on the cleaned code, and the allocation lowered
is `AllocChecked`. -/
theorem backend_total_emit_cleanupT {f : Clif.Function} {vc vcp : VCode} (hd : Dominated f)
    (hs : LowerScopeT f) (har : ArityOk f) (htc : Compile.tryArgClassOk f = true)
    (hrc : ResClassOk f) (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hsc : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i)
    (hcov : FormsCovered default vcp) (hk : killFreeB vcp = true) (hctl : CtlInsts vcp)
    (hem : emitCondsB vcp = true) (ra : Except String RFunc) (k : Nat) :
    AllocChecked (preparedCleanup vc vcp)
        (allocResult (preparedCleanup vc vcp) (readyAnswer (preparedCleanup vc vcp) ra)) ∧
    ∃ af, lowerAllocReady (preparedCleanup vc vcp) ra = .ok af ∧
      ∃ fa fb, emitFunc k af = .ok fa ∧ fa.layout = .ok fb :=
  backend_total_emit_cleanupTF hd hs.toTF har htc hrc hl hp hsc hcov hk hctl hem ra k

end E2E
