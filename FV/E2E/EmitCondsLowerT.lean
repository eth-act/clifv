import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.IselEmitTDefs
import FV.Backend.Proof.LowerCompleteT
import FV.Backend.Proof.SpillEdgesT
import FV.Backend.Proof.DeadCleanupPrepare
import FV.Backend.Proof.DeadCleanupPositions
import FV.E2E.EmitCondsLower

/-!
# The emission conditions of the pipeline's output on the typed scope (S11, assembly)

`emitParts_lowerT`: given the ISLE-side contract on the typed scope `IselEmitT f` (every ISLE run
of the driver emits only instructions with `MInst.emitOk`, branch targets only on a terminator
run's last instruction; `Driver.iselEmitT`), the prepared VCode `prepare (lowerFunction f)` of
input in `Dominated` and `LowerScopeT` meets `immsOkB`, `noAlwaysB` and `branchTargetsOkB`;
`emitParts_cleanup_lowerT`: the same after the dead-code cleanup (`prune`).

The walk is `emitConds_lower`'s (`EmitCondsLower`) over the typed blocks `vcBlocksOfT`
(`lowerFunction_runT`): the driver's own typed instructions (`args`, the parameter loads
`stackArgLoad` — an `ldr s/d` of a 32/64-bit size —, the result `mov`s `extraOfT`, `jump`s) have
the emission conditions and no targets. `prepare` keeps both (`prep_emit`), its domain on the
typed scope is `Spill.prepDomain_ofT`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- A stack-passed parameter's load has the emission conditions. -/
theorem stackArgLoad_emitOk (r : Reg) (b : Nat) (am : AMode) : (stackArgLoad r b am).emitOk = true := by
  unfold stackArgLoad
  split
  · split <;> rfl
  · rfl

theorem stackArgLoad_targets (r : Reg) (b : Nat) (am : AMode) : (stackArgLoad r b am).targets = [] := by
  unfold stackArgLoad
  split <;> rfl

/-- **The emission conditions of `lowerFunction`'s output (typed)**: every instruction has
`emitOk`, and only a block's last instruction has branch targets. Integer externs (`hx`):
`lowerFunction_runT`'s premise since #609. -/
theorem vc_emitT {f : Clif.Function} {vc : VCode} (hI : IselEmitT f)
    (hx : f.externs.all (Compile.sigE ·.2.sig) = true) (hl : lowerFunction f = .ok vc) :
    ∀ vb ∈ vc.blocks.toList, (∀ m ∈ vb.insts.toList, m.emitOk = true) ∧ TargetsLast vb := by
  obtain ⟨ctx, ranges, st0, bl, hb, hlb, hvb, -, -⟩ := lowerFunction_runT hx hl
  obtain ⟨hS, hT, hY⟩ := hI ctx ranges st0 hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  have hemp := lowBlocks_emptied hlb
  -- a statement's emitted code
  have hst : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (j : Nat) (stm : Clif.Stmt) (sl : SLow),
      f.blocks[bi]? = some B → bl[bi]? = some L → B.body[j]? = some stm →
      L.sl[j]? = some sl → ∀ m ∈ sl.st'.emitted.toList, m.emitOk = true ∧ m.targets = [] := by
    intro bi B L j stm sl hB hL hj hsl
    obtain ⟨-, hc, -, -⟩ := hspec bi B L hB hL
    obtain ⟨info, hi, hic, -⟩ := hcf.stmt bi B j stm hB hj
    obtain ⟨tr, hrun⟩ := hc j sl hsl
    rw [hstart bi L hL] at hrun
    obtain ⟨ms, hms, hok⟩ := hS _ info stm.inst _ _ _ _ hi hic hrun
    have he : sl.st'.emitted.toList = ms := by
      rw [hms, hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)]; simp
    rw [he]
    exact hok
  -- the terminator's segment
  have hterm : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B →
      bl[bi]? = some L →
      (∀ m ∈ fixTry L.tl L.tst'.emitted.toList, m.emitOk = true) ∧
      ∀ m ∈ (fixTry L.tl L.tst'.emitted.toList).dropLast, m.targets = [] := by
    intro bi B L hB hL
    obtain ⟨-, -, htst, nl0, nl', hterm⟩ := hspec bi B L hB hL
    obtain ⟨hn, hy⟩ := lowTerm_spec hterm
    have hph := hcf.term bi B hB
    rw [← hstart bi L hL] at hph
    have hti := (Array.getElem?_eq_some_iff.mp hph).1
    have hBm : B ∈ f.blocks := List.mem_of_getElem? hB
    cases ht : B.term.isTry with
    | false =>
      obtain ⟨-, hd, out, tr, hc⟩ := hn ht
      obtain ⟨ms, hms, hok, htg⟩ := hT B hBm _ _ _ _ _ _ _ hti hph ht hd hc
      have he : L.tst'.emitted.toList = ms := by rw [hms, htst]; simp
      rw [he]
      exact ⟨fixTry_emitOk hok, fixTry_targets htg⟩
    | true =>
      obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := by
        cases hB' : B.term <;> rw [hB'] at ht <;> simp [Clif.Terminator.isTry] at ht
        · exact ⟨_, .inl ⟨_, _, rfl⟩⟩
        · exact ⟨_, .inr ⟨_, _, rfl⟩⟩
      obtain ⟨T, -, hd, -, -, -, -, out, tr, hc⟩ := hy et het
      obtain ⟨ms, hms, hok, htg⟩ := hY B hBm _ _ _ _ _ _ _ _ hti hph hd hc
      have he : L.tst'.emitted.toList = ms := by rw [hms]; simp
      rw [he]
      exact ⟨fixTry_emitOk hok, fixTry_targets htg⟩
  rw [hvb]
  intro vb hvb'
  refine ⟨vcBlocksT_all (fun m => m.emitOk = true)
    (fun _ _ hg m h => by rw [emitOk_mapRegs hg]; exact h) (fun _ => rfl)
    (fun r b am => stackArgLoad_emitOk r b am) (fun _ _ _ => rfl) (fun _ => rfl)
    (fun bi B L j stm sl hB hL hj hsl m hm => (hst bi B L j stm sl hB hL hj hsl m hm).1)
    (fun bi B L hB hL => (hterm bi B L hB hL).1) vb hvb', ?_⟩
  obtain ⟨R, ⟨gn, hRg⟩, ⟨bi, B, L, hB, hL, rfl⟩ | ⟨B, L, e, -, he, rfl⟩⟩ := mem_vcBlocksOfT hvb'
  · intro m hm
    have hins : (fixBlock R (rawBlockT f ctx bl bi B)).insts.toList = preT f ctx R bi ++
        ((List.range B.body.length).map (segT f ctx R bl bi)).flatten ++ tseg R bl bi :=
      rawBlockT_insts ctx hRg bl bi B
    rw [hins] at hm
    rcases mem_dropLast_append hm with hm | hm
    · rcases List.mem_append.mp hm with hpre | hm
      · unfold preT at hpre
        split at hpre
        · simp only [List.mem_cons] at hpre
          rcases hpre with rfl | hpre
          · rfl
          · simp only [entryLoadsT, List.mem_filterMap] at hpre
            obtain ⟨q, -, hq⟩ := hpre
            unfold entryLoadOfT at hq
            split at hq
            · cases hq; exact stackArgLoad_targets _ _ _
            · cases hq
        · simp at hpre
      · simp only [List.mem_flatten, List.mem_map, List.mem_range] at hm
        obtain ⟨sg, ⟨j, -, rfl⟩, hm⟩ := hm
        unfold segT at hm
        rw [hB, hL] at hm
        simp only at hm
        split at hm
        · rename_i stm sl hstm hsl
          simp only [List.mem_map] at hm
          obtain ⟨m1, hm1, rfl⟩ := hm
          rw [targets_mapRegs]
          rcases List.mem_append.mp hm1 with hm1 | hm1
          · exact (hst bi B L j stm sl hB hL hstm hsl m1 hm1).2
          · obtain ⟨s, a, b, rfl⟩ := mem_extraOfT hm1
            rfl
        · simp at hm
    · unfold tseg at hm
      rw [hL] at hm
      simp only [← List.map_dropLast, List.mem_map] at hm
      obtain ⟨m1, hm1, rfl⟩ := hm
      rw [targets_mapRegs]
      exact (hterm bi B L hB hL).2 m1 hm1
  · obtain ⟨tl, hi⟩ := edgeBlocksT_insts he
    intro m hm
    simp [fixBlock, hi] at hm

/-- The three emission facts from per-instruction `emitOk` and `TargetsLast` of `prepare`'s
output. -/
theorem emitParts_of {vc vcp : VCode} (hp : Backend.prepare vc = .ok vcp) (hd : Prep.PrepDomain vc)
    (hv : ∀ vb ∈ vcp.blocks.toList, (∀ m ∈ vb.insts.toList, m.emitOk = true) ∧ TargetsLast vb) :
    immsOkB vcp = true ∧ vcp.noAlwaysB = true ∧ branchTargetsOkB vcp = true := by
  have hok : ∀ vb ∈ vcp.blocks.toList, ∀ m ∈ vb.insts.toList,
      immOkB m = true ∧ m.noAlways = true := fun vb hvb m hm => by
    have := (hv vb hvb).1 m hm
    simpa [MInst.emitOk] using this
  refine ⟨?_, ?_, branchTargetsOk_of hp hd (fun vb h => (hv vb h).2)⟩
  · unfold immsOkB
    rw [Array.all_eq_true_iff_forall_mem]
    intro vb hvb
    rw [Array.all_eq_true_iff_forall_mem]
    intro m hm
    exact (hok vb (Array.mem_toList_iff.mpr hvb) m (Array.mem_toList_iff.mpr hm)).1
  · unfold VCode.noAlwaysB
    rw [List.all_eq_true]
    intro vb hvb
    rw [List.all_eq_true]
    intro m hm
    exact (hok vb hvb m hm).2

/-- **The emission conditions of the pipeline's output on the typed scope**: given
`IselEmitT f`, the prepared VCode of input in `Dominated` and `LowerScopeT` meets `immsOkB`,
`noAlwaysB` and `branchTargetsOkB`. -/
theorem emitParts_lowerT {f : Clif.Function} {vc vcp : VCode} (hdom : dominatedB f = true)
    (hs : LowerScopeT f) (hI : IselEmitT f) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare vc = .ok vcp) :
    immsOkB vcp = true ∧ vcp.noAlwaysB = true ∧ branchTargetsOkB vcp = true := by
  have hd := Spill.prepDomain_ofT (dominated_of hdom) hs hl
  exact emitParts_of hp hd (prep_emit hp hd (vc_emitT hI hs.externsE hl))

private theorem clean_emitT {vc : VCode}
    (h : ∀ vb ∈ vc.blocks.toList, (∀ i ∈ vb.insts.toList, i.emitOk = true) ∧ TargetsLast vb) :
    ∀ vb ∈ (clean vc).blocks.toList, (∀ i ∈ vb.insts.toList, i.emitOk = true) ∧ TargetsLast vb := by
  intro vb hb
  simp only [clean_blocks_map, Array.toList_map, List.mem_map] at hb
  obtain ⟨old, hb, rfl⟩ := hb
  refine ⟨fun i hi => (h old hb).1 i (cleanBlock_inst_mem vc 0 old i hi), ?_⟩
  intro i hi
  apply (h old hb).2 i
  exact (dropLast_sublist_of (scan_sublist vc.classes.size
    old.insts.toList (exitLive vc 0 old))).subset
    (by simpa [cleanBlock] using hi)

private theorem prune_emitT {vc : VCode}
    (h : ∀ vb ∈ vc.blocks.toList, (∀ i ∈ vb.insts.toList, i.emitOk = true) ∧ TargetsLast vb) :
    ∀ vb ∈ (prune vc).blocks.toList, (∀ i ∈ vb.insts.toList, i.emitOk = true) ∧ TargetsLast vb := by
  unfold prune
  cases vc.cfg with
  | error e => exact h
  | ok p => exact clean_emitT h

/-- **`emitParts_lowerT` after the dead-code cleanup**: the prepared `prune`d VCode meets
`immsOkB`, `noAlwaysB` and `branchTargetsOkB`. -/
theorem emitParts_cleanup_lowerT {f : Clif.Function} {vc vcp : VCode} (hdom : dominatedB f = true)
    (hs : LowerScopeT f) (hI : IselEmitT f) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare (prune vc) = .ok vcp) :
    immsOkB vcp = true ∧ vcp.noAlwaysB = true ∧ branchTargetsOkB vcp = true := by
  have hd := prune_prepDomain (Spill.prepDomain_ofT (dominated_of hdom) hs hl)
  exact emitParts_of hp hd (prep_emit hp hd (prune_emitT (vc_emitT hI hs.externsE hl)))

/-- **`emitParts_lowerT` on the float scope** (`LowerScopeTF`). -/
theorem emitParts_lowerTF {f : Clif.Function} {vc vcp : VCode} (hs : LowerScopeTF f)
    (hI : IselEmitT f) (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp) :
    immsOkB vcp = true ∧ vcp.noAlwaysB = true ∧ branchTargetsOkB vcp = true := by
  have hd := Spill.prepDomain_ofTF hs hl
  exact emitParts_of hp hd (prep_emit hp hd (vc_emitT hI hs.externsE hl))

/-- **`emitParts_cleanup_lowerT` on the float scope** (`LowerScopeTF`). -/
theorem emitParts_cleanup_lowerTF {f : Clif.Function} {vc vcp : VCode} (hs : LowerScopeTF f)
    (hI : IselEmitT f) (hl : lowerFunction f = .ok vc) (hp : Backend.prepare (prune vc) = .ok vcp) :
    immsOkB vcp = true ∧ vcp.noAlwaysB = true ∧ branchTargetsOkB vcp = true := by
  have hd := prune_prepDomain (Spill.prepDomain_ofTF hs hl)
  exact emitParts_of hp hd (prep_emit hp hd (prune_emitT (vc_emitT hI hs.externsE hl)))

end E2E
