import FV.Backend.Proof.IselEmitDefs
import FV.Backend.Proof.LowerShapeOkFacts
import FV.Backend.Proof.SpillStep4Cfg
import FV.E2E.EmitEnc
import FV.E2E.EmitNear
import FV.E2E.EmitLabels

/-!
# The emission conditions of the pipeline's output from the ISLE runs (V6c, assembly)

`emitConds_lower`: given the ISLE-side contract `IselEmit f` (every ISLE run of the driver emits
only instructions with `MInst.emitOk`, branch targets only on a terminator run's last
instruction), the prepared VCode `prepare (lowerFunction f)` meets `immsOkB`, `noAlwaysB` and
`branchTargetsOkB`.

The walk is `formsCovered_of_runs`' (`LowerCover`): the driver's own instructions (`args`, the
parameter loads, result `mov`s, `jump`s) have no immediates and no targets; the alias renaming
keeps `emitOk` (`emitOk_mapRegs`: an indirect call's int-vreg target stays an int vreg) and the
targets; the `tryCall` replacing a `try_call` rule's last `call` has that call's `CallInfo`. In
every block only the last instruction has branch targets (`TargetsLast`): the entry `pre` and the
statements' segments have none, the terminator's segment only on its last instruction.
`prepare` keeps both (`prep_emit`: a block is kept, retargeted on its last instruction only, or an
edge block's single `jump`), and the last instruction's targets are block labels by `VCode.cfg`
on `prepare`'s output (`Spill.cfg_ok_of_prepare`, `Prep.cfg_spec`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- Only the block's last instruction has branch targets. -/
def TargetsLast (vb : VBlock) : Prop := ∀ m ∈ vb.insts.toList.dropLast, m.targets = []

/-! ## Renaming and retargeting keep `emitOk` -/

theorem isVregInt_vrenaming {R : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming R gn) (r : Reg) :
    (R r).isVregInt = r.isVregInt := by
  cases r with
  | vreg n c => rw [hg.vreg]; cases c <;> rfl
  | _ => rw [hg.real _ (fun _ _ h => by cases h)]

theorem emitOk_mapRegs {R : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming R gn) (m : MInst) :
    (m.mapRegs R).emitOk = m.emitOk := by
  cases m
  all_goals try rfl
  case condBr a b k => cases k <;> rfl
  case trapIf k c => cases k <;> rfl
  case call info =>
    obtain ⟨dest, _⟩ := info
    cases dest <;> simp [MInst.mapRegs, MInst.emitOk, immOkB, MInst.noAlways, isVregInt_vrenaming hg]
  case tryCall info ti =>
    obtain ⟨dest, _⟩ := info
    cases dest <;> simp [MInst.mapRegs, MInst.emitOk, immOkB, MInst.noAlways, isVregInt_vrenaming hg]

theorem emitOk_setTargets {i i' : MInst} {ls : List Label} (h : i.setTargets ls = some i') :
    i'.emitOk = i.emitOk := by
  unfold MInst.setTargets at h
  split at h
  all_goals (try split at h)
  all_goals (cases h; try simp [MInst.emitOk, immOkB, MInst.noAlways])
  all_goals (rename_i k _ _; cases k <;> rfl)

/-! ## The terminator's segment -/

theorem fixTry_emitOk {T : Option TryLow} {ms : List MInst} (h : ∀ m ∈ ms, m.emitOk = true) :
    ∀ m ∈ fixTry T ms, m.emitOk = true := by
  intro m hm
  unfold fixTry at hm
  split at hm
  · unfold tryFix at hm
    split at hm
    · rename_i c hlast
      simp only [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact h m (List.dropLast_subset _ hm)
      · have hc := h _ (List.mem_of_getLast? hlast)
        revert hc
        simp only [MInst.emitOk, immOkB, MInst.noAlways]
        exact id
    · exact h m hm
  · exact h m hm

theorem fixTry_targets {T : Option TryLow} {ms : List MInst}
    (h : ∀ m ∈ ms.dropLast, m.targets = []) :
    ∀ m ∈ (fixTry T ms).dropLast, m.targets = [] := by
  intro m hm
  unfold fixTry at hm
  split at hm
  · unfold tryFix at hm
    split at hm
    · rw [List.dropLast_concat] at hm
      exact h m hm
    · exact h m hm
  · exact h m hm

theorem mem_dropLast_append {α : Type} {X T : List α} {m : α} (h : m ∈ (X ++ T).dropLast) :
    m ∈ X ∨ m ∈ T.dropLast := by
  rw [List.dropLast_append] at h
  split at h
  · exact .inl (List.dropLast_subset _ h)
  · exact List.mem_append.mp h

/-! ## `lowerFunction`'s output -/

/-- **The emission conditions of `lowerFunction`'s output**: every instruction has `emitOk`, and
only a block's last instruction has branch targets. -/
theorem vc_emit {f : Clif.Function} {vc : VCode} (hI : IselEmit f)
    (hl : lowerFunction f = .ok vc) :
    ∀ vb ∈ vc.blocks.toList, (∀ m ∈ vb.insts.toList, m.emitOk = true) ∧ TargetsLast vb := by
  obtain ⟨ctx, ranges, st0, bl, hb, hlb, hvb, -, -⟩ := lowerFunction_run hl
  obtain ⟨hS, hT, hY⟩ := hI ctx ranges st0 hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  have hemp := lowBlocks_emptied hlb
  -- a statement's segment: emitted code and result `mov`s
  have hseg : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (j : Nat) (stm : Clif.Stmt) (sl : SLow),
      f.blocks[bi]? = some B → bl[bi]? = some L → B.body[j]? = some stm →
      L.sl[j]? = some sl → ∀ m ∈ sl.st'.emitted.toList ++ extraOf stm.results sl.rss,
        m.emitOk = true ∧ m.targets = [] := by
    intro bi B L j stm sl hB hL hj hsl
    obtain ⟨-, hc, -, -⟩ := hspec bi B L hB hL
    obtain ⟨info, hi, hic, -⟩ := hcf.stmt bi B j stm hB hj
    obtain ⟨tr, hrun⟩ := hc j sl hsl
    rw [hstart bi L hL] at hrun
    obtain ⟨ms, hms, hok⟩ := hS _ info stm.inst _ _ _ _ hi hic hrun
    have he : sl.st'.emitted.toList = ms := by
      rw [hms, hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)]; simp
    rw [he]
    exact all_extraOf (P := fun m => m.emitOk = true ∧ m.targets = []) (fun _ _ _ => ⟨rfl, rfl⟩)
      hok _ _
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
    cases ht : B.term.isTry with
    | false =>
      obtain ⟨-, hd, out, tr, hc⟩ := hn ht
      obtain ⟨ms, hms, hok, htg⟩ := hT _ _ _ _ _ _ _ _ hti hph ht hd hc
      have he : L.tst'.emitted.toList = ms := by rw [hms, htst]; simp
      rw [he]
      exact ⟨fixTry_emitOk hok, fixTry_targets htg⟩
    | true =>
      obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := by
        cases hB' : B.term <;> rw [hB'] at ht <;> simp [Clif.Terminator.isTry] at ht
        · exact ⟨_, .inl ⟨_, _, rfl⟩⟩
        · exact ⟨_, .inr ⟨_, _, rfl⟩⟩
      obtain ⟨T, -, hd, -, -, -, -, out, tr, hc⟩ := hy et het
      obtain ⟨ms, hms, hok, htg⟩ := hY _ _ _ _ _ _ _ _ _ hti hph hd hc
      have he : L.tst'.emitted.toList = ms := by rw [hms]; simp
      rw [he]
      exact ⟨fixTry_emitOk hok, fixTry_targets htg⟩
  rw [hvb]
  intro vb hvb'
  refine ⟨vcBlocks_all (fun m => m.emitOk = true)
    (fun _ _ hg m h => by rw [emitOk_mapRegs hg]; exact h) (fun _ => rfl) (fun _ _ _ => rfl)
    (fun _ => rfl) (fun bi B L j stm sl hB hL hj hsl m hm => (hseg bi B L j stm sl hB hL hj hsl m hm).1)
    (fun bi B L hB hL => (hterm bi B L hB hL).1) vb hvb', ?_⟩
  obtain ⟨R, -, ⟨bi, B, L, hB, hL, rfl⟩ | ⟨B, L, e, -, he, rfl⟩⟩ := mem_vcBlocksOf hvb'
  · intro m hm
    have hins : (fixBlock R (rawBlock f bl bi B)).insts.toList = pre f R bi ++
        ((List.range B.body.length).map (seg f R bl bi)).flatten ++ tseg R bl bi :=
      rawBlock_insts f R bl bi B
    rw [hins] at hm
    rcases mem_dropLast_append hm with hm | hm
    · rcases List.mem_append.mp hm with hpre | hm
      · unfold pre at hpre
        split at hpre
        · simp only [List.mem_cons] at hpre
          rcases hpre with rfl | hpre
          · rfl
          · simp only [entryLoads, List.mem_filterMap] at hpre
            obtain ⟨q, -, hq⟩ := hpre
            unfold entryLoadOf at hq
            split at hq
            · cases hq; rfl
            · cases hq
        · simp at hpre
      · simp only [List.mem_flatten, List.mem_map, List.mem_range] at hm
        obtain ⟨sg, ⟨j, -, rfl⟩, hm⟩ := hm
        unfold seg at hm
        rw [hB, hL] at hm
        simp only at hm
        split at hm
        · rename_i stm sl hstm hsl
          simp only [List.mem_map] at hm
          obtain ⟨m1, hm1, rfl⟩ := hm
          rw [targets_mapRegs]
          exact (hseg bi B L j stm sl hB hL hstm hsl m1 hm1).2
        · simp at hm
    · unfold tseg at hm
      rw [hL] at hm
      simp only [← List.map_dropLast, List.mem_map] at hm
      obtain ⟨m1, hm1, rfl⟩ := hm
      rw [targets_mapRegs]
      exact (hterm bi B L hB hL).2 m1 hm1
  · obtain ⟨tl, hi⟩ := edgeBlocks_insts he
    intro m hm
    simp [fixBlock, hi] at hm

/-! ## Through `prepare` -/

/-- `prepare` keeps the emission conditions and `TargetsLast`: a block of its output is a block of
the input, one retargeted on its last instruction, or an edge block's single `jump`. -/
theorem prep_emit {vc vcp : VCode} (hp : prepare vc = .ok vcp) (hd : Prep.PrepDomain vc)
    (hv : ∀ vb ∈ vc.blocks.toList, (∀ m ∈ vb.insts.toList, m.emitOk = true) ∧ TargetsLast vb) :
    ∀ vb ∈ vcp.blocks.toList, (∀ m ∈ vb.insts.toList, m.emitOk = true) ∧ TargetsLast vb := by
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, hc1, hS, hc2, rfl⟩ := Prep.prepare_facts hp
  have cs0 := Prep.cfg_spec hc0
  have cs2 : Prep.CfgSpec (B ++ E) ss2 := Prep.cfg_spec hc2
  obtain ⟨-, -, -, -, -, hR, -, -, -, -⟩ := Prep.facts_basic hd cs0 cs2 hS
  intro vb' hvb
  have hvb' : vb' ∈ ((rpo ss2).map fun i => (B ++ E)[i]!).toList := hvb
  rw [Array.mem_toList_iff, Array.mem_map] at hvb'
  obtain ⟨i, hiR, rfl⟩ := hvb'
  have hi2 : i < (B ++ E).size := hR i (by simpa using hiR)
  rw [getElem!_pos (B ++ E) i hi2]
  by_cases hiB : i < B.size
  · rw [Array.getElem_append_left hiB]
    have hi1 : i < (Prep.keep vc.blocks (reachable ss0)).size := by rw [← hS.size]; exact hiB
    obtain ⟨b, hb, e, -⟩ := Prep.keep_src hi1
    have hmem : (Prep.keep vc.blocks (reachable ss0))[i] ∈ vc.blocks.toList := by rw [e]; simp
    obtain ⟨hok, htl⟩ := hv _ hmem
    rcases hS.rw i hi1 hiB with h | ⟨t, t', ls, h1, -, h3, h4, -⟩
    · rw [h]; exact ⟨hok, htl⟩
    · rw [h4]
      have ht := Array.mem_toList_iff.mpr (Array.mem_of_back? h1)
      refine ⟨fun m hm => ?_, fun m hm => ?_⟩
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · exact hok m (Prep.pop_mem hm)
        · rw [emitOk_setTargets h3]; exact hok t ht
      · simp only [Array.toList_push, List.dropLast_concat, Array.toList_pop] at hm
        exact htl m hm
  · rw [Array.getElem_append_right (Nat.le_of_not_lt hiB)]
    have he : i - B.size < E.size := by simp at hi2; omega
    obtain ⟨l, hl⟩ := hS.edges _ he
    rw [hl]
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · simp at hm; subst hm; rfl
    · simp at hm

/-- An instruction of a block with last instruction `t`: `t`, or one before it. -/
theorem mem_of_back {xs : Array MInst} {t m : MInst} (hb : xs.back? = some t)
    (hm : m ∈ xs.toList) : m ∈ xs.toList.dropLast ∨ m = t := by
  rw [← Array.getLast?_toList, List.getLast?_eq_some_iff] at hb
  obtain ⟨ys, hys⟩ := hb
  rw [hys] at hm ⊢
  rw [List.dropLast_concat]
  simpa using hm

/-- **Branch targets are block labels** in `prepare`'s output when only the blocks' last
instructions have targets: `VCode.cfg` resolves those. -/
theorem branchTargetsOk_of {vc vcp : VCode} (hp : prepare vc = .ok vcp) (hd : Prep.PrepDomain vc)
    (htl : ∀ vb ∈ vcp.blocks.toList, TargetsLast vb) : branchTargetsOkB vcp = true := by
  obtain ⟨ss, ps, hc⟩ := Spill.cfg_ok_of_prepare hp hd
  have cs := Prep.cfg_spec hc
  unfold branchTargetsOkB
  rw [Array.all_eq_true_iff_forall_mem]
  intro vb hvb
  rw [Array.all_eq_true_iff_forall_mem]
  intro m hm
  rw [List.all_eq_true]
  intro l hl
  obtain ⟨q, hq, rfl⟩ := Array.getElem_of_mem hvb
  obtain ⟨t, ts, hback, -, -, -, hlab⟩ := cs.blk q _ (Array.getElem?_eq_getElem hq)
  rcases mem_of_back hback (Array.mem_toList_iff.mpr hm) with hm | rfl
  · rw [htl _ (Array.mem_toList_iff.mpr (Array.getElem_mem hq)) m hm] at hl
    cases hl
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
    obtain ⟨k, -, hk⟩ := hlab j _ (List.getElem?_eq_getElem hj)
    obtain ⟨hk', hlk⟩ := Prep.lab_some hk
    rw [Array.any_eq_true]
    exact ⟨k, hk', by simp [hlk]⟩

/-! ## Assembly -/

/-- **The emission conditions of the pipeline's output from the ISLE runs**: given `IselEmit f`,
the prepared VCode of in-scope input meets `immsOkB`, `noAlwaysB` and `branchTargetsOkB`. -/
theorem emitConds_lower {f : Clif.Function} {vc vcp : VCode} (hs : LowerScope f)
    (hI : IselEmit f) (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp) :
    immsOkB vcp = true ∧ vcp.noAlwaysB = true ∧ branchTargetsOkB vcp = true := by
  have hd := prepDomain_of_lower hs hl hs.nonempty
  have hv := prep_emit hp hd (vc_emit hI hl)
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

end E2E
