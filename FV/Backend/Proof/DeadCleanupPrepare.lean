import FV.Backend.Proof.DeadCleanupCorrect
import FV.Backend.Proof.PrepareComplete

namespace Backend.DeadCleanup
open Backend.Proof Backend.Proof.Prep

/-- CFG success supplies termination without an additional input certificate. -/
theorem terminated_of_cfg {vc : VCode} {ss ps : Array (Array Nat)}
    (h : vc.cfg = .ok (ss, ps)) :
    ∀ vb ∈ vc.blocks.toList, ∃ t, vb.insts.back? = some t ∧ t.isTerminator = true := by
  intro vb hvb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hvb
  obtain ⟨t, ts, ht, hterm, _⟩ := (cfg_spec h).blk i vb (by simpa using hi)
  exact ⟨t, ht, hterm⟩

/-- The guarded production pass preserves CFG construction on every input. -/
theorem prune_cfg (vc : VCode) : (prune vc).cfg = vc.cfg := by
  unfold prune
  cases h : vc.cfg with
  | error e => exact h
  | ok p => exact (clean_cfg vc (terminated_of_cfg h)).trans h

/-- The guarded pass preserves observable executions on every input. -/
theorem prune_correct {vc : VCode} {sem : Sem}
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next) :
    E2E.PrepareCorrect sem vc (prune vc) := by
  unfold prune
  cases h : vc.cfg with
  | error e => exact fun _ _ => ⟨fun _ _ _ h => h, fun _ h => h⟩
  | ok p => exact cleanup_correct hp (terminated_of_cfg h)

/-- Cleaning a terminated block preserves the full preparation domain. -/
theorem clean_prepDomain {vc : VCode} {ss ps : Array (Array Nat)}
    (hc : vc.cfg = .ok (ss, ps)) (hd : PrepDomain vc) : PrepDomain (clean vc) := by
  refine ⟨by simpa [clean] using hd.nonempty, ?_, ?_⟩
  · simpa [Lbls, clean_blocks_map, List.map_map, Function.comp_def, cleanBlock] using hd.labels
  · intro b vb t hb ht hn
    simp only [clean_blocks_map, Array.getElem?_map] at hb
    obtain ⟨vb0, hb0, rfl⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨t0, ts, hback, hterm, _⟩ := (cfg_spec hc).blk b vb0 hb0
    have he := cleanBlock_back vc 0 vb0 hback hterm
    rw [he] at ht
    have hte : t0 = t := Option.some.inj ht
    subst t
    exact hd.args b vb0 t0 hb0 hback hn

/-- Preparation's existing domain is preserved by the production guard. -/
theorem prune_prepDomain {vc : VCode} (hd : PrepDomain vc) : PrepDomain (prune vc) := by
  unfold prune
  cases h : vc.cfg with
  | error e => exact hd
  | ok p => exact clean_prepDomain h hd

/-- Any property of each original instruction holds for each retained one. -/
theorem clean_insts {vc : VCode} {P : MInst → Prop}
    (h : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, P i) :
    ∀ vb ∈ (clean vc).blocks.toList, ∀ i ∈ vb.insts.toList, P i := by
  intro vb hb i hi
  simp only [clean_blocks_map, Array.toList_map, List.mem_map] at hb
  obtain ⟨vb0, hb0, rfl⟩ := hb
  exact h vb0 hb0 i (cleanBlock_inst_mem vc 0 vb0 i hi)

theorem prune_insts {vc : VCode} {P : MInst → Prop}
    (h : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, P i) :
    ∀ vb ∈ (prune vc).blocks.toList, ∀ i ∈ vb.insts.toList, P i := by
  unfold prune
  cases hc : vc.cfg with
  | error e => exact h
  | ok p => exact clean_insts h

theorem prune_outgoing (vc : VCode) : (prune vc).outgoing = vc.outgoing := by
  unfold prune
  cases vc.cfg <;> rfl

private theorem prune_any_false {vc : VCode} {p : MInst → Bool}
    (h : (vc.blocks.any fun vb => vb.insts.any p) = false) :
    ((prune vc).blocks.any fun vb => vb.insts.any p) = false := by
  rw [Array.any_eq_false'] at h ⊢
  intro vb hb
  apply Bool.eq_false_iff.mp
  apply Array.any_eq_false'.mpr
  intro i hi
  exact prune_insts (P := fun i => ¬p i = true)
    (fun b hB j hJ => (Array.any_eq_false'.mp
      (Bool.eq_false_iff.mpr (h b (by simpa using hB)))) j (by simpa using hJ))
    vb (by simpa using hb) i (by simpa using hi)

theorem prune_noTryCall {vc : VCode} (h : vc.hasTryCall = false) :
    (prune vc).hasTryCall = false := prune_any_false h

theorem prune_noTls {vc : VCode} (h : vc.hasTls = false) :
    (prune vc).hasTls = false := prune_any_false h

/-- A terminated, nonempty real block inhabits the CFG/domain preservation
premises and actually loses its redundant producer under the guarded pass. -/
example : ∃ vc : VCode, (∃ ss ps, vc.cfg = .ok (ss, ps)) ∧ PrepDomain vc ∧
    (prune vc).blocks[0]!.insts.toList = [liveBic, liveReturn] := by
  let vb : VBlock := ⟨0, #[deadMvn, liveBic, liveReturn], #[], #[]⟩
  let vc : VCode := ⟨"cleanup_prepare", #[vb], #[.int, .int, .int, .int], 0, 0, #[]⟩
  obtain ⟨ss, ps, hc⟩ : ∃ ss ps, vc.cfg = .ok (ss, ps) := cfg_of (by
    intro i b hi
    have hn := (Array.getElem?_eq_some_iff.mp hi).1
    have hz : i = 0 := by simp [vc] at hn; omega
    subst i
    have he : b = vb := (Option.some.inj (show some vb = some b by simpa [vc] using hi)).symm
    subst b
    exact ⟨liveReturn, rfl, rfl, fun l hl => by cases hl⟩)
  have hd : PrepDomain vc := by
    refine ⟨by decide, by simp [Lbls, vc, vb], ?_⟩
    intro i b t hi ht hn
    have hs := (Array.getElem?_eq_some_iff.mp hi).1
    have hz : i = 0 := by simp [vc] at hs; omega
    subst i
    have he : b = vb := (Option.some.inj (show some vb = some b by simpa [vc] using hi)).symm
    subst b
    have he : t = liveReturn := (Option.some.inj ht).symm
    subst t
    simp [liveReturn, MInst.targets] at hn
  refine ⟨vc, ⟨ss, ps, hc⟩, hd, ?_⟩
  simp only [prune, hc]
  decide

end Backend.DeadCleanup
