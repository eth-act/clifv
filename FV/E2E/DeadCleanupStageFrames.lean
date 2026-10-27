import FV.E2E.DeadCleanupLinkFrames
import FV.E2E.DeadCleanupStageLink

/-! `FV/E2E/DeadCleanupLinkFrames.lean`'s entry, outgoing-area and frame facts for the production
cleanup stage's prepared code `stagePrepared g vc vcp` (formerly `preparedCleanup vc vcp`). -/

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- Entry arguments stay at position zero. -/
theorem entryB_stage_of_lower {g : Clif.Function} {vc vcp : VCode}
    (hs : lowerScopeB g = true) (hl : lowerFunction g = .ok vc)
    (hp : Backend.prepare vc = .ok vcp) :
    entryB g (stagePrepared g vc vcp) = true := by
  have hS := lowerScope_of hs
  have hdom := prepDomain_of_lower hS hl hS.nonempty
  obtain ⟨vb0, ds, hvb0, hi0, hds⟩ := vc_entry hS hl
  obtain ⟨vb, hvb, hi⟩ := prep_entry_args hp hdom hvb0 hi0
  obtain ⟨vb', hc, hhead⟩ := stagePrepared_entry_head (f := g) hdom hp hvb hi
  simp only [entryB, hc, hhead, List.all_eq_true, decide_eq_true_eq]
  exact hds

theorem outFits_stage_of_lower {P : Clif.Program} {g : Clif.Function} {vc vcp : VCode}
    (hd : dominatedB g = true) (hs : lowerScopeB g = true) (hos : outScopeB P g = true)
    (hl : lowerFunction g = .ok vc) (hp : Backend.prepare vc = .ok vcp) (rf : RFunc) :
    g.externs.all (fun e => !(P.func? e.2.name).isSome ||
      outFitsB e.2.sig (RAFrame.compute (stagePrepared g vc vcp) rf).intBase) = true := by
  have he : (RAFrame.compute (stagePrepared g vc vcp) rf).intBase =
      (RAFrame.compute vcp rf).intBase := by
    change alignTo (stagePrepared g vc vcp).outgoing 16 = alignTo vcp.outgoing 16
    rw [(stagePrepared_metadata g vc vcp).2.2.2.1]
  rw [he]
  exact outFits_of_lower hd hs hos hl hp rf

/-- Slot and outgoing metadata are unchanged; the emitted frame is checked against the actual
allocation of the stage's code, using the baseline source slot layout. -/
theorem frame_stage_of_lower {g : Clif.Function} {vc vcp : VCode} {a : Art}
    (hl : lowerFunction g = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hv : a.vcp = stagePrepared g vc vcp) (hr : lowerRFunc a.vcp a.rf = .ok a.af) :
    ((!g.slots.isEmpty || (RAFrame.compute a.vcp a.rf).size == a.af.frameSize) &&
      slotFitsB g a) = true := by
  obtain ⟨hfs, hsb, -⟩ := lowerRFunc_ok hr
  obtain ⟨hfs, hsb, -⟩ := hfs
  have hsl : a.vcp.slotBytes = (slotLayout g.slots).2 := by
    rw [hv, (stagePrepared_metadata g vc vcp).2.2.1]
    exact slotBytes_of_lower hl hp
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
