import FV.Backend.Proof.SpillLocal
import FV.Backend.Proof.RegallocOperands
import FV.E2E.SizeVC
import FV.E2E.SizeLower
import FV.Backend.Proof.IselSzDriver
import FV.E2E.DeadCleanupTotal
import FV.Backend.Proof.DeadCleanupPrepare
import FV.Backend.Proof.CleanupStageFacts

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.DeadCleanup

private theorem sum_sublist {α : Type} (w : α → Nat) {xs ys : List α} (h : xs.Sublist ys) :
    (xs.map w).sum ≤ (ys.map w).sum := by
  induction h with
  | slnil => simp
  | cons h ih => simp only [List.map_cons, List.sum_cons]; omega
  | cons_cons h ih => simp only [List.map_cons, List.sum_cons]; omega

private theorem clean_size (vc : VCode) (M : Nat) :
    maxRC (clean vc) ≤ maxRC vc ∧ vcW M (clean vc) ≤ vcW M vc ∧ vcTg (clean vc) ≤ vcTg vc := by
  refine ⟨maxRC_le_iff.mpr ⟨five_le_maxRC vc,
    clean_insts (fun vb hb i hi => regCount_le_maxRC hb hi)⟩, ?_, ?_⟩
  · simp only [vcW, clean_blocks_map, Array.toList_map, List.map_map]
    apply sum_map_le'
    intro vb hb
    have h := sum_sublist szInstW (scan_sublist vc.classes.size
      vb.insts.toList (exitLive vc 0 vb))
    simp only [Function.comp_def, vbW, cleanBlock, wtA, wtL, List.toList_toArray] at *
    omega
  · simp only [vcTg, clean_blocks_map, Array.toList_map, List.map_map]
    apply sum_map_le'
    intro vb hb
    simpa [cleanBlock, tgA, tgL] using
      sum_sublist (fun i : MInst => i.targets.length)
        (scan_sublist vc.classes.size vb.insts.toList (exitLive vc 0 vb))

/-- Cleanup cannot increase any of the three measures used by the existing
input-side size proof. -/
theorem prune_size (vc : VCode) (M : Nat) :
    maxRC (prune vc) ≤ maxRC vc ∧ vcW M (prune vc) ≤ vcW M vc ∧ vcTg (prune vc) ≤ vcTg vc := by
  unfold prune
  cases vc.cfg with
  | error e => exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  | ok p => exact clean_size vc M

/-- A deleting block map cannot increase the three measures either. -/
private theorem delMap_size {T : VBlock → VBlock} (hT : DelMap T) (vc : VCode) (M : Nat) :
    maxRC (mapBlocks T vc) ≤ maxRC vc ∧ vcW M (mapBlocks T vc) ≤ vcW M vc ∧
      vcTg (mapBlocks T vc) ≤ vcTg vc := by
  refine ⟨maxRC_le_iff.mpr ⟨five_le_maxRC vc,
    hT.insts vc (fun vb hb i hi => regCount_le_maxRC hb hi)⟩, ?_, ?_⟩
  · simp only [vcW, mapBlocks_blocks, Array.toList_map, List.map_map]
    apply sum_map_le'
    intro vb hb
    have h := sum_sublist szInstW (hT.sub vb)
    have hba : (T vb).branchArgs.size = vb.branchArgs.size := by rw [hT.map.branchArgs]
    simp only [Function.comp_def, vbW, wtA, wtL] at *
    omega
  · simp only [vcTg, mapBlocks_blocks, Array.toList_map, List.map_map]
    apply sum_map_le'
    intro vb hb
    simpa [tgA, tgL] using sum_sublist (fun i : MInst => i.targets.length) (hT.sub vb)

/-- The production cleanup stage (the skip, then `prune`) cannot increase the measures. -/
theorem cleanupStage_size (f : Clif.Function) (vc : VCode) (M : Nat) :
    maxRC (cleanupStage f vc) ≤ maxRC vc ∧ vcW M (cleanupStage f vc) ≤ vcW M vc ∧
      vcTg (cleanupStage f vc) ≤ vcTg vc := by
  obtain ⟨a1, a2, a3⟩ := prune_size (skipStage f vc) M
  have hs := delMap_size (skipStage_delMap f vc) vc M
  rw [← skipStage_eq] at hs
  obtain ⟨b1, b2, b3⟩ := hs
  exact ⟨Nat.le_trans a1 b1, Nat.le_trans a2 b2, Nat.le_trans a3 b3⟩

/-- The baseline source size bound still bounds the cleanup pipeline. (`hp` is about the
production cleanup stage `cleanupStage f vc`, formerly `prune vc`.) -/
theorem spillWordBound_cleanup_le_sizeBoundIn {f : Clif.Function} {vc vcp : VCode}
    (hI : IselSz f) (hE : Compile.functionE f = true) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare (cleanupStage f vc) = .ok vcp) : spillWordBound vcp ≤ sizeBoundIn f := by
  obtain ⟨hM, hW, hT⟩ := size_lower hI hE hl
  obtain ⟨hMc, hWc, hTc⟩ := cleanupStage_size f vc (mIn f)
  have h1 := spillWordBound_le vcp
  have h2 := vcW_mono (Nat.le_trans (maxRC_prepare hp) (Nat.le_trans hMc hM)) vcp
  have h3 := vcW_prepare hp (mIn f)
  have h4 := Nat.mul_le_mul_left (jumpBW (mIn f)) (Nat.le_trans hTc hT)
  unfold sizeBoundIn
  omega

theorem spillSizeOkB_cleanup_of_sizeOkB {f : Clif.Function} {vc vcp : VCode}
    (hs : lowerScopeB f = true) (hsz : sizeOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare (cleanupStage f vc) = .ok vcp) :
    spillSizeOkB vcp = true := by
  have h := spillWordBound_cleanup_le_sizeBoundIn (iselSz (lowerScope_of hs))
    (lowerScope_of hs).subsetE hl hp
  have hs : sizeBoundIn f < 2 ^ 24 := of_decide_eq_true hsz
  exact decide_eq_true (by omega)

/-- The cleanup pipeline retains the baseline theorem with every code bound
on the source input, including total allocation, emission and layout. -/
theorem backend_correct_final_cleanup_total_emit_input {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (har : Spill.arityOkB f = true) (hw : extendsWidenB f = true) (hsz : sizeOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare (cleanupStage f vc) = .ok vcp)
    (ra : Except String RFunc) :
    ∃ af, lowerAllocReady vcp ra = .ok af ∧
      ∃ fa fb, emitFunc k af = .ok fa ∧ fa.layout = .ok fb ∧
      ∀ {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
        {K : Nat},
      ∀
        (hC : ∀ s, CalleeOk
          (frameW K (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).size af s) K X H
            vcp.CallSite)
        (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
          (frameW K (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).size af s) X H
            vcp.TrySite)
        (hTls : hasTls f = true → ∀ s, TlsOk
          (frameW K (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).size af s) K X H)
        (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
          Rel.holds ⟨frameW K (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).size af s, syms,
            slotOff, (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase⟩
            f sl cm w) X)
        (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
          Rel.holds ⟨frameW K (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).size af s, syms,
            slotOff, (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase⟩
            f sl cm w) X)
        (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
        (hslot : af.slotBase = slotOff)
        {base ra' : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
        (hent : AbiEntry fb base ra' s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
        (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
        (hrel : Rel.holds ⟨frameW K
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).size af s,
          syms, slotOff, (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase⟩
          f cs.frame.slots cs.mem w₀)
        (htr : TrapsExplicit env p cs) (fuel : Nat),
      ArmRefines fb base ra' (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) :=
  backend_correct_final_cleanup_total_emit_in hsub hd hs har hw hl hp
    (spillSizeOkB_cleanup_of_sizeOkB hs hsz hl hp) ra

end E2E
