import FV.Concurrency.IselMem

/-!
# The segment of a memory statement (T2h, #311, layer 2e)

* `mem_complete`: the end of a memory statement's segment — after the walk to the memory
  instruction and its step, the thread walks the rest of the segment (no events) and reaches
  the configuration the driver matches with the CLIF state after the statement
  (`IselStep.vtrun_patchN`, `vstepN_det`), or its run ends inside the segment; with the CLIF
  step's events corresponding to the memory step's, the segment's result follows.
-/

namespace Concurrency.IselMemSeg

open Arm ArmFoot ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread SegRun IselStep IselCheck IselSeg CorrRefine ClifCStepTerm IselThread IselMem Code

section
variable {vc : VCode} {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}

/-- **The end of a memory statement's segment** (module doc), with progress, the return covered
and the VCode end off `rets` (`SegResRN`). -/
theorem mem_completeRN {env : Clif.Env} {p : Clif.Program}
    {Mt : Clif.State → VState CV ArmState → Prop} {s s' : Clif.State} {b k : Nat}
    {ρ : Nat → CV} {w : ArmState} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) {L m : Nat}
    (hmL : m < L) (hlt : k + L < vb.insts.size)
    (hpost : ∀ i < L - (m + 1), ∃ ins, vb.insts[k + (m + 1) + i]? = some ins ∧ akinds ins = [] ∧
      isRetsB ins = false)
    {pre : List (List Ev)} {ρm : Nat → CV} {wm : ArmState} (hpl : pre.length = m)
    (hpe : ∀ e ∈ pre, e = [])
    (h1 : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨b, k, ρ, w⟩) pre (.run ⟨b, k + m, ρm, wm⟩))
    {evs : List Ev} {ρ'' : Nat → CV} {w'' : ArmState}
    (h2 : VTStep vc (csem F fc X) (cEvs F fc) (.run ⟨b, k + m, ρm, wm⟩) evs
      (.run ⟨b, k + m + 1, ρ'', w''⟩))
    {rest2 : List (List Ev)} {cT : VConf CV ArmState}
    (h3 : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨b, k + m + 1, ρ'', w''⟩) rest2 cT)
    {cL : VState CV ArmState}
    (hstar : StarN (VStep vc (csem F fc X)) L (patchC evs (.run ⟨b, k, ρ, w⟩)) (.run cL))
    (hML : Mt s' cL) {evsS : List (Prog.Ev SKind BVal)} (hc : CStep env p (.run s) evsS (.run s'))
    (hS : evsS ≠ []) (hcorr : PW (EvRel Maps) evsS (evs.map ProgE2E.convEv)) :
    SegResRN env p vc (csem F fc X) (cEvs F fc) Mt s (pre ++ evs :: rest2) cT := by
  rcases vtrun_walk (F := F) (ctx := fc) (X := X) hvb (L - (m + 1)) hpost (by omega) h3 with
    ⟨ρL, wL, post, rest3, htr, hl, hpe', h4, h5, -⟩ | ⟨hl, hpe'⟩
  · have hN := vtrun_patchN h1 hpe h2 h4 hpe'
    rw [hpl, hl, show m + 1 + (L - (m + 1)) = L by omega] at hN
    have e := vstepN_det hN hstar
    rw [show k + (m + 1) + (L - (m + 1)) = k + L by omega] at e h5
    cases e
    have htr' : pre ++ evs :: rest2 = (pre ++ evs :: post) ++ rest3 := by rw [htr]; simp
    have hlen : (pre ++ evs :: post).length = L := by simp; omega
    refine .inr ⟨L, [evsS], s', _, ?_, .cons hc .nil, ?_, hML, ?_, .inl (by omega)⟩
    · rw [htr']; simp; omega
    · rw [htr', List.take_left' hlen]
      exact corr_one hpe hpe' hcorr hS
    · rw [htr', List.drop_left' hlen]
      exact h5
  · have hN := vtrun_patchN h1 hpe h2 h3 hpe'
    rw [hpl] at hN
    have hcorr1 : Corr Maps [evsS] (conv ((pre ++ evs :: rest2).take
        (pre ++ evs :: rest2).length)) := by
      rw [List.take_length]
      exact corr_one hpe hpe' hcorr hS
    rcases vstep_of_starNR (retsRet_csem F fc X) hN hstar (by omega) with ⟨hv, hnr⟩ | ⟨hlen, e⟩
    · exact .inl ⟨(pre ++ evs :: rest2).length, [evsS], .run s', Nat.le_refl _, .cons hc .nil,
        hcorr1, .inl ⟨rfl, hv, hnr⟩, fun _ h => by cases h⟩
    · subst e
      have hlen' : (pre ++ evs :: rest2).length = L := by simp; omega
      refine .inr ⟨L, [evsS], s', _, by omega, .cons hc .nil, ?_, hML, ?_, .inl (by omega)⟩
      · rw [← hlen']; exact hcorr1
      · rw [← hlen', List.drop_length]; exact .nil

/-- **The end of a memory statement's segment** (module doc), with progress and the return covered
(`SegResR`). -/
theorem mem_completeR {env : Clif.Env} {p : Clif.Program}
    {Mt : Clif.State → VState CV ArmState → Prop} {s s' : Clif.State} {b k : Nat}
    {ρ : Nat → CV} {w : ArmState} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) {L m : Nat}
    (hmL : m < L) (hlt : k + L < vb.insts.size)
    (hpost : ∀ i < L - (m + 1), ∃ ins, vb.insts[k + (m + 1) + i]? = some ins ∧ akinds ins = [] ∧
      isRetsB ins = false)
    {pre : List (List Ev)} {ρm : Nat → CV} {wm : ArmState} (hpl : pre.length = m)
    (hpe : ∀ e ∈ pre, e = [])
    (h1 : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨b, k, ρ, w⟩) pre (.run ⟨b, k + m, ρm, wm⟩))
    {evs : List Ev} {ρ'' : Nat → CV} {w'' : ArmState}
    (h2 : VTStep vc (csem F fc X) (cEvs F fc) (.run ⟨b, k + m, ρm, wm⟩) evs
      (.run ⟨b, k + m + 1, ρ'', w''⟩))
    {rest2 : List (List Ev)} {cT : VConf CV ArmState}
    (h3 : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨b, k + m + 1, ρ'', w''⟩) rest2 cT)
    {cL : VState CV ArmState}
    (hstar : StarN (VStep vc (csem F fc X)) L (patchC evs (.run ⟨b, k, ρ, w⟩)) (.run cL))
    (hML : Mt s' cL) {evsS : List (Prog.Ev SKind BVal)} (hc : CStep env p (.run s) evsS (.run s'))
    (hS : evsS ≠ []) (hcorr : PW (EvRel Maps) evsS (evs.map ProgE2E.convEv)) :
    SegResR env p vc (csem F fc X) (cEvs F fc) Mt s (pre ++ evs :: rest2) cT :=
  (mem_completeRN hvb hmL hlt hpost hpl hpe h1 h2 h3 hstar hML hc hS hcorr).toR

/-- **The end of a memory statement's segment** (module doc), with progress (`SegResP`). -/
theorem mem_completeP {env : Clif.Env} {p : Clif.Program}
    {Mt : Clif.State → VState CV ArmState → Prop} {s s' : Clif.State} {b k : Nat}
    {ρ : Nat → CV} {w : ArmState} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) {L m : Nat}
    (hmL : m < L) (hlt : k + L < vb.insts.size)
    (hpost : ∀ i < L - (m + 1), ∃ ins, vb.insts[k + (m + 1) + i]? = some ins ∧ akinds ins = [] ∧
      isRetsB ins = false)
    {pre : List (List Ev)} {ρm : Nat → CV} {wm : ArmState} (hpl : pre.length = m)
    (hpe : ∀ e ∈ pre, e = [])
    (h1 : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨b, k, ρ, w⟩) pre (.run ⟨b, k + m, ρm, wm⟩))
    {evs : List Ev} {ρ'' : Nat → CV} {w'' : ArmState}
    (h2 : VTStep vc (csem F fc X) (cEvs F fc) (.run ⟨b, k + m, ρm, wm⟩) evs
      (.run ⟨b, k + m + 1, ρ'', w''⟩))
    {rest2 : List (List Ev)} {cT : VConf CV ArmState}
    (h3 : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨b, k + m + 1, ρ'', w''⟩) rest2 cT)
    {cL : VState CV ArmState}
    (hstar : StarN (VStep vc (csem F fc X)) L (patchC evs (.run ⟨b, k, ρ, w⟩)) (.run cL))
    (hML : Mt s' cL) {evsS : List (Prog.Ev SKind BVal)} (hc : CStep env p (.run s) evsS (.run s'))
    (hS : evsS ≠ []) (hcorr : PW (EvRel Maps) evsS (evs.map ProgE2E.convEv)) :
    SegResP env p vc (csem F fc X) (cEvs F fc) Mt s (pre ++ evs :: rest2) cT :=
  (mem_completeR hvb hmL hlt hpost hpl hpe h1 h2 h3 hstar hML hc hS hcorr).segResP

/-- **The end of a memory statement's segment** (module doc). -/
theorem mem_complete {env : Clif.Env} {p : Clif.Program}
    {Mt : Clif.State → VState CV ArmState → Prop} {s s' : Clif.State} {b k : Nat}
    {ρ : Nat → CV} {w : ArmState} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) {L m : Nat}
    (hmL : m < L) (hlt : k + L < vb.insts.size)
    (hpost : ∀ i < L - (m + 1), ∃ ins, vb.insts[k + (m + 1) + i]? = some ins ∧ akinds ins = [] ∧
      isRetsB ins = false)
    {pre : List (List Ev)} {ρm : Nat → CV} {wm : ArmState} (hpl : pre.length = m)
    (hpe : ∀ e ∈ pre, e = [])
    (h1 : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨b, k, ρ, w⟩) pre (.run ⟨b, k + m, ρm, wm⟩))
    {evs : List Ev} {ρ'' : Nat → CV} {w'' : ArmState}
    (h2 : VTStep vc (csem F fc X) (cEvs F fc) (.run ⟨b, k + m, ρm, wm⟩) evs
      (.run ⟨b, k + m + 1, ρ'', w''⟩))
    {rest2 : List (List Ev)} {cT : VConf CV ArmState}
    (h3 : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨b, k + m + 1, ρ'', w''⟩) rest2 cT)
    {cL : VState CV ArmState}
    (hstar : StarN (VStep vc (csem F fc X)) L (patchC evs (.run ⟨b, k, ρ, w⟩)) (.run cL))
    (hML : Mt s' cL) {evsS : List (Prog.Ev SKind BVal)} (hc : CStep env p (.run s) evsS (.run s'))
    (hS : evsS ≠ []) (hcorr : PW (EvRel Maps) evsS (evs.map ProgE2E.convEv)) :
    SegRes env p vc (csem F fc X) (cEvs F fc) Mt s (pre ++ evs :: rest2) cT :=
  (mem_completeP hvb hmL hlt hpost hpl hpe h1 h2 h3 hstar hML hc hS hcorr).segRes

end

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
  {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {MR : MemRelT} {env : Clif.Env}
  {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {sb : Nat} {syms : String → Option Nat}

/-- **The static facts of a memory statement's segment**: its code splits around its one
memory instruction. -/
theorem mem_split {inst : Clif.Inst} {ms : List MInst} (hok : stmtOkB inst ms = true)
    {ks : List AKind} {nE : Nat} (hexp : SegShape.expect inst = some (ks, nE)) :
    ∃ pre0 mi0 post0, ms = pre0 ++ mi0 :: post0 ∧ (∀ y ∈ pre0, akinds y = []) ∧
      (∀ y ∈ post0, akinds y = []) ∧ akinds mi0 = ks ∧
      (ks = [.dmb] ∨ SegShape.memBytes mi0 = some nE) ∧ (∀ i ∈ ms, instOkB i = true) ∧
      casOkB inst ms = true := by
  simp only [stmtOkB, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨-, hsh⟩, hall⟩, hcas⟩ := hok
  unfold SegShape.segShape at hsh
  rw [hexp] at hsh
  simp only at hsh
  split at hsh
  · rename_i mi0 hmi
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hsh
    obtain ⟨hk, hb⟩ := hsh
    obtain ⟨pre0, post0, rfl, h1, h2, h3⟩ := filter_eq_singleton hmi
    refine ⟨pre0, mi0, post0, rfl, fun y hy => ?_, fun y hy => ?_, hk, ?_,
      List.all_eq_true.mp hall, hcas⟩
    · simpa using h1 y hy
    · simpa using h2 y hy
    · rcases hb with hb | hb
      · exact .inl (by simpa using hb)
      · exact .inr hb
  · cases hsh

end

end Concurrency.IselMemSeg
