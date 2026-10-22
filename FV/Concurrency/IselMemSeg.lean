import FV.Concurrency.IselVar

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
    SegRes env p vc (csem F fc X) (cEvs F fc) Mt s (pre ++ evs :: rest2) cT := by
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
  · refine .inl ⟨(pre ++ evs :: rest2).length, [evsS], .run s', Nat.le_refl _, .cons hc .nil,
      ?_, .inl rfl⟩
    rw [List.take_length]
    exact corr_one hpe hpe' hcorr hS

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

theorem isRetsB_mapRegs (R : Reg → Reg) (i : MInst) : isRetsB (i.mapRegs R) = isRetsB i := by
  cases i <;> rfl

theorem instOkB_mapRegs {i : MInst} (h : instOkB i = true) : isRetsB i = false := by
  simp only [instOkB, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.2

theorem covered_of_instOkB {fc : FnCtx} {i : MInst} (h : instOkB i = true) : SegFoot.Covered fc i := by
  simp only [instOkB, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at h
  obtain ⟨⟨hc, hcall⟩, -⟩ := h
  refine ⟨fun info e => ?_, fun info ti e => ?_, ?_⟩
  · subst e; simp [isCallB] at hcall
  · subst e; simp [isCallB] at hcall
  · rcases hc with h | h
    · exact .inl h
    · exact .inr (by simpa [FormOk] using h)

/-- **The segment of a memory statement** (module doc). -/
theorem mem_seg (H : DriverHyp f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBl f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : ArmState}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hnp : pureInst stm.inst = false) {tr : List (List Ev)} {cT : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨b, k, ρ, w⟩) tr cT) :
    SegRes env p vc (csem F fc X) (cEvs F fc) (Match f ctx R gn bl A MR slots) s tr cT := by
  -- the statement, its lowering and its code
  obtain ⟨hcall, hfunc, hslots, hmr, B, j, hB, hterm, hj, hbd, hk, hheld, hcons⟩ := id hm
  simp only at hk hheld hcons hB hmr
  obtain ⟨hjlt, hstm, hrest⟩ := drop_cons_split (hbd ▸ hbody)
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨vb, hvb, hsllen, hstmts, -, -, -, -, hcode, htne, -⟩ := H.shape.blk b B L hB hL
  obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[j]? = some sl :=
    ⟨L.sl[j]'(by omega), List.getElem?_eq_getElem _⟩
  have hchkS := stmtOk_of hchk hB hstm hL hsl
  have hthr : threadInstB stm.inst = true := by
    simp only [stmtOkB, Bool.and_eq_true] at hchkS; exact hchkS.1.1.1
  obtain ⟨ks, nE, hexp⟩ : ∃ ks nE, SegShape.expect stm.inst = some (ks, nE) := by
    cases h : stm.inst <;> rw [h] at hthr hnp <;> simp [threadInstB, pureInst] at hthr hnp <;>
      exact ⟨_, _, rfl⟩
  obtain ⟨pre0, mi0, post0, hms, hpre0, hpost0, hks, hnE, hall, hcas⟩ := mem_split hchkS hexp
  have hsegat := seg_at hcode htne hjlt
  have hseg : seg f R bl b j =
      (pre0 ++ mi0 :: (post0 ++ extraOf stm.results sl.rss)).map (·.mapRegs R) := by
    rw [seg_eq hB hL hstm hsl, hms]; simp
  have hlen : (seg f R bl b j).length =
      pre0.length + 1 + (post0 ++ extraOf stm.results sl.rss).length := by
    rw [hseg]; simp; omega
  have hlt : k + (seg f R bl b j).length < vb.insts.size := by
    have := hsegat.2; rw [pos_succ] at this; rw [hk]; exact this
  have hat : ∀ i, i < (seg f R bl b j).length → vb.insts[k + i]? = (seg f R bl b j)[i]? :=
    fun i hi => by rw [hk, hsegat.1 i hi, List.getElem?_eq_getElem hi]
  -- the thread walks to the memory instruction
  have hpos : ∀ i < pre0.length, ∃ ins, vb.insts[k + i]? = some ins ∧ akinds ins = [] ∧
      isRetsB ins = false := by
    intro i hi
    refine ⟨(pre0[i]).mapRegs R, ?_, ?_, ?_⟩
    · rw [hat i (by omega), hseg, List.map_append, List.getElem?_append_left (by simpa using hi)]
      simp only [List.getElem?_map]
      rw [List.getElem?_eq_getElem hi]; rfl
    · rw [SegShape.akinds_mapRegs]; exact hpre0 _ (List.getElem_mem _)
    · rw [isRetsB_mapRegs]
      exact instOkB_mapRegs (hall _ (by rw [hms]; exact List.mem_append_left _ (List.getElem_mem _)))
  rcases vtrun_walk (F := F) (ctx := fc) (X := X) hvb pre0.length hpos (by omega) hr with
    ⟨ρm, wm, pre, rest1, htr, hpl, hpe, h1, h2, hwm⟩ | ⟨hl, hpe⟩
  rotate_left
  · exact .inl ⟨tr.length, [], .run s, Nat.le_refl _, .nil,
      (by rw [List.take_length]; exact corr_nil_tgts hpe), .inl rfl⟩
  cases h2 with
  | nil =>
    subst htr
    exact .inl ⟨_, [], .run s, Nat.le_refl _, .nil,
      (by rw [List.take_length, List.append_nil]; exact corr_nil_tgts hpe), .inl rfl⟩
  | @cons _ c'' _ evs rest2 hstep h3 =>
  sorry

end

end Concurrency.IselMemSeg
