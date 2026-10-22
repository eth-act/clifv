import FV.Concurrency.IselMemHelp

/-!
# The segment of a memory statement (T2h, #311, layer 2e)

**`mem_seg`**: from a match at a memory statement, a VCode thread run is realized: the thread
walks to the statement's one memory instruction without events (`IselSeg.vtrun_walk`); the
instruction's events are the CLIF access (`IselVar.events_at_access` on the matched pair with
the CLIF access holding the world's own bytes, `IselSeg.mr_own`); both memories patched with the
bytes the thread read keep the memory relation (`IselSeg.mr_patch`), so the driver's step from
the patched pair (`IselStep.stmt_matchN`) is the thread's segment (`IselMemSeg.mem_complete`) and
the CLIF step reading those bytes (`ClifCStep`) has the thread's events.
-/

namespace Concurrency.IselMemMain

open Arm ArmFoot ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread SegRun IselStep IselCheck IselSeg CorrRefine ClifCStepTerm IselThread IselMem Code
  IselMemSeg IselMemHelp

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
  {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {MR : MemRelT} {env : Clif.Env}
  {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {sb : Nat} {syms : String → Option Nat}

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

end Concurrency.IselMemMain
