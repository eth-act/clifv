import FV.Concurrency.IselCall

/-!
# Layer 2 pausing at calls and returns (#473, the `rets` end)

`IselCall.isel_refinesC` pauses at call statements. An activation's contract at its return
(the callee contract `Ret` of the generic call theorem) needs layer 2's relation at the CLIF
`return`, so the variant here also pauses there:

* `AtRetS s`: the CLIF state is at a `return` terminator;
* `SimResP`/`SegResP`, `simResP_of_seg`: `SimResC`/`SegResC`/`simResC_of_seg` with the pause
  predicate a parameter;
* **`seg_resCR`**, **`isel_refinesCR`**, **`isel_refines_entryCR`**: as `seg_resC`,
  `isel_refinesC`, `isel_refines_entryC`, pausing at a call statement or a `return` (`AtCR`),
  related by `Match` to a VCode configuration from which the rest of the trace runs.
-/

namespace Concurrency.IselCallRet

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine IselStep IselCall

/-- The CLIF state is at a `return` terminator. -/
def AtRetS (s : Clif.State) : Prop :=
  s.frame.body = [] ∧ ∃ xs, s.frame.term = .ret xs

/-- At a call statement or a `return`. -/
def AtCR (s : Clif.State) : Prop := AtCallS s ∨ AtRetS s

/-- **`SimResC` with the pause predicate `Pz`** (module doc). -/
def SimResP (env : Clif.Env) (p : Clif.Program) (vc : VCode) (sem : ISem CV ArmState)
    (ev : MInst → List CV → ArmState → List Ev) (Pz : Clif.State → Prop)
    (Mt : Clif.State → VState CV ArmState → Prop) (s : Clif.State) (tr : List (List Ev))
    (cT : VConf CV ArmState) : Prop :=
  ∃ n trS t, n ≤ tr.length ∧ CRun env p (.run s) trS t ∧ Corr Maps trS (conv (tr.take n)) ∧
    ((((n = tr.length ∧ ∃ c', VStep vc sem cT c') ∨ Stop env p t) ∧
        ∀ v, t = .ret v → n = tr.length) ∨
      ∃ s' vs', t = .run s' ∧ Pz s' ∧ Mt s' vs' ∧ VTRun vc sem ev (.run vs') (tr.drop n) cT)

/-- `SegResC` with the pause predicate `Pz`. -/
def SegResP (env : Clif.Env) (p : Clif.Program) (vc : VCode) (sem : ISem CV ArmState)
    (ev : MInst → List CV → ArmState → List Ev) (Pz : Clif.State → Prop)
    (Mt : Clif.State → VState CV ArmState → Prop) (s : Clif.State) (tr : List (List Ev))
    (cT : VConf CV ArmState) : Prop :=
  SimResP env p vc sem ev Pz Mt s tr cT ∨
  ∃ n trS s' vs', n ≤ tr.length ∧ CRun env p (.run s) trS (.run s') ∧
    Corr Maps trS (conv (tr.take n)) ∧ Mt s' vs' ∧ VTRun vc sem ev (.run vs') (tr.drop n) cT ∧
    (0 < n ∨ s'.frame.body.length < s.frame.body.length)

section
variable {env : Clif.Env} {p : Clif.Program} {vc : VCode} {sem : ISem CV ArmState}
  {ev : MInst → List CV → ArmState → List Ev} {Mt : Clif.State → VState CV ArmState → Prop}
  {Pz : Clif.State → Prop}

theorem SegResR.segResP {s : Clif.State} {tr : List (List Ev)} {cT : VConf CV ArmState}
    (h : SegResR env p vc sem ev Mt s tr cT) : SegResP env p vc sem ev Pz Mt s tr cT := by
  rcases h with ⟨n, trS, t, hn, hrun, hcorr, hend, hret⟩ | h
  · exact .inl ⟨n, trS, t, hn, hrun, hcorr, .inl ⟨hend, hret⟩⟩
  · exact .inr h

/-- **Segment results with pauses compose** (`IselCall.simResC_of_seg`). -/
theorem simResP_of_seg
    (hseg : ∀ s c tr cT, Mt s c → VTRun vc sem ev (.run c) tr cT →
      SegResP env p vc sem ev Pz Mt s tr cT)
    (s : Clif.State) (c : VState CV ArmState) (tr : List (List Ev)) (cT : VConf CV ArmState)
    (hm : Mt s c) (hr : VTRun vc sem ev (.run c) tr cT) :
    SimResP env p vc sem ev Pz Mt s tr cT := by
  rcases hseg s c tr cT hm hr with h | ⟨n, trS, s', vs', hn, hrun, hcorr, hm', hr', hprog⟩
  · exact h
  · obtain ⟨n', trS', t', hn', hrun', hcorr', hend⟩ :=
      simResP_of_seg hseg s' vs' (tr.drop n) cT hm' hr'
    refine ⟨n + n', trS ++ trS', t', ?_, hrun.append hrun', ?_, ?_⟩
    · simp at hn'; omega
    · rw [List.take_add, conv_append]
      exact hcorr.append hcorr'
    · rcases hend with ⟨hend, hret⟩ | ⟨s2, vs2, ht, hat, hm2, hr2⟩
      · refine .inl ⟨?_, fun v hv => ?_⟩
        · rcases hend with ⟨h, hv⟩ | h
          · left; simp at h; exact ⟨by omega, hv⟩
          · exact .inr h
        · have := hret v hv
          simp at this; omega
      · refine .inr ⟨s2, vs2, ht, hat, hm2, ?_⟩
        rw [List.drop_drop] at hr2
        simpa only [Nat.add_comm] using hr2
termination_by (tr.length, s.frame.body.length)
decreasing_by
  rcases hprog with h | h
  · exact Prod.Lex.left _ _ (by simp; omega)
  · by_cases h0 : n = 0
    · subst h0; simp only [List.drop_zero]; exact Prod.Lex.right _ h
    · exact Prod.Lex.left _ _ (by simp; omega)

end

/-- **`SimResP` with the VCode end off `rets`** (#473; `IselThread.SimResRN`'s first case). -/
def SimResPN (env : Clif.Env) (p : Clif.Program) (vc : VCode) (sem : ISem CV ArmState)
    (ev : MInst → List CV → ArmState → List Ev) (Pz : Clif.State → Prop)
    (Mt : Clif.State → VState CV ArmState → Prop) (s : Clif.State) (tr : List (List Ev))
    (cT : VConf CV ArmState) : Prop :=
  ∃ n trS t, n ≤ tr.length ∧ CRun env p (.run s) trS t ∧ Corr Maps trS (conv (tr.take n)) ∧
    ((((n = tr.length ∧ (∃ c', VStep vc sem cT c') ∧ ¬ VAtRets vc cT) ∨ Stop env p t) ∧
        ∀ v, t = .ret v → n = tr.length) ∨
      ∃ s' vs', t = .run s' ∧ Pz s' ∧ Mt s' vs' ∧ VTRun vc sem ev (.run vs') (tr.drop n) cT)

/-- `SegResP` with `SimResPN` in place of `SimResP`. -/
def SegResPN (env : Clif.Env) (p : Clif.Program) (vc : VCode) (sem : ISem CV ArmState)
    (ev : MInst → List CV → ArmState → List Ev) (Pz : Clif.State → Prop)
    (Mt : Clif.State → VState CV ArmState → Prop) (s : Clif.State) (tr : List (List Ev))
    (cT : VConf CV ArmState) : Prop :=
  SimResPN env p vc sem ev Pz Mt s tr cT ∨
  ∃ n trS s' vs', n ≤ tr.length ∧ CRun env p (.run s) trS (.run s') ∧
    Corr Maps trS (conv (tr.take n)) ∧ Mt s' vs' ∧ VTRun vc sem ev (.run vs') (tr.drop n) cT ∧
    (0 < n ∨ s'.frame.body.length < s.frame.body.length)

section
variable {env : Clif.Env} {p : Clif.Program} {vc : VCode} {sem : ISem CV ArmState}
  {ev : MInst → List CV → ArmState → List Ev} {Mt : Clif.State → VState CV ArmState → Prop}
  {Pz : Clif.State → Prop}

theorem SegResRN.segResPN {s : Clif.State} {tr : List (List Ev)} {cT : VConf CV ArmState}
    (h : SegResRN env p vc sem ev Mt s tr cT) : SegResPN env p vc sem ev Pz Mt s tr cT := by
  rcases h with ⟨n, trS, t, hn, hrun, hcorr, hend, hret⟩ | h
  · exact .inl ⟨n, trS, t, hn, hrun, hcorr, .inl ⟨hend, hret⟩⟩
  · exact .inr h

/-- **Segment results off `rets` with pauses compose** (`simResP_of_seg`). -/
theorem simResPN_of_seg
    (hseg : ∀ s c tr cT, Mt s c → VTRun vc sem ev (.run c) tr cT →
      SegResPN env p vc sem ev Pz Mt s tr cT)
    (s : Clif.State) (c : VState CV ArmState) (tr : List (List Ev)) (cT : VConf CV ArmState)
    (hm : Mt s c) (hr : VTRun vc sem ev (.run c) tr cT) :
    SimResPN env p vc sem ev Pz Mt s tr cT := by
  rcases hseg s c tr cT hm hr with h | ⟨n, trS, s', vs', hn, hrun, hcorr, hm', hr', hprog⟩
  · exact h
  · obtain ⟨n', trS', t', hn', hrun', hcorr', hend⟩ :=
      simResPN_of_seg hseg s' vs' (tr.drop n) cT hm' hr'
    refine ⟨n + n', trS ++ trS', t', ?_, hrun.append hrun', ?_, ?_⟩
    · simp at hn'; omega
    · rw [List.take_add, conv_append]
      exact hcorr.append hcorr'
    · rcases hend with ⟨hend, hret⟩ | ⟨s2, vs2, ht, hat, hm2, hr2⟩
      · refine .inl ⟨?_, fun v hv => ?_⟩
        · rcases hend with ⟨h, hv⟩ | h
          · left; simp at h; exact ⟨by omega, hv⟩
          · exact .inr h
        · have := hret v hv
          simp at this; omega
      · refine .inr ⟨s2, vs2, ht, hat, hm2, ?_⟩
        rw [List.drop_drop] at hr2
        simpa only [Nat.add_comm] using hr2
termination_by (tr.length, s.frame.body.length)
decreasing_by
  rcases hprog with h | h
  · exact Prod.Lex.left _ _ (by simp; omega)
  · by_cases h0 : n = 0
    · subst h0; simp only [List.drop_zero]; exact Prod.Lex.right _ h
    · exact Prod.Lex.left _ _ (by simp; omega)

end

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
  {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {MR : MemRelT} {env : Clif.Env}
  {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {sb : Nat} {syms : String → Option Nat}

/-- **Every segment from a match has its result, pausing at calls and returns** (module doc). -/
theorem seg_resCR (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X) (s : Clif.State) (c : VState CV ArmState) (tr : List (List Ev))
    (cT : VConf CV ArmState) (hm : Match f ctx R gn bl A MR slots s c)
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run c) tr cT) :
    SegResP env p vc (csem F fc X) (cEvs F fc) AtCR (Match f ctx R gn bl A MR slots) s tr cT := by
  by_cases hret : AtRetS s
  · exact .inl ⟨0, [], .run s, Nat.zero_le _, .nil, .nil,
      .inr ⟨s, c, rfl, .inr hret, hm, by simpa using hr⟩⟩
  rcases seg_resC (env := env) H hchk hMR hMRw hX s c tr cT hm hr with
    ⟨n, trS, t, hn, hrun, hcorr, hend⟩ | h
  · refine .inl ⟨n, trS, t, hn, hrun, hcorr, ?_⟩
    rcases hend with h | ⟨s', vs', ht, hat, hm', hr'⟩
    · exact .inl h
    · exact .inr ⟨s', vs', ht, .inl hat, hm', hr'⟩
  · exact .inr h

/-- **Layer 2 from a match, pausing at calls and returns** (module doc). -/
theorem isel_refinesCR (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X) {s : Clif.State} {c : VState CV ArmState}
    (hm : Match f ctx R gn bl A MR slots s c) {tr : List (List Ev)} {cT : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run c) tr cT) :
    ∃ n trS t ψ, n ≤ tr.length ∧ CRun env p (.run s) trS t ∧
      Refines Maps (fun _ => False) (StepPair (conv (tr.take n))) trS (conv (tr.take n)) ψ ∧
      ((((n = tr.length ∧ ∃ c', VStep vc (csem F fc X) cT c') ∨ Stop env p t) ∧
          ∀ v, t = .ret v → n = tr.length) ∨
        ∃ s' vs', t = .run s' ∧ AtCR s' ∧ Match f ctx R gn bl A MR slots s' vs' ∧
          VTRun vc (csem F fc X) (cEvs F fc) (.run vs') (tr.drop n) cT) := by
  obtain ⟨n, trS, t, hn, hrun, hcorr, hend⟩ :=
    simResP_of_seg (seg_resCR H hchk hMR hMRw hX) s c tr cT hm hr
  obtain ⟨ψ, href⟩ := refines_of_corr hcorr hrun.length_le
  exact ⟨n, trS, t, ψ, hn, hrun, href, hend⟩

/-- **Layer 2 from the function's entry, pausing at calls and returns** (module doc; as
`IselCall.isel_refines_entryC`). -/
theorem isel_refines_entryCR (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X) (hMem : MemRefines F sb syms (csem F fc X)) (hMRs : MRStable F MR)
    (hreg : ∀ off, ArgLoc.stack off ∉ locsOf f.sig)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) {tr : List (List Ev)} {cT : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨0, 0, ρ₀, w₀⟩) tr cT) :
    ∃ n trS t ψ, n ≤ tr.length ∧ CRun env p (.run cs) trS t ∧
      Refines Maps (fun _ => False) (StepPair (conv (tr.take n))) trS (conv (tr.take n)) ψ ∧
      ((((n = tr.length ∧ ∃ c', VStep vc (csem F fc X) cT c') ∨ Stop env p t) ∧
          ∀ v, t = .ret v → n = tr.length) ∨
        ∃ s' vs', t = .run s' ∧ AtCR s' ∧ Match f ctx R gn bl A MR slots s' vs' ∧
          VTRun vc (csem F fc X) (cEvs F fc) (.run vs') (tr.drop n) cT) := by
  obtain ⟨vb, ps, ρ₁, ρ₂, w₂, hvb, hvb0, hstep, hseq, hm⟩ :=
    IselEntry.entry_matchNT H (driverSem_csem F fc X) hMem hMRs hB0 hcall hfunc hslots hbody
      hterm hregs hty hsig hmr hargs
  rw [IselEntry.entryLoads_nil hreg] at hseq hm
  simp only [seqRun, Option.some.injEq, SeqEnd.fall.injEq] at hseq
  obtain ⟨rfl, rfl⟩ := hseq
  have hsim : SimResP env p vc (csem F fc X) (cEvs F fc) AtCR (Match f ctx R gn bl A MR slots) cs
      tr cT := by
    cases hr with
    | nil => exact ⟨0, [], .run cs, Nat.le_refl _, .nil, .nil, .inl ⟨.inl ⟨rfl, _, hstep⟩,
        fun _ h => by cases h⟩⟩
    | @cons _ c' _ evs tr' hs hr' =>
      obtain ⟨vb', i, ops, hb', hi, -, hev, -, hst⟩ := IselMemMain.vtstep_evs hs
      rw [hvb] at hb'; cases hb'
      rw [hvb0] at hi; cases hi
      have he : evs = [] := hev.trans (VCodeEvents.cEvs_nil rfl _ _)
      subst he
      have e := vstep_det hst hstep
      subst e
      obtain ⟨n, trS, t, hn, hrun, hcorr, hend⟩ :=
        simResP_of_seg (seg_resCR H hchk hMR hMRw hX) cs _ tr' cT hm hr'
      refine ⟨n + 1, trS, t, by simp; omega, hrun, ?_, ?_⟩
      · simpa [conv] using hcorr.tgt
      · rcases hend with ⟨hend, hret⟩ | ⟨s', vs', ht, hat, hm', hr2⟩
        · refine .inl ⟨?_, fun v hv => by simp [hret v hv]⟩
          rcases hend with ⟨h, hv⟩ | h
          · exact .inl ⟨by simp [h], hv⟩
          · exact .inr h
        · exact .inr ⟨s', vs', ht, hat, hm', by simpa using hr2⟩
  obtain ⟨n, trS, t, hn, hrun, hcorr, hend⟩ := hsim
  obtain ⟨ψ, href⟩ := refines_of_corr hcorr hrun.length_le
  exact ⟨n, trS, t, ψ, hn, hrun, href, hend⟩

/-- **Every segment from a match has its result, pausing at calls and returns, the VCode end off
`rets`** (`seg_resCR` with `IselThread.pure_segRTN`, `term_segRTN`, `IselMemMain.mem_segRTN`). -/
theorem seg_resCRN (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X) (s : Clif.State) (c : VState CV ArmState) (tr : List (List Ev))
    (cT : VConf CV ArmState) (hm : Match f ctx R gn bl A MR slots s c)
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run c) tr cT) :
    SegResPN env p vc (csem F fc X) (cEvs F fc) AtCR (Match f ctx R gn bl A MR slots) s tr cT := by
  by_cases hret : AtRetS s
  · exact .inl ⟨0, [], .run s, Nat.zero_le _, .nil, .nil,
      .inr ⟨s, c, rfl, .inr hret, hm, by simpa using hr⟩⟩
  obtain ⟨b, k, ρ, w⟩ := c
  cases hbody : s.frame.body with
  | nil => exact SegResRN.segResPN (term_segRTN H hchk hm hbody hr)
  | cons stm rest =>
    by_cases hc : ∃ fn args, stm.inst = .call fn args
    · obtain ⟨fn, args, hc⟩ := hc
      exact .inl ⟨0, [], .run s, Nat.zero_le _, .nil, .nil,
        .inr ⟨s, _, rfl, .inl ⟨stm, rest, fn, args, hbody, hc⟩, hm, by simpa using hr⟩⟩
    · have hnc : ∀ fn args, stm.inst ≠ .call fn args := fun fn args h => hc ⟨fn, args, h⟩
      cases hp : pureInst stm.inst
      · exact SegResRN.segResPN (IselMemMain.mem_segRTN H hchk hMR hMRw hX hm hbody hp hnc hr)
      · exact SegResRN.segResPN (pure_segRTN H hchk hm hbody hp hr)

/-- **Layer 2 from a match, pausing at calls and returns, the VCode end off `rets`**
(`isel_refinesCR` with the end of a realized run with a VCode step not at a `rets`). -/
theorem isel_refinesCRN (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X) {s : Clif.State} {c : VState CV ArmState}
    (hm : Match f ctx R gn bl A MR slots s c) {tr : List (List Ev)} {cT : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run c) tr cT) :
    ∃ n trS t ψ, n ≤ tr.length ∧ CRun env p (.run s) trS t ∧
      Refines Maps (fun _ => False) (StepPair (conv (tr.take n))) trS (conv (tr.take n)) ψ ∧
      ((((n = tr.length ∧ (∃ c', VStep vc (csem F fc X) cT c') ∧ ¬ VAtRets vc cT) ∨
          Stop env p t) ∧ ∀ v, t = .ret v → n = tr.length) ∨
        ∃ s' vs', t = .run s' ∧ AtCR s' ∧ Match f ctx R gn bl A MR slots s' vs' ∧
          VTRun vc (csem F fc X) (cEvs F fc) (.run vs') (tr.drop n) cT) := by
  obtain ⟨n, trS, t, hn, hrun, hcorr, hend⟩ :=
    simResPN_of_seg (seg_resCRN H hchk hMR hMRw hX) s c tr cT hm hr
  obtain ⟨ψ, href⟩ := refines_of_corr hcorr hrun.length_le
  exact ⟨n, trS, t, ψ, hn, hrun, href, hend⟩

/-- **Layer 2 from the function's entry, pausing at calls and returns, the VCode end off
`rets`** (`isel_refines_entryCR`). -/
theorem isel_refines_entryCRN (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X) (hMem : MemRefines F sb syms (csem F fc X)) (hMRs : MRStable F MR)
    (hreg : ∀ off, ArgLoc.stack off ∉ locsOf f.sig)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) {tr : List (List Ev)} {cT : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨0, 0, ρ₀, w₀⟩) tr cT) :
    ∃ n trS t ψ, n ≤ tr.length ∧ CRun env p (.run cs) trS t ∧
      Refines Maps (fun _ => False) (StepPair (conv (tr.take n))) trS (conv (tr.take n)) ψ ∧
      ((((n = tr.length ∧ (∃ c', VStep vc (csem F fc X) cT c') ∧ ¬ VAtRets vc cT) ∨
          Stop env p t) ∧ ∀ v, t = .ret v → n = tr.length) ∨
        ∃ s' vs', t = .run s' ∧ AtCR s' ∧ Match f ctx R gn bl A MR slots s' vs' ∧
          VTRun vc (csem F fc X) (cEvs F fc) (.run vs') (tr.drop n) cT) := by
  obtain ⟨vb, ps, ρ₁, ρ₂, w₂, hvb, hvb0, hstep, hseq, hm⟩ :=
    IselEntry.entry_matchNT H (driverSem_csem F fc X) hMem hMRs hB0 hcall hfunc hslots hbody
      hterm hregs hty hsig hmr hargs
  rw [IselEntry.entryLoads_nil hreg] at hseq hm
  simp only [seqRun, Option.some.injEq, SeqEnd.fall.injEq] at hseq
  obtain ⟨rfl, rfl⟩ := hseq
  have hsim : SimResPN env p vc (csem F fc X) (cEvs F fc) AtCR (Match f ctx R gn bl A MR slots)
      cs tr cT := by
    cases hr with
    | nil =>
      refine ⟨0, [], .run cs, Nat.le_refl _, .nil, .nil, .inl ⟨.inl ⟨rfl, ⟨_, hstep⟩, ?_⟩,
        fun _ h => by cases h⟩⟩
      rintro ⟨b, k, ρ, w, vb', us, he, hb, hi⟩
      cases he
      rw [hvb] at hb; cases hb
      rw [hvb0] at hi; cases hi
    | @cons _ c' _ evs tr' hs hr' =>
      obtain ⟨vb', i, ops, hb', hi, -, hev, -, hst⟩ := IselMemMain.vtstep_evs hs
      rw [hvb] at hb'; cases hb'
      rw [hvb0] at hi; cases hi
      have he : evs = [] := hev.trans (VCodeEvents.cEvs_nil rfl _ _)
      subst he
      have e := vstep_det hst hstep
      subst e
      obtain ⟨n, trS, t, hn, hrun, hcorr, hend⟩ :=
        simResPN_of_seg (seg_resCRN H hchk hMR hMRw hX) cs _ tr' cT hm hr'
      refine ⟨n + 1, trS, t, by simp; omega, hrun, ?_, ?_⟩
      · simpa [conv] using hcorr.tgt
      · rcases hend with ⟨hend, hret⟩ | ⟨s', vs', ht, hat, hm', hr2⟩
        · refine .inl ⟨?_, fun v hv => by simp [hret v hv]⟩
          rcases hend with ⟨h, hv⟩ | h
          · exact .inl ⟨by simp [h], hv⟩
          · exact .inr h
        · exact .inr ⟨s', vs', ht, hat, hm', by simpa using hr2⟩
  obtain ⟨n, trS, t, hn, hrun, hcorr, hend⟩ := hsim
  obtain ⟨ψ, href⟩ := refines_of_corr hcorr hrun.length_le
  exact ⟨n, trS, t, ψ, hn, hrun, href, hend⟩

end

end Concurrency.IselCallRet
