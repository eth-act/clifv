import FV.Concurrency.IselEntry

/-!
# Layer 2 pausing at calls (#473, (2a) of the generic call theorem)

Layer 2's induction (`IselThread.simResR_of_seg`) covers statements that it runs as one CLIF
step. A call of a function of the program is not one: the CLIF thread pushes the callee's frame,
whose run is the callee's (its own refinement, composed by `CallCompose.link_compose`). So the
caller's layer 2 **pauses** at a call statement, with its relation there:

* `AtCallS s`: the CLIF state is at a `call` statement;
* **`SimResC`**/`SegResC`: `SimResR`/`SegResR` with a third end, the realized prefix ending at a
  call statement whose state is related (`Mt`) to a VCode configuration from which the rest of
  the trace runs; `SegResR.segResC`, **`simResC_of_seg`** (segment results compose);
* **`seg_resC`**: every segment from a match has its `SegResC`, on `DriverHypT` (no extern-only
  calls) and the check admitting direct calls with register arguments
  (`IselCheck.threadCheckBlC`): a call pauses at once, the other statements and terminators by
  the existing segment lemmas (`pure_segRT`, `IselMemMain.mem_segRT`, `term_segRT`);
* **`isel_refinesC`** (from a match, e.g. the caller resumed after a call) and
  **`isel_refines_entryC`** (from the function's entry): the VCode trace is realized as in
  `IselEntry.isel_refines_entryR`, or up to a call statement where the CLIF state is related by
  `Match` to a VCode configuration from which the rest of the trace runs;
* the pause is at the trace's end when the external semantics has no `call` step
  (`NoCall X`): the VCode configuration of a matched call statement is at a `call`
  instruction (`match_atCall`), which then has no step (`vtrun_atCall`); **`isel_pauseC`**:
  from the entry, with `NoCall X`, the trace is realized entirely, or up to where the CLIF
  thread stops, or entirely with the CLIF state at a call statement related by `Match` to the
  trace's last configuration.
-/

namespace Concurrency.IselCall

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine IselStep

/-- The CLIF state is at a `call` statement. -/
def AtCallS (s : Clif.State) : Prop :=
  ∃ stm rest fn args, s.frame.body = stm :: rest ∧ stm.inst = .call fn args

/-- **`SimResR` pausing at calls** (module doc). -/
def SimResC (env : Clif.Env) (p : Clif.Program) (vc : VCode) (sem : ISem CV ArmState)
    (ev : MInst → List CV → ArmState → List Ev)
    (Mt : Clif.State → VState CV ArmState → Prop) (s : Clif.State) (tr : List (List Ev))
    (cT : VConf CV ArmState) : Prop :=
  ∃ n trS t, n ≤ tr.length ∧ CRun env p (.run s) trS t ∧ Corr Maps trS (conv (tr.take n)) ∧
    ((((n = tr.length ∧ ∃ c', VStep vc sem cT c') ∨ Stop env p t) ∧
        ∀ v, t = .ret v → n = tr.length) ∨
      ∃ s' vs', t = .run s' ∧ AtCallS s' ∧ Mt s' vs' ∧ VTRun vc sem ev (.run vs') (tr.drop n) cT)

/-- `SegResR` pausing at calls (`SimResC` in place of `SimResR`). -/
def SegResC (env : Clif.Env) (p : Clif.Program) (vc : VCode) (sem : ISem CV ArmState)
    (ev : MInst → List CV → ArmState → List Ev)
    (Mt : Clif.State → VState CV ArmState → Prop) (s : Clif.State) (tr : List (List Ev))
    (cT : VConf CV ArmState) : Prop :=
  SimResC env p vc sem ev Mt s tr cT ∨
  ∃ n trS s' vs', n ≤ tr.length ∧ CRun env p (.run s) trS (.run s') ∧
    Corr Maps trS (conv (tr.take n)) ∧ Mt s' vs' ∧ VTRun vc sem ev (.run vs') (tr.drop n) cT ∧
    (0 < n ∨ s'.frame.body.length < s.frame.body.length)

section
variable {env : Clif.Env} {p : Clif.Program} {vc : VCode} {sem : ISem CV ArmState}
  {ev : MInst → List CV → ArmState → List Ev} {Mt : Clif.State → VState CV ArmState → Prop}

theorem SegResR.segResC {s : Clif.State} {tr : List (List Ev)} {cT : VConf CV ArmState}
    (h : SegResR env p vc sem ev Mt s tr cT) : SegResC env p vc sem ev Mt s tr cT := by
  rcases h with ⟨n, trS, t, hn, hrun, hcorr, hend, hret⟩ | h
  · exact .inl ⟨n, trS, t, hn, hrun, hcorr, .inl ⟨hend, hret⟩⟩
  · exact .inr h

/-- **Segment results pausing at calls compose** (`IselThread.simResR_of_seg`). -/
theorem simResC_of_seg
    (hseg : ∀ s c tr cT, Mt s c → VTRun vc sem ev (.run c) tr cT →
      SegResC env p vc sem ev Mt s tr cT)
    (s : Clif.State) (c : VState CV ArmState) (tr : List (List Ev)) (cT : VConf CV ArmState)
    (hm : Mt s c) (hr : VTRun vc sem ev (.run c) tr cT) : SimResC env p vc sem ev Mt s tr cT := by
  rcases hseg s c tr cT hm hr with h | ⟨n, trS, s', vs', hn, hrun, hcorr, hm', hr', hprog⟩
  · exact h
  · obtain ⟨n', trS', t', hn', hrun', hcorr', hend⟩ :=
      simResC_of_seg hseg s' vs' (tr.drop n) cT hm' hr'
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

/-- **Every segment from a match has its result, pausing at calls** (module doc). -/
theorem seg_resC (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X) (s : Clif.State) (c : VState CV ArmState) (tr : List (List Ev))
    (cT : VConf CV ArmState) (hm : Match f ctx R gn bl A MR slots s c)
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run c) tr cT) :
    SegResC env p vc (csem F fc X) (cEvs F fc) (Match f ctx R gn bl A MR slots) s tr cT := by
  obtain ⟨b, k, ρ, w⟩ := c
  cases hbody : s.frame.body with
  | nil => exact SegResR.segResC (term_segRT H hchk hm hbody hr)
  | cons stm rest =>
    by_cases hc : ∃ fn args, stm.inst = .call fn args
    · obtain ⟨fn, args, hc⟩ := hc
      exact .inl ⟨0, [], .run s, Nat.zero_le _, .nil, .nil,
        .inr ⟨s, _, rfl, ⟨stm, rest, fn, args, hbody, hc⟩, hm, by simpa using hr⟩⟩
    · have hnc : ∀ fn args, stm.inst ≠ .call fn args := fun fn args h => hc ⟨fn, args, h⟩
      cases hp : pureInst stm.inst
      · exact SegResR.segResC (IselMemMain.mem_segRT H hchk hMR hMRw hX hm hbody hp hnc hr)
      · exact SegResR.segResC (pure_segRT H hchk hm hbody hp hr)

/-- **Layer 2 from a match, pausing at calls** (module doc). -/
theorem isel_refinesC (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X) {s : Clif.State} {c : VState CV ArmState}
    (hm : Match f ctx R gn bl A MR slots s c) {tr : List (List Ev)} {cT : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run c) tr cT) :
    ∃ n trS t ψ, n ≤ tr.length ∧ CRun env p (.run s) trS t ∧
      Refines Maps (fun _ => False) (StepPair (conv (tr.take n))) trS (conv (tr.take n)) ψ ∧
      ((((n = tr.length ∧ ∃ c', VStep vc (csem F fc X) cT c') ∨ Stop env p t) ∧
          ∀ v, t = .ret v → n = tr.length) ∨
        ∃ s' vs', t = .run s' ∧ AtCallS s' ∧ Match f ctx R gn bl A MR slots s' vs' ∧
          VTRun vc (csem F fc X) (cEvs F fc) (.run vs') (tr.drop n) cT) := by
  obtain ⟨n, trS, t, hn, hrun, hcorr, hend⟩ :=
    simResC_of_seg (seg_resC H hchk hMR hMRw hX) s c tr cT hm hr
  obtain ⟨ψ, href⟩ := refines_of_corr hcorr hrun.length_le
  exact ⟨n, trS, t, ψ, hn, hrun, href, hend⟩

/-- **Layer 2 from the function's entry, pausing at calls** (module doc; as
`IselEntry.isel_refines_entryR`). -/
theorem isel_refines_entryC (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
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
        ∃ s' vs', t = .run s' ∧ AtCallS s' ∧ Match f ctx R gn bl A MR slots s' vs' ∧
          VTRun vc (csem F fc X) (cEvs F fc) (.run vs') (tr.drop n) cT) := by
  obtain ⟨vb, ps, ρ₁, ρ₂, w₂, hvb, hvb0, hstep, hseq, hm⟩ :=
    IselEntry.entry_matchNT H (driverSem_csem F fc X) hMem hMRs hB0 hcall hfunc hslots hbody
      hterm hregs hty hsig hmr hargs
  rw [IselEntry.entryLoads_nil hreg] at hseq hm
  simp only [seqRun, Option.some.injEq, SeqEnd.fall.injEq] at hseq
  obtain ⟨rfl, rfl⟩ := hseq
  have hsim : SimResC env p vc (csem F fc X) (cEvs F fc) (Match f ctx R gn bl A MR slots) cs tr
      cT := by
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
        simResC_of_seg (seg_resC H hchk hMR hMRw hX) cs _ tr' cT hm hr'
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

/-! ## The pause is at the trace's end -/

/-- **The VCode configuration of a matched call statement is at a direct `call`.** -/
theorem match_atCall (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBlC f bl = true) {s : Clif.State} {vs : VState CV ArmState}
    (hm : Match f ctx R gn bl A MR slots s vs) (hat : AtCallS s) :
    ∃ vb n us ds, vc.blocks[vs.b]? = some vb ∧
      vb.insts[vs.k]? = some (.call ⟨.sym n, us, ds⟩) := by
  obtain ⟨stm, rest, fn, args, hbody, hc⟩ := hat
  obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, hk, -, -⟩ := hm
  obtain ⟨hjlt, hstm, -⟩ := drop_cons_split (hbd ▸ hbody)
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨vb, hvb, hsllen, -, -, -, -, -, hcode, htne, -⟩ := H.shape.blk vs.b B L hB hL
  obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[j]? = some sl :=
    ⟨L.sl[j]'(by omega), List.getElem?_eq_getElem _⟩
  have hok := callOk_ofC hchk hB hstm hL hsl hc
  simp only [callOkB, hc, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff] at hok
  obtain ⟨hms, hex⟩ := hok
  have hseg := seg_eq (R := R) hB hL hstm hsl
  rw [hex, List.append_nil] at hseg
  split at hms
  · rename_i n us ds hem
    rw [hem] at hseg
    have h0 := (seg_at hcode htne hjlt).1 0 (by rw [hseg]; simp)
    have h1 : ∀ (h : 0 < (seg f R bl vs.b j).length), (seg f R bl vs.b j)[0] =
        .call ⟨.sym n, us.map fun (v, p) => (R v, p), ds.map fun (p, v) => (p, R v)⟩ := by
      rw [hseg]; intro _; rfl
    rw [Nat.add_zero, ← hk, h1] at h0
    exact ⟨vb, n, _, _, hvb, h0⟩
  · cases hms

/-- The external semantics has no `call` step. -/
def NoCall (X : ExtSem) : Prop := ∀ d u w, X.call d u w = none

/-- **No VCode step at a `call`** when the external semantics has none. -/
theorem vtrun_atCall {X : ExtSem} (hX0 : NoCall X) {ev : MInst → List CV → ArmState → List Ev}
    {vs : VState CV ArmState} {vb : VBlock} {info : CallInfo}
    (hvb : vc.blocks[vs.b]? = some vb) (hi : vb.insts[vs.k]? = some (.call info))
    {tr : List (List Ev)} {cT : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) ev (.run vs) tr cT) : tr = [] ∧ cT = .run vs := by
  cases hr with
  | nil => exact ⟨rfl, rfl⟩
  | cons hs _ =>
    obtain ⟨b, k, ρ, w⟩ := vs
    cases hs with
    | mk hvb1 hi1 _ _ _ hst =>
      simp only at hvb hi
      rw [hvb] at hvb1; cases hvb1
      rw [hi] at hi1; cases hi1
      cases hst with
      | step hvb2 hi2 _ hsem _ _ =>
        rw [hvb] at hvb2; cases hvb2
        rw [hi] at hi2; cases hi2
        simp only [csem] at hsem
        rw [hX0] at hsem
        simp at hsem

/-- **Layer 2 from the function's entry, the pause at the trace's end** (module doc). -/
theorem isel_pauseC (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X) (hX0 : NoCall X) (hMem : MemRefines F sb syms (csem F fc X))
    (hMRs : MRStable F MR) (hreg : ∀ off, ArgLoc.stack off ∉ locsOf f.sig)
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
        n = tr.length ∧ ∃ s' vs', t = .run s' ∧ AtCallS s' ∧ cT = .run vs' ∧
          Match f ctx R gn bl A MR slots s' vs') := by
  obtain ⟨n, trS, t, ψ, hn, hrun, href, hend⟩ := isel_refines_entryC H hchk hMR hMRw hX hMem hMRs
    hreg hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr hargs hr
  refine ⟨n, trS, t, ψ, hn, hrun, href, ?_⟩
  rcases hend with h | ⟨s', vs', ht, hat, hm', hr'⟩
  · exact .inl h
  · obtain ⟨vb, m, us, ds, hvb, hi⟩ := match_atCall H hchk hm' hat
    obtain ⟨hnil, rfl⟩ := vtrun_atCall hX0 hvb hi hr'
    refine .inr ⟨?_, s', vs', ht, hat, rfl, hm'⟩
    have := congrArg List.length hnil
    simp at this; omega

end

end Concurrency.IselCall
