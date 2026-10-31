import FV.Concurrency.IselCall
import FV.E2E.Main
import FV.E2E.LinkWorld

/-!
# Layer 2 resuming after a call (#473, (2c) of the generic call theorem, layer 2)

A caller paused at a call statement (`IselCall.isel_pauseC`) resumes when its callee returns:
the CLIF thread pops the callee's frame (`ClifCStepTerm.cstep_ret_pop`), binding the call's
results to the callee's return values and taking the callee's final memory; the VCode `call`
instruction's outputs are the result registers at the return. Layer 2's `Match` after the call
is the driver's simulation of the call statement **in the extern view**: the callee seen as an
extern of the environment returning exactly those values and that memory (`envX`), the program
without functions (`pNil`), and an external semantics whose `call` returns exactly those outputs
and that world (`xcallX`). The call's code is the rules' (`instCalls_of_rules`), so the driver's
statement step (`IselStep.stmt_matchNT`) gives the `Match`, from the callee contract of the
extern view (`XCallsOk`: the outputs hold the return values, `PrefixHold`, and the memory
relation holds after the call) — which here is the hypothesis on the actual return.

* `pNil`, `inSubset_nil`; `pinSl MR sl0` (the memory relation at the slots `sl0` only, so that
  the callee contract need hold at the caller's slots only) with `mrStable_pin`,
  `outArgsOk_pin`, `memRelOk_pin`, `match_pin`;
* **`driverHypT_mk`**: `DriverHypT` for any environment, program, external semantics and memory
  relation, from the lowering's obligations and the checks (`driverHyp_of`'s construction);
  `driverHypT_of`;
* **`isel_resumeC`** (module doc): from `Match` at a call statement, the callee's return values,
  memory, outputs and world (`PrefixHold`, the memory relation at the caller's slots), the VCode
  `call` steps (under `xcallX`) to the configuration after it, which matches the CLIF state after
  the return.
-/

namespace Concurrency.IselResume

open Arm ArmThread ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread PrepThread
  IselThread E2E IselCall IselCheck

/-- A program without functions. -/
def pNil : Clif.Program := { funcs := [] }

/-- A checked function is in the subset of the program without functions. -/
theorem inSubset_nil {f : Clif.Function} (hv : verifiable f = true) : InSubset pNil f := by
  simp only [verifiable, abiSigs, indSigsOk, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, and_assoc] at hv
  obtain ⟨hE, hf, hext', hind⟩ := hv
  exact ⟨hE, fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl, ⟨hf, hext'⟩, hind⟩

/-! ## The memory relation at fixed slots -/

/-- The memory relation at the slots `sl0` only. -/
def pinSl (MR : MemRelT) (sl0 : List (Clif.SlotId × Nat)) : MemRelT :=
  fun sl cm w => MR sl cm w ∧ sl = sl0

theorem mrStable_pin {F : BitVec 64 → Prop} {MR : MemRelT} (h : MRStable F MR)
    (sl0 : List (Clif.SlotId × Nat)) : MRStable F (pinSl MR sl0) :=
  fun sl cm w w' hsw ⟨hm, he⟩ => ⟨h sl cm w w' hsw hm, he⟩

theorem outArgsOk_pin {F : BitVec 64 → Prop} {out : Nat} {MR : MemRelT} (h : OutArgsOk F out MR)
    (sl0 : List (Clif.SlotId × Nat)) : OutArgsOk F out (pinSl MR sl0) := by
  intro sl cm w ⟨hm, he⟩
  obtain ⟨h1, h2, h3⟩ := h sl cm w hm
  exact ⟨h1, h2, fun k n y hk => ⟨h3 k n y hk, he⟩⟩

theorem memRelOk_pin {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {f : Clif.Function} {MR : MemRelT} (h : MemRelOk F sb syms f MR)
    (sl0 : List (Clif.SlotId × Nat)) : MemRelOk F sb syms f (pinSl MR sl0) where
  bytes := fun sl cm w a b hm => h.bytes sl cm w a b hm.1
  valid := fun sl cm w a n hm => h.valid sl cm w a n hm.1
  symbols := fun sl cm w hm => h.symbols sl cm w hm.1
  slots := fun sl cm w id b hm => h.slots sl cm w id b hm.1
  store := fun sl cm w a n y hm hv => ⟨h.store sl cm w a n y hm.1 hv, hm.2⟩

theorem match_pin {f : Clif.Function} {ctx : Ctx} {R : Reg → Reg} {gn : Nat → Nat}
    {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {MR : MemRelT}
    {slots : List (Clif.SlotId × Nat)} {s : Clif.State} {vs : VState CV ArmState} :
    Match f ctx R gn bl A (pinSl MR slots) slots s vs ↔ Match f ctx R gn bl A MR slots s vs := by
  constructor
  · rintro ⟨h1, h2, h3, ⟨h4, -⟩, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, ⟨h4, rfl⟩, h5⟩

/-! ## The driver hypothesis for any environment -/

/-- **`DriverHypT` for any environment, program, external semantics and memory relation**
(module doc). -/
theorem driverHypT_mk {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {Γ : E2E.Rel} {fctx : FnCtx} {X : ExtSem} {MR : MemRelT} {env : Clif.Env} {p : Clif.Program}
    (hshape : LowerShape f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term)
    (hlow : lowerCheck f vc = true) (hind : indSigs f = []) (hv : verifiable f = true)
    (hnt : f.blocks.all (fun B => !B.term.isTry) = true)
    (hcfg : ∃ ss ps, vc.cfg = .ok (ss, ps)) (hout0 : vc.outgoing = 0)
    (hslot : fctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hMRs : MRStable Γ.F MR) (hOut : OutArgsOk Γ.F Γ.out MR)
    (hMRo : MemRelOk Γ.F Γ.slotOff Γ.syms f MR)
    (hX : XCallsOk env (f.externs.map (·.2)) MR X) :
    DriverHypT f vc ctx st0 R gn bl A (csem Γ.F fctx X) MR env p := by
  have hsub := inSubset_nil hv
  have hXI : XCallsIndOk env (indSigs f) MR X := by
    rw [hind]; intro s h; cases h
  have hRef : Refines Γ.F (csem Γ.F fctx X) := refines_csem Γ.F fctx X
  have hmem : MemRefines Γ.F Γ.slotOff Γ.syms (csem Γ.F fctx X) :=
    memRefines_csem Γ.F fctx X hslot hsym
  have hcalls := callsRefine_csem (F := Γ.F) (ctx := fctx) hX
  have hicalls := indCallsRefine_csem (F := Γ.F) (ctx := fctx) hXI hsym hMRo.symbols
  have houtB : vc.outgoing ≤ Γ.out := by rw [hout0]; exact Nat.zero_le _
  exact {
    shape := hshape
    cert := hcert
    dsem := (driverSem_csem Γ.F fctx X).toDriverSemG
    insts := instCalls_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrect
      indRulesCorrect memRulesCorrect_program hRef hMRs hcalls hicalls hmem hOut
      (callsStack_mono (callsStack_of_check hlow) houtB) hMRo
    terms := termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
      branchExcludedUnmatchable hRef hMRs
    indSig := indSig_of_subset hsub
    subE := hsub.subsetE
    entryLocs := entryOk_of_check hlow
    brIdx := hbr
    noTail := noTail_of_subset hsub
    tries := ⟨_, tryCalls_of_rules tryRulesCorrect tryUnmatchable hRef hMRs hmem hOut hcalls,
      tryStack_mono (tryStack_of_check hlow) houtB⟩
    tryExt := fun B hB fn args et ht => by
      have := List.all_eq_true.mp hnt B hB
      rw [ht] at this; cases this
    tryInd := tryIndCalls_of_rules tryIndRulesCorrect tryIndUnmatchable hRef hMRs hicalls
    tryIndSig := tryIndSig_of_subset hsub
    cfg := hcfg }

/-- **`DriverHypT` and the check admitting calls for a checked function** whose externs are not
the environment's (`RealizeCompiled.Witness.driverHyp_of` admitting calls). -/
theorem driverHypT_of {f : Clif.Function} {vc : VCode} {Γ : E2E.Rel} {fctx : FnCtx} {X : ExtSem}
    {c : BitVec 64} {env : Clif.Env} {p : Clif.Program}
    (hlow : lowerCheck f vc = true) (hthr : IselCheck.threadCheckC f = true)
    (hext : ∀ e ∈ f.externs, env.extern e.2.name = none) (hind : indSigs f = [])
    (hv : verifiable f = true) (hnt : f.blocks.all (fun B => !B.term.isTry) = true)
    (hcfg : ∃ ss ps, vc.cfg = .ok (ss, ps)) (hout0 : vc.outgoing = 0)
    (hslot : fctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    ∃ ctx st0 R gn bl A, DriverHypT f vc ctx st0 R gn bl A (csem Γ.F fctx X) (RelW Γ f c) env p ∧
      IselCheck.threadCheckBlC f bl = true := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hbl⟩ :=
    IselCheck.obligations_of_threadCheckC hlow hthr
  refine ⟨ctx, st0, R, gn, bl, A, driverHypT_mk hshape hcert hbr hlow hind hv hnt hcfg hout0
    hslot hsym (mrStable_relW Γ f c) (outArgsOk_relW Γ f c) (memRelOk_relW Γ f c) ?_, hbl⟩
  intro ext hmem g _ _ _ _ _ _ _ _ _ hg
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
  rw [hext e he] at hg; cases hg

/-! ## The resume -/

open Classical in
/-- The callee as an extern: returning `rvals` and `cm'` on the arguments `vals` and the memory
`cm`. -/
noncomputable def externX (name : String) (vals : List Clif.Val) (cm : Clif.Mem) (rvals : List Clif.Val)
    (cm' : Clif.Mem) (n : String) : Option (List Clif.Val → Clif.Mem → Clif.Outcome) :=
  if n = name then
    some (fun vs m => if vs = vals ∧ m = cm then .returned rvals cm' else .stuck "")
  else none

/-- The callee seen as an extern returning `rvals` and `cm'` on the arguments `vals` and the memory
`cm` (the other externs absent). -/
noncomputable def envX (env : Clif.Env) (name : String) (vals : List Clif.Val) (cm : Clif.Mem)
    (rvals : List Clif.Val) (cm' : Clif.Mem) : Clif.Env :=
  { env with extern := externX name vals cm rvals cm' }

/-- The external semantics whose `call` returns `outs` and the world `y`. -/
def xcallX (X : ExtSem) (outs : List CV) (y : ArmState) : ExtSem :=
  { X with call := fun _ _ _ => some (outs, y) }

/-- **Layer 2 resuming after a call** (module doc). -/
theorem isel_resumeC {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {Γ : E2E.Rel} {fctx : FnCtx} {X : ExtSem} {c : BitVec 64}
    {slots : List (Clif.SlotId × Nat)}
    (hshape : LowerShape f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term) (hchk : threadCheckBlC f bl = true)
    (hlow : lowerCheck f vc = true) (hind : indSigs f = []) (hv : verifiable f = true)
    (hnt : f.blocks.all (fun B => !B.term.isTry) = true)
    (hcfg : ∃ ss ps, vc.cfg = .ok (ss, ps)) (hout0 : vc.outgoing = 0)
    (hslot : fctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : ArmState}
    (hm : Match f ctx R gn bl A (RelW Γ f c) slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    {fn : Clif.FnRef} {args : List Clif.ValueId} (hc : stm.inst = .call fn args)
    {ext : Clif.ExtFunc} (hext : s.frame.func.extern? fn = some ext)
    (huniq : ∀ e ∈ f.externs, e.2.name = ext.name → e.2 = ext)
    {vals : List Clif.Val} (hvals : s.frame.getMany args = .ok vals)
    (htys : vals.map (·.ty) = Clif.AbiParam.tys ext.sig.params)
    {rvals : List Clif.Val} {cm' : Clif.Mem}
    (hrty : rvals.map (·.ty) = Clif.AbiParam.tys ext.sig.returns)
    {regs' : Clif.Regs} (hregs : s.frame.regs.setMany stm.results rvals = some regs')
    {outs : List CV} {y : ArmState} (hlen : outs.length = ext.sig.returns.length)
    (hpre : PrefixHold rvals outs) (hmr : RelW Γ f c slots cm' y) :
    ∃ ρ', VStep vc (csem Γ.F fctx (xcallX X outs y)) (.run ⟨b, k, ρ, w⟩) (.run ⟨b, k + 1, ρ', y⟩) ∧
      Match f ctx R gn bl A (RelW Γ f c) slots
        { s with frame := { s.frame with regs := regs', body := rest }, mem := cm' }
        ⟨b, k + 1, ρ', y⟩ := by
  -- the extern view
  let env' := envX Clif.Env.empty ext.name vals s.mem rvals cm'
  have hX : XCallsOk env' (f.externs.map (·.2)) (pinSl (RelW Γ f c) slots) (xcallX X outs y) := by
    intro e0 hmem g sl cm w0 d uses args0 vals0 rvals0 cm0 hg _ _ hmr0 hret _
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
    simp only [env', envX, externX] at hg
    split at hg
    · rename_i hn
      have he' := huniq e he hn
      rw [he']
      cases hg
      simp only at hret
      split at hret
      · rename_i hvc
        obtain ⟨rfl, rfl⟩ := hvc
        cases hret
        obtain ⟨-, rfl⟩ := hmr0
        exact ⟨outs, y, rfl, hlen, hpre, hmr, rfl⟩
      · cases hret
    · cases hg
  have hsym' : ∀ n b, Γ.syms n = some b → (xcallX X outs y).sym n 0 = BitVec.ofNat 64 b := hsym
  have H := driverHypT_mk (p := pNil) hshape hcert hbr hlow hind hv hnt hcfg hout0 hslot hsym'
    (mrStable_pin (mrStable_relW Γ f c) slots) (outArgsOk_pin (outArgsOk_relW Γ f c) slots)
    (memRelOk_pin (memRelOk_relW Γ f c) slots) hX
  -- the CLIF step of the call in the extern view
  have hs : Clif.step env' pNil s =
      .next { s with frame := { s.frame with regs := regs', body := rest }, mem := cm' } := by
    rw [step_stmt env' pNil s stm rest hbody (fun _ _ _ _ _ => rfl)
      (fun sig callee args h => by rw [hc] at h; cases h), hc]
    simp only [instOutcome, hext, hvals, Clif.Res.ofOption, Clif.checkTys, htys, beq_self_eq_true,
      Clif.Res.check, env', envX, externX, pNil, Clif.Program.func?, List.find?_nil, ite_true, hrty,
      and_self, Clif.Res.bind, bind, pure]
    simp [Clif.StepResult.ofRes, Clif.continueWith, hregs]
  obtain ⟨B, j, ρ', w', hB, hstm, hbd, hk, hstar, hsr, hM⟩ :=
    IselStep.stmt_matchNT H (match_pin.mpr hm) hbody
      (fun sig callee args h => by rw [hc] at h; cases h) (fun _ _ _ _ _ => rfl) hs
  -- the call's code is the one `call`
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨-, -, hsllen, -⟩ := hshape.blk b B L hB hL
  have hjlt : j < B.body.length := (List.getElem?_eq_some_iff.mp hstm).1
  obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[j]? = some sl :=
    ⟨L.sl[j]'(by omega), List.getElem?_eq_getElem _⟩
  have hok := callOk_ofC hchk hB hstm hL hsl hc
  simp only [callOkB, hc, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff] at hok
  obtain ⟨hms, hex⟩ := hok
  have hseg := seg_eq (R := R) hB hL hstm hsl
  rw [hex, List.append_nil] at hseg
  split at hms
  · rename_i nm us ds hem
    rw [hem] at hseg
    rw [hseg] at hstar hsr hM
    simp only [List.map_cons, List.map_nil, List.length_singleton] at hstar hsr hM
    -- the world after the call
    have hw' : w' = y := by
      simp only [seqRun, MInst.mapRegs, csem, xcallX, Option.map_some] at hsr
      split at hsr
      · cases hsr
      · split at hsr
        · simp at hsr
          obtain ⟨-, -, rfl⟩ := hsr
          rfl
        · cases hsr
    subst hw'
    cases hstar with
    | step _ hv h0 =>
      cases h0
      exact ⟨ρ', hv, match_pin.mp hM⟩
  · cases hms

end Concurrency.IselResume
