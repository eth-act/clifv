import FV.E2E.Final
import FV.Backend.Proof.SretStable

/-!
# The `sret` return register (S7)

AAPCS64 (and Cranelift's `sigRets`) returns the struct-return pointer of a function with an
`sret` parameter and no returns in x0. `backend_correct_final` claims the CLIF return values
(none for such a function) and the memory; `backend_correct_final_abi` also claims the ABI
return values after them: `sretArg f args`, the `sret` argument, in x0.

* `IselSimAbi`, `iselSimAbi_of_driver`: the CLIF → VCode layer with all ABI returns held
  (`driver_correct_abi` with `sret_reach`: the `sretRet f` value at every `return` is the
  `sret` argument, for functions with `sretStableB f`);
* `ArmRefinesAbi`: `ArmRefines` with `vals ++ rets` in x0.. (`ArmRefinesAbi.armRefines`);
* `backend_correct_of_layers_ex_abi`, `backend_correct_ex_abi`, `backend_correct_of_rules_ex_abi`,
  `backend_correct_m4_ex_abi`, `backend_correct_final_ex_abi`, **`backend_correct_final_abi`**:
  the chain of `backend_correct_final[_ex]` with the premise `sretStableB f = true`;
* **`backend_correct_final_sret`**: for a function with an `sret` parameter `i` and no returns,
  a return leaves the `sret` argument `args[i]` in x0.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **CLIF → VCode with the ABI return values**: `IselSim`, and the returned use values hold the
CLIF return values followed by `sretArg f args` (`AllHold`: exactly the ABI returns). -/
def IselSimAbi (sem : Sem) (Γ : Rel) (env : Clif.Env) (p : Clif.Program) (f : Clif.Function)
    (vc : VCode) : Prop :=
  ∀ args cs w₀ (ρ₀ : Nat → CV), ClifEntry f args cs → Γ.holds f cs.frame.slots cs.mem w₀ →
    ArgsAtEntry Γ.F f.sig args w₀ → TrapsExplicit env p cs → ∀ fuel,
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w, VReturns vc sem ρ₀ w₀ us outs w ∧
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        AllHold (vals ++ sretArg f args) outs ∧ MemRel Γ.F Γ.syms cm w) ∧
    (∀ c, Clif.runLoop env p fuel cs = .trapped c → VTraps vc sem ρ₀ w₀ c)

/-- The run premises of the driver simulation from a CLIF entry state (`TrapsExplicit`). -/
theorem runPrem_of_entry {env : Clif.Env} {p : Clif.Program} {f : Clif.Function}
    {args : List Clif.Val} {cs : Clif.State} (hce : ClifEntry f args cs)
    (htr : TrapsExplicit env p cs) : RunPrem env p f cs := by
  have hf := hce.func
  exact ⟨htr.stmt, fun s c fn args et hr hs hb hT B hB => htr.tryCall s c fn args et hr hs hb hT B
      (hf ▸ hB),
    fun s c callee args et hr hs hb hT B hB =>
      htr.tryCallInd s c callee args et hr hs hb hT B (hf ▸ hB),
    fun s st rest sig callee args hr hb hi ⟨B, hB, hst⟩ =>
      htr.indirect s st rest sig callee args hr hb hi ⟨B, hf ▸ hB, hst⟩,
    fun s callee args et hr hb hT ⟨B, hB, e⟩ =>
      htr.tryIndirect s callee args et hr hb hT ⟨B, hf ▸ hB, e⟩⟩

/-- **CLIF → VCode with the ABI return values** from the driver simulation, for a function whose
`sret` value is bound once (`sretStableB`). -/
theorem iselSimAbi_of_driver {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {sem : Sem} {Γ : Rel} {env : Clif.Env} {p : Clif.Program}
    (H : DriverHyp f vc ctx st0 R gn bl A sem (fun sl cm w => Γ.holds f sl cm w) env p)
    (hds : DriverSem sem) {sb : Nat} (hMem : MemRefines Γ.F sb Γ.syms sem)
    (hS : sretStableB f = true) :
    IselSimAbi sem Γ env p f vc := by
  intro args cs w₀ ρ₀ hce hrel hargs htr fuel
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP : RunPrem env p f cs := runPrem_of_entry hce htr
  have hrun := driver_correct_abi H hds hMem (mrStable_holds Γ f) hB0 hce.callers hce.func rfl
    hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs hP
    (Q := (· = sretArg f args))
    (sret_reach H.ext H.tryExt H.noTail hP hS hB0 hce.callers hce.func hbody hterm hregs hty.symm)
    fuel
  refine ⟨fun vals cm h => ?_, fun c h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, sv, hret, h1, h2, hsv, h3, h4, h5⟩ := hrun
    subst hsv
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1 _)⟩
  · rw [h] at hrun
    exact hrun

/-- What the Arm run does for a CLIF outcome, with the ABI return values `rets` after the CLIF
ones (`stuck`/`outOfFuel`: no claim). -/
def ArmRefinesAbi (fb : FnBin) (base ra : BitVec 64) (astep : Arm.ArmState → Arm.ArmState)
    (s : Arm.ArmState) (rets : List Clif.Val) : Clif.Outcome → Prop
  | .returned vals cm => ∃ n, ArmRet ra s (runX astep n s) ∧
      (∀ (j : Nat) v, (vals ++ rets)[j]? = some v → XHolds v (xreg j (runX astep n s))) ∧
      MemAgree cm (runX astep n s)
  | .trapped c => ∃ n, TrapAt fb base c (runX astep n s)
  | .stuck _ | .outOfFuel => True

theorem ArmRefinesAbi.armRefines {fb : FnBin} {base ra : BitVec 64}
    {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState} {rets : List Clif.Val}
    {o : Clif.Outcome} (h : ArmRefinesAbi fb base ra astep s rets o) :
    ArmRefines fb base ra astep s o := by
  cases o with
  | returned vals cm =>
    obtain ⟨n, hret, hx, hm⟩ := h
    refine ⟨n, hret, fun j v hj => hx j v ?_, hm⟩
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hj).1]
    exact hj
  | trapped c => exact h
  | _ => trivial

/-- **Composition with the ABI return values** (`backend_correct_of_layers_ex` for
`IselSimAbi`). -/
theorem backend_correct_of_layers_ex_abi {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    {af : AFunc} {fb : FnBin} {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat}
    {astep : Arm.ArmState → Arm.ArmState} {env : Clif.Env}
    (hIsel : ∀ s, IselSimAbi (sem s) ⟨F s, syms, slotOff, out⟩ env p f vc)
    (hPrep : ∀ s, PrepareCorrect (sem s) vc vcp)
    (hReg : RegLevelCorrectEx sem F K astep vcp af fb)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsAtEntry (F s) f.sig args w₀)
    (hcs : ClifEntry f args cs) (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesAbi fb base ra astep s (sretArg f args) (Clif.runLoop env p fuel cs) := by
  obtain ⟨ρ₀, hR⟩ := hReg base ra s hent hres w₀ hbe
  have hI := hIsel s args cs w₀ ρ₀ hcs hrel hargs htr fuel
  cases hrun : Clif.runLoop env p fuel cs with
  | returned vals cm =>
    obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmem⟩ := hI.1 vals cm hrun
    obtain ⟨n, hret, hregs, hmemF⟩ := hR.1 us outs w ((hPrep s _ _).1 _ _ _ hv)
    refine ⟨n, hret, ?_, memAgree_of hmem hmemF⟩
    intro j v hj
    have hjv : j < (vals ++ sretArg f args).length := (List.getElem?_eq_some_iff.mp hj).1
    have hju : j < us.length := by have := hhold.1; omega
    obtain ⟨x, hx⟩ : ∃ x, outs[j]? = some x :=
      ⟨outs[j]'(by have := hhold.1; omega), List.getElem?_eq_getElem _⟩
    have hp : (us[j]'hju).2 = Reg.x j := by
      have := congrArg (fun l => l[j]?) hus
      simp only [List.getElem?_map, List.getElem?_range hju, List.getElem?_eq_getElem hju,
        Option.map_some] at this
      exact Option.some.inj this
    have hr := hregs j (us[j]'hju).1 (us[j]'hju).2 x (by simp [List.getElem?_eq_getElem hju]) hx
    rw [hp, regVal_x] at hr
    show VHolds v (ofX (xreg j (runX astep n s)))
    rw [hr]
    exact hhold.2 j v x hj hx
  | trapped c =>
    exact hR.2 c ((hPrep s _ _).2 c (hI.2 c hrun))
  | stuck _ => trivial
  | outOfFuel => trivial

/-- `backend_correct_ex` with the ABI return values (`sretStableB f`). -/
theorem backend_correct_ex_abi {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledA f k vc vcp rf af fa fb) (hS : sretStableB f = true)
    {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    (hrules : LowerRulesCorrect Isle.Aarch64.program)
    (hex : ExcludedUnmatchable Isle.Aarch64.program)
    (hcallRules : CallRulesCorrect Isle.Aarch64.program)
    (hindRules : IndRulesCorrect Isle.Aarch64.program)
    (hmemRules : MemRulesCorrect Isle.Aarch64.program)
    (hterms : ∀ s, TermCalls (sem s) (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w))
    (htries : ∀ s, TryCalls f (sem s) (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w)
      env p out)
    (htryInds : ∀ s, TryIndCalls (sem s) (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w)
      env p (indSigs f))
    (hM6 : RegLevelCorrectEx sem F K astep vcp af fb)
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    (hcalls : ∀ s, CallsRefine (F s) env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hicalls : ∀ s, IndCallsRefine env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    (houtB : vc.outgoing ≤ out)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesAbi fb base ra astep s (sretArg f args) (Clif.runLoop env p fuel cs) := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligations_of_check hc.lowerOk
  refine backend_correct_of_layers_ex_abi (fun s' => iselSimAbi_of_driver (ctx := ctx) (st0 := st0)
    (R := R) (gn := gn) (bl := bl) (A := A) ?_ (hds s') (hmem s') hS)
    (fun s' => prepareCorrect_of_check (hds s') hc.prepOk)
    hM6 hent hres hbe
    (argsAtEntry_body (lowerRFunc_frame hc.alloc) (entryRegs_of_check hc.lowerOk) hbe hargs hargF)
    hcs hrel htr fuel
  exact {
    shape := hshape
    cert := hcert
    dsem := (hds s').toDriverSemG
    insts := instCalls_of_rules hrules hex hcallRules hindRules hmemRules (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hcalls s') (hicalls s') (hmem s')
      (outArgsOk_holds ⟨F s', syms, slotOff, out⟩ f)
      (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
      (indStack_mono (indStack_of_check hc.lowerOk) houtB)
      (memRelOk_holds ⟨F s', syms, slotOff, out⟩ f)
    terms := hterms s'
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subset hsub
    subE := hsub.subsetE
    entryLocs := entryOk_of_check hc.lowerOk
    brIdx := hbr
    noTail := noTail_of_subset hsub
    tries := ⟨out, htries s', tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := htryInds s'
    tryIndSig := tryIndSig_of_subset hsub
    cfg := cfg_of_prepare hc.prepare }

/-- `backend_correct_of_rules_ex` with the ABI return values (`sretStableB f`). -/
theorem backend_correct_of_rules_ex_abi {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledA f k vc vcp rf af fa fb) (hS : sretStableB f = true)
    {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    (hrules : LowerRulesCorrect Isle.Aarch64.program)
    (hex : ExcludedUnmatchable Isle.Aarch64.program)
    (hcallRules : CallRulesCorrect Isle.Aarch64.program)
    (hindRules : IndRulesCorrect Isle.Aarch64.program)
    (hmemRules : MemRulesCorrect Isle.Aarch64.program)
    (htermRules : LowerTermRulesCorrect Isle.Aarch64.program)
    (htermUn : TermUnmatchable Isle.Aarch64.program)
    (hbranch : BranchRulesCorrect Isle.Aarch64.program)
    (hbranchEx : BranchExcludedUnmatchable Isle.Aarch64.program)
    (htryRules : TryRulesCorrect Isle.Aarch64.program)
    (htryUn : TryUnmatchable Isle.Aarch64.program)
    (htryIndRules : TryIndRulesCorrect Isle.Aarch64.program)
    (htryIndUn : TryIndUnmatchable Isle.Aarch64.program)
    (hM6 : RegLevelCorrectEx sem F K astep vcp af fb)
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    (hcalls : ∀ s, CallsRefine (F s) env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hicalls : ∀ s, IndCallsRefine env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    (houtB : vc.outgoing ≤ out)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesAbi fb base ra astep s (sretArg f args) (Clif.runLoop env p fuel cs) :=
  backend_correct_ex_abi hsub hc hS hrules hex hcallRules hindRules hmemRules
    (fun s' => termCalls_of_rules htermRules htermUn hbranch hbranchEx (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f))
    (fun s' => tryCalls_of_rules htryRules htryUn (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hmem s')
      (outArgsOk_holds ⟨F s', syms, slotOff, out⟩ f) (hcalls s'))
    (fun s' => tryIndCalls_of_rules htryIndRules htryIndUn (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hmem s')
      (outArgsOk_holds ⟨F s', syms, slotOff, out⟩ f)
      (indStack_mono (indStack_of_check hc.lowerOk) houtB) (hicalls s'))
    hM6 hRef hds hcalls hicalls hmem houtB hent hres hbe hargs hargF hcs hrel htr fuel

/-- `backend_correct_m4_ex` with the ABI return values (`sretStableB f`). -/
theorem backend_correct_m4_ex_abi {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledA f k vc vcp rf af fa fb) (hS : sretStableB f = true)
    {F : Arm.ArmState → BitVec 64 → Prop} {ctx : Arm.ArmState → FnCtx}
    {X : Arm.ArmState → ExtSem}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    (hM6 : RegLevelCorrectEx (fun s => csem (F s) (ctx s) (X s)) F K astep vcp af fb)
    (hRef : ∀ s, Refines (F s) (csem (F s) (ctx s) (X s)))
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s))
    (hXI : ∀ s, XCallsIndOk env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s))
    (hsym : ∀ s n b, syms n = some b → (X s).sym n 0 = BitVec.ofNat 64 b)
    (hmem : ∀ s, MemRefines (F s) slotOff syms (csem (F s) (ctx s) (X s)))
    (houtB : vc.outgoing ≤ out)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesAbi fb base ra astep s (sretArg f args) (Clif.runLoop env p fuel cs) :=
  backend_correct_of_rules_ex_abi hsub hc hS
    lowerRulesCorrect_program excludedUnmatchable callRulesCorrect indRulesCorrect
    memRulesCorrect_program lowerTermRulesCorrect termUnmatchable branchRulesCorrect
    branchExcludedUnmatchable tryRulesCorrect tryUnmatchable tryIndRulesCorrect tryIndUnmatchable
    hM6 hRef (fun s' => driverSem_csem (F s') (ctx s') (X s'))
    (fun s' => callsRefine_csem (hX s'))
    (fun s' => indCallsRefine_csem (hXI s') (hsym s') (fun _ _ _ h => h.1.symbols)) hmem houtB
    hent hres hbe hargs hargF hcs hrel htr fuel

/-- **The backend's end-to-end theorem with the ABI return values, for an `AllocChecked`
allocation**: `backend_correct_final_ex`, and a return also leaves the ABI return values after
the CLIF ones in x0..: `sretArg f args`, the `sret` argument of a function that returns its
struct pointer (`sigRets`). Extra premise: the `sret` value is bound once (`sretStableB`,
decided per function). -/
theorem backend_correct_final_ex_abi {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledA f k vc vcp rf af fa fb) (hS : sretStableB f = true)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesAbi fb base ra (ArmStepX X H fa) s (sretArg f args) (Clif.runLoop env p fuel cs) :=
  backend_correct_m4_ex_abi (ctx := fun _ => ⟨fa.k, af.slotBase⟩) (X := fun _ => X) hsub hc hS
    (regLevelCorrect_backend_ex hc.check hc.alloc hc.emit hc.layout hcov hC
      (fun h => hCT (hasTry_of_hasTryCallA hc h)) (fun h => hTls (hasTls_of_vcodeA hc h)))
    (refines_final K vcp rf af fa X) hX hXI (fun _ => hsym)
    (fun _ => memRefines_csem _ _ X hslot hsym) (outgoing_le_intBaseA hc)
    hent hres hbe hargs (stackArgsAvoid_frameWA hc hres hent hargs) hcs hrel htr fuel

/-- **The backend's end-to-end theorem with the ABI return values** (`docs/contracts/e2e.md`,
"`sret`"): `backend_correct_final` (its premises plus `sretStableB f`), and a return also leaves
the ABI return values after the CLIF ones in x0..: for a function with an `sret` parameter and
no returns, the `sret` argument in x0 (`sretArg`, `backend_correct_final_sret`). -/
theorem backend_correct_final_abi {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb) (hS : sretStableB f = true)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesAbi fb base ra (ArmStepX X H fa) s (sretArg f args) (Clif.runLoop env p fuel cs) :=
  backend_correct_final_ex_abi hsub hc.toA hS hcov hC hCT hTls hX hXI hsym hslot
    hent hres hbe hargs hcs hrel htr fuel

/-- `sretArg` of a function with an `sret` parameter `i` and no returns is `args[i]`. -/
theorem sretArg_of_sret {f : Clif.Function} {i : Nat}
    (hi : f.sig.params.findIdx? (·.purpose == .sret) = some i) (hr : f.sig.returns = [])
    (args : List Clif.Val) : sretArg f args = args[i]?.toList := by
  have hne : (sigRets f.sig != f.sig.returns) = true := by
    obtain ⟨q, hq⟩ : ∃ q, f.sig.params.find? (·.purpose == .sret) = some q := by
      cases h : f.sig.params.find? (·.purpose == .sret) with
      | some q => exact ⟨q, rfl⟩
      | none =>
        rw [List.find?_eq_none] at h
        obtain ⟨hlt, hq, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
        exact absurd hq (h _ (List.getElem_mem hlt))
    simp [sigRets, hq, hr]
  simp only [sretArg, hne, ite_true, hi]

/-- **The `sret` return register**: for a function with an `sret` parameter `i` and no returns
(AAPCS64, `sigRets`: the struct pointer is its one ABI result), under the premises of
`backend_correct_final_abi`, a CLIF return is matched by an Arm return (`ArmRet`) whose x0 holds
the `sret` argument `args[i]` (the pointer the caller passed in x8), with the memory the function
wrote (`MemAgree`). -/
theorem backend_correct_final_sret {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb) (hS : sretStableB f = true)
    {i : Nat} (hi : f.sig.params.findIdx? (·.purpose == .sret) = some i)
    (hnr : f.sig.returns = [])
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop env p fuel cs = .returned vals cm) {v : Clif.Val}
    (hv : args[i]? = some v) :
    ∃ n, ArmRet ra s (runX (ArmStepX X H fa) n s) ∧
      XHolds v (xreg 0 (runX (ArmStepX X H fa) n s)) ∧
      MemAgree cm (runX (ArmStepX X H fa) n s) := by
  obtain ⟨B0, hentB, hbody, hterm, -, -⟩ := hcs.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hentB
  have hvals : vals = [] := by
    have := runLoop_returned_tys_entry hsub.externCalls hsub.tryExterns (noTail_of_subset hsub)
      (runPrem_of_entry hcs htr) (sretStable_of hS) hB0 hcs.callers hcs.func hbody hterm hrun
    rw [hnr] at this
    simpa [Clif.AbiParam.tys] using this
  subst hvals
  have h := backend_correct_final_abi hsub hc hS hcov hC hCT hTls hX hXI hsym hslot
    hent hres hbe hargs hcs hrel htr fuel
  rw [hrun, sretArg_of_sret hi hnr, hv] at h
  obtain ⟨n, hret, hx, hm⟩ := h
  exact ⟨n, hret, hx 0 v (by simp), hm⟩

end E2E
