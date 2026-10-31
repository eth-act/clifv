import FV.E2E.RegLevelMemTrap
import FV.E2E.LinkWorld
import FV.E2E.DeadCleanupFinal
import FV.E2E.DeadCleanupGot

/-!
# The per-function world theorem with memory traps (A3, #412, slice F4)

`docs/plans/memfault.md`. `backend_correct_worldX_cleanup` (the per-function theorem the
linked-program induction applies) for a trapping run under the run premise `TrapsExplicitM` (a
statement traps only if it traps explicitly or is a trapping atomic, `Clif.memTrapInst`) and the
memory map premise `MapFaults mp` (every memory trap's access has a byte `mp` does not map): the
activation's machine run reaches a trap site of the function with the CLIF trap code, at a `udf`
line or at the trapping atomic's `ldaxr` whose access has an unmapped byte (`TrapAtM`), every
earlier state `GoodX`.

The machine is the existing one (`ArmStepX`, memory total). The theorem says that **if** the run
reaches the trapping atomic, its `ldaxr` faults under `mp` (`TrapAtF`, `trapAtF_of_trapAtM`); it
does not say that no earlier access faults under `mp` (slice F8).

* `iselSim_relW_cleanup_memtrap`: CLIF → VCode (`driver_memtrap` under the dead-cleanup chain's
  value semantics): an explicit VCode trap or a VCode memory trap (`VMemTraps`) whose address
  ranges have an unmapped byte;
* `vMemTraps_gotV_value`: `vTraps_gotV_value` for memory traps;
* `regLevel_memtrap_value`: `regLevel_memtrap_world_value` from `checkAlloc`;
* **`backend_correct_worldX_cleanup_memtrap`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **CLIF → VCode with memory traps** (`iselSim_relW_cleanup`'s trap half under
`TrapsExplicitM`): a trapping CLIF run is an explicit VCode trap, or reaches an LL/SC loop with
the trap code whose address range has a byte `mp` does not map (`MapFaults`). -/
theorem iselSim_relW_cleanup_memtrap {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {args : List Clif.Val} {cs : Clif.State} {w₀ : Arm.ArmState} (ρ₀ : Nat → CV)
    (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicitM env p cs)
    {mp : ArmFault.MemMap} (hmf : MapFaults mp env p cs) (fuel : Nat) :
    ∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      VTraps vc (valueSem F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c' ∨
      VMemTraps vc (valueSem F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c'
        (addrPred fun a n => ∃ k < n, mp (BitVec.ofNat 64 (a + k)) = .none) := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligations_of_check hc.lowerOk
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hRef : Refines F (valueSem F ⟨fa.k, af.slotBase⟩ X) := refines_valueSem _ _ X
  have hmem : MemRefines F slotOff syms (valueSem F ⟨fa.k, af.slotBase⟩ X) :=
    memRefines_valueSem _ _ X hslot hsym
  have hcalls := callsRefine_valueSem (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hX
  have hicalls := indCallsRefine_valueSem (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hXI hsym
    (fun _ _ _ h => h.1.1.symbols)
  have houtB := outgoing_le_intBaseCleanupA hc.toA
  have H : DriverHyp f vc ctx st0 R gn bl A (valueSem F ⟨fa.k, af.slotBase⟩ X) (RelW Γ f c) env p := {
    shape := hshape
    cert := hcert
    dsem := (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X).toDriverSemG
    insts := instCalls_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrect
      indRulesCorrect memRulesCorrect_program hRef (mrStable_relW Γ f c) hcalls hicalls hmem
      (outArgsOk_relW Γ f c) (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
      (indStack_mono (indStack_of_check hc.lowerOk) houtB) (memRelOk_relW Γ f c)
    terms := termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
      branchExcludedUnmatchable hRef (mrStable_relW Γ f c)
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subset hsub
    subE := hsub.subsetE
    entryLocs := entryOk_of_check hc.lowerOk
    brIdx := hbr
    noTail := noTail_of_subset hsub
    tries := ⟨_, tryCalls_of_rules tryRulesCorrect tryUnmatchable hRef (mrStable_relW Γ f c) hmem
      (outArgsOk_relW Γ f c) hcalls, tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCalls_of_rules tryIndRulesCorrect tryIndUnmatchable hRef (mrStable_relW Γ f c)
      hmem (outArgsOk_relW Γ f c) (indStack_mono (indStack_of_check hc.lowerOk) houtB) hicalls
    tryIndSig := tryIndSig_of_subset hsub
    cfg := by
      obtain ⟨ss, ps, he⟩ := cfg_of_prepare hc.prepare
      exact ⟨ss, ps, (prune_cfg vc).symm.trans he⟩ }
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP : RunPremM env p f cs := by
    have hf := hce.func
    exact ⟨htr.stmt, fun s c fn args et hr hs hb hT B hB => htr.tryCall s c fn args et hr hs hb hT B
        (hf ▸ hB),
      fun s c callee args et hr hs hb hT B hB =>
        htr.tryCallInd s c callee args et hr hs hb hT B (hf ▸ hB),
      fun s st rest sig callee args hr hb hi ⟨B, hB, hst⟩ =>
        htr.indirect s st rest sig callee args hr hb hi ⟨B, hf ▸ hB, hst⟩,
      fun s callee args et hr hb hT ⟨B, hB, e⟩ =>
        htr.tryIndirect s callee args et hr hb hT ⟨B, hf ▸ hB, e⟩⟩
  intro c' hrun
  exact driver_memtrap H (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X) hmem (mrStable_relW Γ f c)
    hB0 hce.callers hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs hP
    (Q := fun a n => ∃ k < n, mp (BitVec.ofNat 64 (a + k)) = .none) hmf fuel c' hrun

/-- **A VCode memory trap under the value semantics is one under `valueSemV (GotV vc)`** (the run
to the loop is one of `valueSemV`, `gotInv_star_value`; the loop itself is no step). -/
theorem vMemTraps_gotV_value {vc : VCode} {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} {c : Clif.TrapCode} {A : BitVec 64 → Nat → Prop}
    (h : VMemTraps vc (valueSem F ctx X) ρ₀ w₀ c A) :
    VMemTraps vc (valueSemV (GotV vc) F ctx X) ρ₀ w₀ c A := by
  obtain ⟨b, k, ρ, w, vb, i, ops, u, us, n, hs, h1⟩ := h
  obtain ⟨hs', -⟩ := gotInv_star_value (gotInv_entry vc X ρ₀ w₀) hs
  exact ⟨b, k, ρ, w, vb, i, ops, u, us, n, hs', h1⟩

/-- **The register level of the explicit and the memory traps** (`regLevel_memtrap_world_value`)
from the allocation check. -/
theorem regLevel_memtrap_value {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : CalleeOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → CalleeTryOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K X H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀)
    (ρ₀ : Nat → CV) (mp : ArmFault.MemMap) :
    (∀ c, VTraps vcp (valueSemV gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c →
      ∃ n, TrapAtM mp fa fb base c (E2E.runX (ArmStepX X H fa) n s) ∧
        ∀ i < n, actGoodX vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) ∧
    (∀ c (A : BitVec 64 → Nat → Prop), (∀ x n, A x n → Unmapped mp x n) →
      VMemTraps vcp (valueSemV gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c A →
      ∃ n, TrapAtM mp fa fb base c (E2E.runX (ArmStepX X H fa) n s) ∧
        ∀ i < n, actGoodX vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) := by
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨_, h⟩ := regLevel_memtrap_world_value hat (entryOk_of_le hle) halloc hemit hlayout hcov
    hent hres hG hC hCT hTls hbe (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState) mp
  exact h

/-- **The per-function world theorem with memory traps** (`backend_correct_worldX_cleanup`'s trap
half under `TrapsExplicitM` and `MapFaults mp`): every activation (`ActEntry`) of a trapping run
reaches a trap site of `f` with the CLIF code, at a `udf` line or at the trapping atomic's `ldaxr`
whose access has a byte `mp` does not map (`TrapAtM`), every earlier state `GoodX`. -/
theorem backend_correct_worldX_cleanup_memtrap {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicitM env p cs) {mp : ArmFault.MemMap} (hmf : MapFaults mp env p cs)
    (fuel : Nat) :
    ∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAtM mp fa fb base c' (runX (ArmStepX X H fa) n s) ∧
          ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp) (runX (ArmStepX X H fa) i s) := by
  intro c' hrun H G base ra s he
  have hM6 := regLevel_memtrap_value hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
    (K := K) (G := G) (gv := GotV vcp) hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
    (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body)
    (fun _ => 0) mp
  rw [he.hF] at hM6
  have hpr : ∀ i us w outs w' ctl, pureForm i = true →
      valueSem F ⟨fa.k, af.slotBase⟩ X i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next :=
    fun _ _ _ _ _ _ hp he => valueSem_pure hp he
  rcases iselSim_relW_cleanup_memtrap hsub hc hX hXI hsym hslot (fun _ => 0) hcs hrel hargs htr
    hmf fuel c' hrun with ht | ht
  · have hP : PrepareCorrect (valueSem F ⟨fa.k, af.slotBase⟩ X) vc vcp := by
      intro a w
      obtain ⟨hr, ht⟩ := prune_correct (vc := vc) hpr (valueSem_cmpOverwrite _ _ _) a w
      obtain ⟨pr, pt⟩ := prepareCorrect_of_check (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X)
        hc.prepOk a w
      exact ⟨fun _ _ _ he => pr _ _ _ (hr _ _ _ he), fun _ he => pt _ (ht _ he)⟩
    exact hM6.1 c' (vTraps_gotV_value ((hP (fun _ => 0) w₀).2 c' ht))
  · exact hM6.2 c' _ (fun _ _ h => unmapped_of_addrPred h)
      (vMemTraps_gotV_value (memTraps_prep (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X) hc.prepOk
        (memTraps_prune hpr (valueSem_cmpOverwrite _ _ _) ht)))

end E2E
