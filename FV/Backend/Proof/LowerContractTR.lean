import FV.Backend.Proof.LowerContractT
import FV.Backend.Proof.LowerContractTPR

/-!
# The typed driver's `lower` calls under the call contracts with registers (#753, stage R2)

`instCallsT_of_rules`, `tryCallsT_of_rules`, `tryIndCallsT_of_rules` (`LowerContractT`) from the
typed rule families with registers (`CallRulesCorrectTPR`, …) under the unpinned contracts with
registers: `instCallsTR_of_rules`, `tryCallsTR_of_rules`, `tryIndCallsTR_of_rules` (through the
pinned typed dispatchers of `LowerContractTPR` at the trivial read guard and pin).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- **From the typed rule families to the driver's `lower` calls** in a typed, store-typed
context `ctx` of `f` (whose memory relation satisfies `MemRelOk`, under the callee contract for
`f`'s externs, the indirect-call contract for its indirect-call signatures and the float accesses'
`MemRefinesFP`). -/
theorem instCallsTR_of_rules (hrules : LowerRulesCorrectTI Isle.Aarch64.program)
    (hT : LowerRulesCorrectT Isle.Aarch64.program) (hFT : LowerRulesCorrectFT Isle.Aarch64.program)
    (hnE : NonEUnmatchableT Isle.Aarch64.program) (hcalls : CallRulesCorrectTPR Isle.Aarch64.program)
    (hind : IndRulesCorrectTPR Isle.Aarch64.program) (hmem : MemRulesCorrectRTI Isle.Aarch64.program)
    (hmemF : MemRulesCorrectRT Isle.Aarch64.program)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {sem : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {f : Clif.Function} {ctx : Ctx}
    (hR : Refines F sem) (hMR : MRStable F MR) (hcr : CallsRefinePR (fun _ _ _ _ => True) F env (f.externs.map (·.2)) MR sem)
    (hicr : IndCallsRefinePR (fun _ _ _ _ => True) env (indSigs f) MR sem)
    (hMem : MemRefines F sb syms sem) (hFP : MemRefinesFP (fun _ => True) F sb sem) {outB : Nat}
    (hout : OutArgsOk F outB MR) (hstk : CallsStack f outB) (hIstk : IndStack (indSigs f) outB)
    (hMRo : MemRelOk F sb syms f MR) (hctx : CtxT f ctx) (hsc : InstScopeT ctx)
    (hst : StoresTyped ctx) :
    InstCallsT f ctx sem MR env p := by
  intro ii info inst st rss st' tr hmem' hi hc hsig hemp hvb hrun
  obtain ⟨B, hB, stm, hstm, rfl⟩ := hmem'
  obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOkPR_runTermT (Rd := fun _ => True) (Pc := fun _ _ _ _ => True) hrules hT hFT hnE hcalls hind hmem hmemF
    (env := env) (cp := p) hR hMR hcr hicr (memRefinesR_of hMem) hFP hctx hsc hout (externsIn_self f) hMRo hi hc hsig
    hIstk
    (hst ii info _ hi hc)
    (fun fn args e hc he => hstk B hB stm hstm fn args e hc he) hvb hrun
  cases hov
  rw [hemp, Array.empty_append] at hem
  rw [hem, List.toList_toArray]
  exact hok.toOk

/-- **From the typed `try_call` rule families to the driver's `try_call` calls** in a typed
context. -/
theorem tryCallsTR_of_rules (htr : TryRulesCorrectTPR Isle.Aarch64.program)
    (hun : TryUnmatchableT Isle.Aarch64.program) {F : BitVec 64 → Prop} {sem : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {f : Clif.Function} {ctx : Ctx}
    (hR : Refines F sem)
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat} (hMem : MemRefines F sb syms sem)
    {outB : Nat} (hout : OutArgsOk F outB MR) (hcr : CallsRefinePR (fun _ _ _ _ => True) F env (f.externs.map (·.2)) MR sem)
    (hctx : CtxT f ctx) : TryCallsT f ctx sem MR env p outB := by
  intro ti fn args et data sig items targets info trs lo st1 out st' tr hra hd hip he hph
    hinfo hregs hvb hrun
  have hctx' := ctxT_tryRegs (ctxT_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  obtain ⟨ms, hem, hok⟩ := tryOkPR_runTermT (Rd := fun _ => True) (Pc := fun _ _ _ _ => True) htr hun hR hMR (memRefinesR_of hMem) hout hcr hctx' (externsIn_self f) hra
    hd hip he hi hinfo hregs' hvb' (st := { st1 with emitted := #[] }) (Nat.le_refl _) hrun
  have : ms = st'.emitted.toList := by
    simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
  rw [← this]; exact hok.toOk

/-- **From the typed `try_call_indirect` rule families to the driver's calls** in a typed
context (under the memory forms and an outgoing area `outB` that holds the stack arguments of
`sigs`). -/
theorem tryIndCallsTR_of_rules (htr : TryIndRulesCorrectTPR Isle.Aarch64.program)
    (hun : TryIndUnmatchableT Isle.Aarch64.program) {F : BitVec 64 → Prop} {sem : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {sigs : List Clif.Signature}
    {f : Clif.Function} {ctx : Ctx}
    (hR : Refines F sem) (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) {outB : Nat} (hout : OutArgsOk F outB MR)
    (hIstk : IndStack sigs outB) (hcr : IndCallsRefinePR (fun _ _ _ _ => True) env sigs MR sem)
    (hctx : CtxT f ctx) : TryIndCallsT f ctx sem MR env p sigs := by
  intro ti callee args et data sig items targets info trs lo st1 out st' tr hd hip he hsig
    hph hinfo hregs hvb hrun
  have hctx' := ctxT_tryRegs (ctxT_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  obtain ⟨ms, hem, hok⟩ := tryIndOkPR_runTermT (Rd := fun _ => True) (Pc := fun _ _ _ _ => True) htr hun hR hMR (memRefinesR_of hMem) hout hIstk hcr hctx' hd hip he
    hsig hi
    hinfo hregs' hvb' (st := { st1 with emitted := #[] }) (Nat.le_refl _) hrun
  have : ms = st'.emitted.toList := by
    simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
  rw [← this]; exact hok.toOk

end Backend.Proof.Driver
