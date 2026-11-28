import FV.Backend.Proof.LowerContract
import FV.Backend.Proof.IselContractPRDispatch

/-!
# The driver's `lower` calls under the call contracts with registers (#753, stage R2)

`instCalls_of_rules`, `tryCalls_of_rules`, `tryIndCalls_of_rules` (`LowerContract`) from the rule
families with registers (`CallRulesCorrectPR`, …) under the unpinned contracts with registers
(`CallsRefinePR`/`IndCallsRefinePR` at the trivial pin): `instCallsR_of_rules`,
`tryCallsR_of_rules`, `tryIndCallsR_of_rules` (through the pinned dispatchers of
`IselContractPRDispatch` at the trivial read guard and pin).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- **From M4's rule theorems to the driver's `lower` calls** (of function `f`, whose memory
relation satisfies `MemRelOk`, under the callee contract for `f`'s externs and the indirect-call
contract for `f`'s indirect-call signatures, whose calls' stack arguments fit the outgoing area
`outB`: `CallsStack`, `IndStack`). -/
theorem instCallsR_of_rules (hrules : LowerRulesCorrect Isle.Aarch64.program)
    (hex : ExcludedUnmatchable Isle.Aarch64.program)
    (hcalls : CallRulesCorrectPR Isle.Aarch64.program) (hind : IndRulesCorrectPR Isle.Aarch64.program)
    (hmem : MemRulesCorrectR Isle.Aarch64.program)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {sem : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {f : Clif.Function} (hR : Refines F sem)
    (hMR : MRStable F MR) (hcr : CallsRefinePR (fun _ _ _ _ => True) F env (f.externs.map (·.2)) MR sem)
    (hicr : IndCallsRefinePR (fun _ _ _ _ => True) env (indSigs f) MR sem)
    (hMem : MemRefines F sb syms sem) {outB : Nat} (hout : OutArgsOk F outB MR)
    (hstk : CallsStack f outB) (hIstk : IndStack (indSigs f) outB)
    (hMRo : MemRelOk F sb syms f MR) : InstCalls f sem MR env p := by
  intro ctx ii info inst st rss st' tr hctx hmem' hE hi hc hsig hemp hvb hrun
  obtain ⟨B, hB, stm, hstm, rfl⟩ := hmem'
  obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOkPR_runTerm (Rd := fun _ => True) (Pc := fun _ _ _ _ => True) hrules hex hcalls hind hmem
    (env := env) (cp := p) hR hMR hcr hicr (memRefinesR_of hMem) hctx hout (externsIn_self f) hE hMRo hi hc hsig hIstk
    (fun fn args e hc he => hstk B hB stm hstm fn args e hc he) hvb hrun
  cases hov
  rw [hemp, Array.empty_append] at hem
  rw [hem, List.toList_toArray]
  exact hok.toOk

/-- **From M4's `try_call` rule statements to the driver's `try_call` calls** (of `f`, under the
callee contract for `f`'s externs, the memory forms and the outgoing area `outB`). -/
theorem tryCallsR_of_rules (htr : TryRulesCorrectPR Isle.Aarch64.program)
    (hun : TryUnmatchable Isle.Aarch64.program) {F : BitVec 64 → Prop} {sem : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {f : Clif.Function} (hR : Refines F sem)
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat} (hMem : MemRefines F sb syms sem)
    {outB : Nat} (hout : OutArgsOk F outB MR) (hcr : CallsRefinePR (fun _ _ _ _ => True) F env (f.externs.map (·.2)) MR sem) :
    TryCalls f sem MR env p outB := by
  intro ctx ti fn args et data sig items targets info trs lo st1 out st' tr hctx hra hd he hph
    hinfo hregs hvb hrun
  have hctx' := ctxInv_tryRegs (ctxInv_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  obtain ⟨ms, hem, hok⟩ := tryOkPR_runTerm (Rd := fun _ => True) (Pc := fun _ _ _ _ => True) htr hun hR hMR (memRefinesR_of hMem) hout hcr hctx' (externsIn_self f) hra
    hd he hi
    hinfo hregs' hvb' (st := { st1 with emitted := #[] }) (Nat.le_refl _) hrun
  have : ms = st'.emitted.toList := by
    simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
  rw [← this]; exact hok.toOk

/-- **From M4's `try_call_indirect` rule statements to the driver's `try_call_indirect` calls**
(under the indirect-call contract for the signatures `sigs`, the memory forms and an outgoing
area `outB` that holds their stack arguments). -/
theorem tryIndCallsR_of_rules (htr : TryIndRulesCorrectPR Isle.Aarch64.program)
    (hun : TryIndUnmatchable Isle.Aarch64.program) {F : BitVec 64 → Prop} {sem : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {sigs : List Clif.Signature}
    (hR : Refines F sem) (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) {outB : Nat} (hout : OutArgsOk F outB MR)
    (hIstk : IndStack sigs outB) (hcr : IndCallsRefinePR (fun _ _ _ _ => True) env sigs MR sem) :
    TryIndCalls sem MR env p sigs := by
  intro f ctx ti callee args et data sig items targets info trs lo st1 out st' tr hctx hd he hsig
    hph hinfo hregs hvb hrun
  have hctx' := ctxInv_tryRegs (ctxInv_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  obtain ⟨ms, hem, hok⟩ := tryIndOkPR_runTerm (Rd := fun _ => True) (Pc := fun _ _ _ _ => True) htr hun hR hMR (memRefinesR_of hMem) hout hIstk hcr hctx' hd he hsig hi
    hinfo hregs' hvb' (st := { st1 with emitted := #[] }) (Nat.le_refl _) hrun
  have : ms = st'.emitted.toList := by
    simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
  rw [← this]; exact hok.toOk

end Backend.Proof.Driver
