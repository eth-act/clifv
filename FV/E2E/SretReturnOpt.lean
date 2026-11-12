import FV.E2E.Opt
import FV.Opt.Proof.SimpPass
import FV.E2E.SretReturn

/-!
# The `sret` return register over the mid-end (S7)

`backend_correct_opt_abi`, `backend_correct_opt_proven_abi`: `backend_correct_opt` /
`backend_correct_opt_proven` with the premise `sretStableB (Opt.optimize f cfg) = true` (the
per-function check on the compiled, optimised function), and a return also leaves the ABI
return values `sretArg f args` in x8 after the CLIF ones in x0.. (`ArmRefinesAbi`). The optimiser
keeps the signature (`Opt.optimize_facts`), so `sretArg` of the optimised function is the
source's.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- `backend_correct_opt` with the ABI return values (`sretStableB` of the optimised function). -/
theorem backend_correct_opt_abi (cfg : Opt.Config)
    (hS : Opt.SimplifyPassSim cfg.simplifyFn cfg.skeletonFn)
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f)
    (hci : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ sig callee args, st.inst ≠ .callIndirect sig callee args)
    (hnt : ∀ B ∈ f.blocks, B.term.isTry = false)
    (hc : Compiled (Opt.optimize f cfg) k vc vcp rf af fa fb)
    (hSo : sretStableB (Opt.optimize f cfg) = true)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hTls : hasTls (Opt.optimize f cfg) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbols env)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env (Opt.optimizeProgram p cfg) (optEntry cfg f cs)) (fuel : Nat) :
    ArmRefinesAbi fb base ra (ArmStepX X H fa) s (sretArg f args) (Clif.runLoop env p fuel cs) := by
  have hF := Opt.optimize_facts cfg f
  obtain ⟨hcs', hSR⟩ := clifEntry_opt cfg hS hcs
  have hP : Opt.FunsSim p.funcs (Opt.optimizeProgram p cfg).funcs :=
    Opt.FunsSim.map (T := (Opt.optimize · cfg)) (Opt.optimize_sim cfg hS)
  obtain ⟨n', hn⟩ := Opt.runLoop_refines hE hP (ciFree_of_subset hsub hci hnt) fuel cs
    (optEntry cfg f cs) hSR (inv_of_entry hcs)
  have hslots : (optEntry cfg f cs).frame.slots = cs.frame.slots ∧
      (optEntry cfg f cs).mem = cs.mem := by
    obtain ⟨b, hb, -⟩ := hcs.entry
    obtain ⟨R, -, hent'⟩ := (Opt.optimize_sim cfg hS f).sim cs.mem.symbols
    obtain ⟨b', hb', -⟩ := hent' b hb
    simp [optEntry, hb']
  have hnci := hF.noCI (noCI_of f hci hnt)
  have hA := backend_correct_final_abi (inSubset_opt cfg hsub hci hnt) hc hSo hcov hC
    (fun ⟨B, hB, h⟩ => by rw [hnci.2 B hB] at h; cases h) hTls
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun _ => by rw [indSigs_nil_of_noCI hnci]; exact xCallsIndOk_nil _ _ _) hsym hslot hent hres
    hbe (by rw [hF.sig]; exact hargs) hcs'
    (by rw [rel_holds_slots hF.slots, hslots.1, hslots.2]; exact hrel) htr n'
  have hsa : sretArg (Opt.optimize f cfg) args = sretArg f args := by
    simp only [sretArg, hF.sig]
  rw [hsa] at hA
  obtain ⟨hret, htrap⟩ := hn
  cases hr : Clif.runLoop env p fuel cs with
  | returned vals m => rw [hret vals m hr] at hA; exact hA
  | trapped c => rw [htrap c hr] at hA; exact hA
  | stuck _ => trivial
  | outOfFuel => trivial

/-- `backend_correct_opt_proven` with the ABI return values (`sretStableB` of the optimised
function). -/
theorem backend_correct_opt_proven_abi (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven)
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f)
    (hci : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ sig callee args, st.inst ≠ .callIndirect sig callee args)
    (hnt : ∀ B ∈ f.blocks, B.term.isTry = false)
    (hc : Compiled (Opt.optimize f cfg) k vc vcp rf af fa fb)
    (hSo : sretStableB (Opt.optimize f cfg) = true)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hTls : hasTls (Opt.optimize f cfg) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbols env)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env (Opt.optimizeProgram p cfg) (optEntry cfg f cs)) (fuel : Nat) :
    ArmRefinesAbi fb base ra (ArmStepX X H fa) s (sretArg f args) (Clif.runLoop env p fuel cs) :=
  backend_correct_opt_abi cfg (Opt.simplifyPassSim_proven hr ha) hsub hci hnt hc hSo hcov hC hTls
    hX hsym hslot hE hent hres hbe hargs hcs hrel htr fuel

end E2E
