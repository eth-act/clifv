import FV.E2E.OptProven
import FV.E2E.DeadCleanupOpt

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver

theorem backend_correct_opt_proven_cleanup (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven)
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f)
    (hci : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ sig callee args, st.inst ≠ .callIndirect sig callee args)
    (hnt : ∀ B ∈ f.blocks, B.term.isTry = false)
    (hc : CompiledCleanup (Opt.optimize f cfg) k vc vcp rf af fa fb)
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
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) :=
  backend_correct_opt_cleanup cfg (Opt.simplifyPassSim_proven hr ha) hsub hci hnt hc hcov hC hTls hX hsym hslot hE
    hent hres hbe hargs hcs hrel htr fuel

end E2E
