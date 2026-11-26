import FV.Link.MidSourceTB
import FV.Link.MidProgSyms

/-! # The typed Stock route's `SrcScopeTB` theorems through the mid-end validator, hoisting mode (#1119)

`attemptT_correct_sourceTBMidS`, `attemptT_correct_source_peakTBMidS`: `FV/Link/MidSourceTB.lean`'s
`…TBMid` theorems with the premise at the route input's symbol table, `hv : Opt.FunsSimMUAt
(fun n => (input lower S true).syms.lookup n) P0.funcs Q.funcs` (decided by
`Link.midValidatedSymsB` on that table; the hoisting mode of the validator), through
`Link.midProgAt` / `Link.midProgAt_depth`; the run's memory has that table by the outside call
premise (`OutsideCall.symbols`). The `…TBMid` theorems are unchanged. -/

set_option autoImplicit false

namespace Link.SemanticCompilerWith
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128
variable {lower : ProductionLowering}

/-- **`attemptT_correct_sourceTB` about a program validated against the route's source
program** (module doc). -/
theorem attemptT_correct_sourceTBMidS {S : LinkSpec} {file0 file : ByteArray}
    (h : attemptT lower S file0 = .ok file) (hsrc : SrcScopeTB (input lower S true) = true)
    {P0 : Clif.Program}
    (hv : Opt.FunsSimMUAt (fun n => (input lower S true).syms.lookup n)
      P0.funcs (input lower S true).toLinkInput.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S true) B)) (hH : HooksSim (input lower S true) B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ (input lower S true).toLinkInput.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S true)).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f g : Clif.Function} (hf : P0.func? n = some f)
    (hg : (input lower S true).toLinkInput.srcProg.func? n = some g)
    (hc : ¬ SemanticStackBound.CycleFrom
      (SemanticStackBound.Calls (input lower S true) (input lower S true).results) (legalize g))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S true) (BinCheck.roByte (input lower S true) S.data) (legalize g)
      (SemanticStackBound.stackFn (input lower S true) (legalize g)) r args' cs'.mem)
    (hr : ClifRun (input lower S true) B (legalize g) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env (input lower S true).toLinkInput.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env P0 M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecBytes.ExecRefinesT (art (input lower S true) (legalize g)).fb
          (art (input lower S true) (legalize g)).base (xreg 30 r)
          (step (input lower S true) B file) r
          (RelocAtWithResults (input lower S true) (input lower S true).results) (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog (input lower S true)) B.env M)
        (prog (input lower S true)).bare cs') →
      Opt.Legal.NoMemTrap B.env (input lower S true).toLinkInput.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env P0 M cs = .trapped c →
      ExecBytes.ExecRefinesT (art (input lower S true) (legalize g)).fb
        (art (input lower S true) (legalize g)).base (xreg 30 r)
        (step (input lower S true) B file) r
        (RelocAtWithResults (input lower S true) (input lower S true).results) (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) M
  have hTB := fun (m : Nat) => attemptT_correct_sourceTB h hsrc B hB hH hlegal hsig hg hc
    hX ho hr hcs1 (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm) (hmem.trans hmem1.symm) hbnd m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨m, hm⟩ := hret vals cm hrun
    have := (hTB m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨m, hm⟩ := htrap c hrun
    exact (hTB m).2 htr hnmt c hm

/-- **`attemptT_correct_source_peakTB` about a program validated against the route's source
program** (module doc): the call-depth bound `d` of `P0`'s run from `cs` carried to `Q`'s run
from `midEntry g cs` by `Link.midProgAt_depth`. -/
theorem attemptT_correct_source_peakTBMidS {S : LinkSpec} {file0 file : ByteArray}
    (h : attemptT lower S file0 = .ok file) (hsrc : SrcScopeTB (input lower S true) = true)
    {P0 : Clif.Program}
    (hv : Opt.FunsSimMUAt (fun n => (input lower S true).syms.lookup n)
      P0.funcs (input lower S true).toLinkInput.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S true) B)) (hH : HooksSim (input lower S true) B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ (input lower S true).toLinkInput.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S true)).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f g : Clif.Function} (hf : P0.func? n = some f)
    (hg : (input lower S true).toLinkInput.srcProg.func? n = some g)
    (d : Nat) {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S true) (BinCheck.roByte (input lower S true) S.data) (legalize g)
      (frameDrop (art (input lower S true) (legalize g)).af +
        ((input lower S true).D * d + pbMax (input lower S true))) r args' cs'.mem)
    (hr : ClifRun (input lower S true) B (legalize g) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env (input lower S true).toLinkInput.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env P0 d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env P0 M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecBytes.ExecRefinesT (art (input lower S true) (legalize g)).fb
          (art (input lower S true) (legalize g)).base (xreg 30 r)
          (step (input lower S true) B file) r
          (RelocAtWithResults (input lower S true) (input lower S true).results) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog (input lower S true)) B.env F d)
        (prog (input lower S true)).bare cs') →
      Opt.Legal.NoMemTrap B.env (input lower S true).toLinkInput.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env P0 M cs = .trapped c →
      ExecBytes.ExecRefinesT (art (input lower S true) (legalize g)).fb
        (art (input lower S true) (legalize g)).base (xreg 30 r)
        (step (input lower S true) B file) r
        (RelocAtWithResults (input lower S true) (input lower S true).results) (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt_depth hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) hd M
  have hTB := fun (hd1 : Clif.DepthLe B.env (input lower S true).toLinkInput.srcProg d (midEntry g cs))
      (m : Nat) => attemptT_correct_source_peakTB h hsrc B hB hH hlegal hsig hg d hX ho hr hcs1
    (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm) (hmem.trans hmem1.symm) hbnd hd1 m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨⟨m, hm⟩, hd1⟩ := hret vals cm hrun
    have := (hTB hd1 m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨⟨m, hm⟩, hd1⟩ := htrap c hrun
    exact (hTB hd1 m).2 htr hnmt c hm

end Link.SemanticCompilerWith
