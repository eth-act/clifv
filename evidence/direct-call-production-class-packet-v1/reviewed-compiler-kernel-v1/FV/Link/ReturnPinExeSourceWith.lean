import FV.Link.ReturnPinCompilerSourceKernel
import FV.Link.SemanticExeSourceWith
import FV.Link.ReturnPinExeWith

/-! Original-source correctness for the ABI-aware executable attempt.
The source, world and foreign-code conditions match the retained semantic variants. -/
set_option autoImplicit false
namespace Link.ReturnPinCompilerWith
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128
variable {lower : ProductionLowering}

theorem attempt_correct_source {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) (hsrc : SrcScopeB (input lower S cleanup) = true)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S cleanup) B)) (hH : HooksSim (input lower S cleanup) B)
    (hlegal : (∃ f ∈ (input lower S cleanup).toLinkInput.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S cleanup)).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (input lower S cleanup).toLinkInput.srcProg.func? n = some f)
    (hc : ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls (input lower S cleanup) (input lower S cleanup).results) (legalize f))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) (legalize f)
      (SemanticStackBound.stackFn (input lower S cleanup) (legalize f)) r args' cs'.mem)
    (hr : ClifRun (input lower S cleanup) B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env (input lower S cleanup).toLinkInput.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env (input lower S cleanup).toLinkInput.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art (input lower S cleanup) (legalize f)).fb (art (input lower S cleanup) (legalize f)).base (xreg 30 r)
          (step (input lower S cleanup) B file) r (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results) (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog (input lower S cleanup)) B.env M) (prog (input lower S cleanup)).bare cs') →
      Opt.Legal.NoMemTrap B.env (input lower S cleanup).toLinkInput.srcProg cs → ∀ c,
      Clif.runLoop B.env (input lower S cleanup).toLinkInput.srcProg M cs = .trapped c →
      ExecRefines (art (input lower S cleanup) (legalize f)).fb (art (input lower S cleanup) (legalize f)).base (xreg 30 r)
        (step (input lower S cleanup) B file) r (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results) (.trapped c)) := by
  exact Link.ReturnPinCompilerFor.attempt_correct_source
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (S := S) (cleanup := cleanup)
    (file0 := file0) (file := file) (h := h)
    (hsrc := hsrc) (B := B) (hB := hB)
    (hH := hH) (hlegal := hlegal) (hsig := hsig)
    (n := n) (f := f) (hf := hf)
    (hc := hc) (r := r) (args := args)
    (args' := args') (cs := cs) (cs' := cs')
    (hX := hX) (ho := ho) (hr := hr)
    (hcs := hcs) (hexp := hexp) (hsl := hsl)
    (hmem := hmem) (hbnd := hbnd) (M := M)

/-- **The executable compiler refines the original source program, recursive programs
included** (S3, L1d): `attempt_correct_source` without the call-graph premise. The outside
caller of `legalize f`'s code provides `frameDrop + D * d` bytes of stack, where `d` bounds the
call depth of the **source** run from `cs` (`Clif.DepthLe`: no state the whole-program run of the
original program reaches has more than `d` callers). A return of the source run is the
executable's return of the results split by `f`'s return groups with the same memory; a trap
(of a source run without load/store traps, the target runs' traps explicit under
`Clif.linkEnvD` at every fuel) is the same trap. -/
theorem attempt_correct_source_peak {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) (hsrc : SrcScopeB (input lower S cleanup) = true)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S cleanup) B)) (hH : HooksSim (input lower S cleanup) B)
    (hlegal : (∃ f ∈ (input lower S cleanup).toLinkInput.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S cleanup)).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (input lower S cleanup).toLinkInput.srcProg.func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) (legalize f)
      (frameDrop (art (input lower S cleanup) (legalize f)).af + (input lower S cleanup).D * d) r args' cs'.mem)
    (hr : ClifRun (input lower S cleanup) B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env (input lower S cleanup).toLinkInput.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env (input lower S cleanup).toLinkInput.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env (input lower S cleanup).toLinkInput.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art (input lower S cleanup) (legalize f)).fb (art (input lower S cleanup) (legalize f)).base (xreg 30 r)
          (step (input lower S cleanup) B file) r (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog (input lower S cleanup)) B.env F d) (prog (input lower S cleanup)).bare cs') →
      Opt.Legal.NoMemTrap B.env (input lower S cleanup).toLinkInput.srcProg cs → ∀ c,
      Clif.runLoop B.env (input lower S cleanup).toLinkInput.srcProg M cs = .trapped c →
      ExecRefines (art (input lower S cleanup) (legalize f)).fb (art (input lower S cleanup) (legalize f)).base (xreg 30 r)
        (step (input lower S cleanup) B file) r (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results) (.trapped c)) := by
  exact Link.ReturnPinCompilerFor.attempt_correct_source_peak
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (S := S) (cleanup := cleanup)
    (file0 := file0) (file := file) (h := h)
    (hsrc := hsrc) (B := B) (hB := hB)
    (hH := hH) (hlegal := hlegal) (hsig := hsig)
    (n := n) (f := f) (hf := hf)
    (d := d) (r := r) (args := args)
    (args' := args') (cs := cs) (cs' := cs')
    (hX := hX) (ho := ho) (hr := hr)
    (hcs := hcs) (hexp := hexp) (hsl := hsl)
    (hmem := hmem) (hbnd := hbnd) (hd := hd)
    (M := M)

end Link.ReturnPinCompilerWith
