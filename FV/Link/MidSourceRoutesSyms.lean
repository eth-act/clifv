import FV.Link.MidSourceRoutes
import FV.Link.MidProgSyms

/-! # The routes' executable theorems about the bundle's unoptimised program, hoisting mode (#1119)

`FV/Link/MidSourceRoutes.lean`'s `…Mid` theorems with the premise at the route input's symbol
table: for each route's `…_sourceCp` theorem (about `I1.srcProg`) the `…MidS` theorem here (same
namespace) concludes the same about `I0.srcProg`, from `hv : Opt.FunsSimMUAt syms
I0.srcProg.funcs I1.srcProg.funcs` with `syms` the symbol table of the route's input (the one its
outside call premise `ho` fixes for the run's memory: `OutsideCall.symbols`), through
`Link.midProgAt` (`midProgAt_depth` for the peak versions). `lean-link --verified` decides `hv` by
`Link.midValidatedSymsB` on that table (`Link.midValidatedSymsB_sound`): the pairs `midPairB`
accepts, and those the hoisting mode accepts where the global values of the compared copy of the
unoptimised function resolve (Cranelift's loop-invariant code motion hoists `symbol_value`).
Every `…Mid` premise gives this one (`ValidatedC.funsSimMU`, `FunsSimMU.at`); the `…Mid`
theorems are unchanged.

Premises otherwise as the `…Mid` theorems'.
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.Binary E2E.ExecBytes E2E.LegalProgram Backend
  LinkSpec Opt.Legalize128

/-- **`Link.compileExe_correct_sourceCp` about the bundle's unoptimised program** (module doc): the theorem at
the compiled inputs `I1`, composed with `Link.midProgAt`; a return (trap) of `I0`'s source run from
`f`'s entry `cs` is the executable's return of the results split by `f`'s return groups (the same
trap). -/
theorem compileExe_correct_sourceMidS {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) {I0 I1 : LinkInput}
    (hcp : S.funcs = I1.funcs.map FnInput.cp) (hsrc : SrcScopeB I1 = true)
    (hv : Opt.FunsSimMUAt (fun n => S.input.syms.lookup n)
      I0.srcProg.funcs I1.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys S.input B)) (hH : HooksSim S.input B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I1.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f g f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hg : I1.srcProg.func? n = some g)
    (hf' : (prog S.input).func? n = some f')
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.input S.input.results) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) f'
      (StackBound.stackFn S.input f') r args' cs'.mem)
    (hr : ClifRun S.input B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I1.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.input f').fb (art S.input f').base
          (xreg 30 r) (step S.input B file) r (RelocAt S.input) (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.input) B.env M) (prog S.input).bare cs') →
      Opt.Legal.NoMemTrap B.env I1.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefines (art S.input f').fb (art S.input f').base
        (xreg 30 r) (step S.input B file) r (RelocAt S.input) (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) M
  have hcp' := fun (m : Nat) => compileExe_correct_sourceCp h hcp hsrc B hB hH hkeep hlegal hsig hg hf' hc
    hX ho hr hcs1 (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm) (hmem.trans hmem1.symm) hbnd m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨m, hm⟩ := hret vals cm hrun
    have := (hcp' m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨m, hm⟩ := htrap c hrun
    exact (hcp' m).2 htr hnmt c hm

/-- **`Link.compileExe_correct_source_peakCp` about the bundle's unoptimised program** (module doc): the call-depth
bound `d` of `I0`'s source run from `cs` carried to `I1`'s run from `midEntry g cs` by
`Link.midProgAt_depth`. -/
theorem compileExe_correct_source_peakMidS {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) {I0 I1 : LinkInput}
    (hcp : S.funcs = I1.funcs.map FnInput.cp) (hsrc : SrcScopeB I1 = true)
    (hv : Opt.FunsSimMUAt (fun n => S.input.syms.lookup n)
      I0.srcProg.funcs I1.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys S.input B)) (hH : HooksSim S.input B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I1.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f g f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hg : I1.srcProg.func? n = some g)
    (hf' : (prog S.input).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) f'
      (frameDrop (art S.input f').af + (S.input.D * d + pbMax S.input)) r args' cs'.mem)
    (hr : ClifRun S.input B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I1.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env I0.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.input f').fb (art S.input f').base
          (xreg 30 r) (step S.input B file) r (RelocAt S.input) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.input) B.env F d) (prog S.input).bare cs') →
      Opt.Legal.NoMemTrap B.env I1.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefines (art S.input f').fb (art S.input f').base
        (xreg 30 r) (step S.input B file) r (RelocAt S.input) (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt_depth hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) hd M
  have hcp' := fun (hd1 : Clif.DepthLe B.env I1.srcProg d (midEntry g cs)) (m : Nat) =>
    compileExe_correct_source_peakCp h hcp hsrc B hB hH hkeep hlegal hsig
    hg hf' d hX ho hr hcs1 (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm)
    (hmem.trans hmem1.symm) hbnd hd1 m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨⟨m, hm⟩, hd1⟩ := hret vals cm hrun
    have := (hcp' hd1 m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨⟨m, hm⟩, hd1⟩ := htrap c hrun
    exact (hcp' hd1 m).2 htr hnmt c hm

end Link

namespace Link.DeadCleanup

set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128

/-- **`Link.DeadCleanup.compileExe_correct_sourceCp` about the bundle's unoptimised program** (module doc): the theorem at
the compiled inputs `I1`, composed with `Link.midProgAt`; a return (trap) of `I0`'s source run from
`f`'s entry `cs` is the executable's return of the results split by `f`'s return groups (the same
trap). -/
theorem compileExe_correct_sourceMidS {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) {I0 I1 : LinkInput}
    (hcp : S.funcs = I1.funcs.map FnInput.cp) (hsrc : SrcScopeB I1 = true)
    (hv : Opt.FunsSimMUAt (fun n => S.inputCleanup.syms.lookup n)
      I0.srcProg.funcs I1.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I1.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f g f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hg : I1.srcProg.func? n = some g)
    (hf' : (prog S.inputCleanup).func? n = some f')
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f'
      (DeadCleanupStackBound.stackFn S.inputCleanup f') r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I1.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup f').fb (art S.inputCleanup f').base
          (xreg 30 r) (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env I1.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefines (art S.inputCleanup f').fb (art S.inputCleanup f').base
        (xreg 30 r) (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) M
  have hcp' := fun (m : Nat) => compileExe_correct_sourceCp h hcp hsrc B hB hH hkeep hlegal hsig hg hf' hc
    hX ho hr hcs1 (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm) (hmem.trans hmem1.symm) hbnd m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨m, hm⟩ := hret vals cm hrun
    have := (hcp' m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨m, hm⟩ := htrap c hrun
    exact (hcp' m).2 htr hnmt c hm

/-- **`Link.DeadCleanup.compileExe_correct_source_peakCp` about the bundle's unoptimised program** (module doc): the call-depth
bound `d` of `I0`'s source run from `cs` carried to `I1`'s run from `midEntry g cs` by
`Link.midProgAt_depth`. -/
theorem compileExe_correct_source_peakMidS {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) {I0 I1 : LinkInput}
    (hcp : S.funcs = I1.funcs.map FnInput.cp) (hsrc : SrcScopeB I1 = true)
    (hv : Opt.FunsSimMUAt (fun n => S.inputCleanup.syms.lookup n)
      I0.srcProg.funcs I1.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I1.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f g f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hg : I1.srcProg.func? n = some g)
    (hf' : (prog S.inputCleanup).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f'
      (frameDrop (art S.inputCleanup f').af + (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I1.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env I0.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup f').fb (art S.inputCleanup f').base
          (xreg 30 r) (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env I1.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefines (art S.inputCleanup f').fb (art S.inputCleanup f').base
        (xreg 30 r) (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt_depth hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) hd M
  have hcp' := fun (hd1 : Clif.DepthLe B.env I1.srcProg d (midEntry g cs)) (m : Nat) =>
    compileExe_correct_source_peakCp h hcp hsrc B hB hH hkeep hlegal hsig
    hg hf' d hX ho hr hcs1 (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm)
    (hmem.trans hmem1.symm) hbnd hd1 m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨⟨m, hm⟩, hd1⟩ := hret vals cm hrun
    have := (hcp' hd1 m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨⟨m, hm⟩, hd1⟩ := htrap c hrun
    exact (hcp' hd1 m).2 htr hnmt c hm

end Link.DeadCleanup

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.Binary E2E.ExecBytes E2E.LegalProgram Backend
  LinkSpec Opt.Legalize128

/-- **`Link.compileExeOpt_correct_sourceCp` about the bundle's unoptimised program** (module doc): the theorem at
the compiled inputs `I1`, composed with `Link.midProgAt`; a return (trap) of `I0`'s source run from
`f`'s entry `cs` is the executable's return of the results split by `f`'s return groups (the same
trap). -/
theorem compileExeOpt_correct_sourceMidS {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) {I0 I1 : LinkInput}
    (hcp : S.funcs = I1.funcs.map FnInput.cp) (hsrc : SrcScopeB I1 = true)
    (hv : Opt.FunsSimMUAt (fun n => S.opt.input.syms.lookup n)
      I0.srcProg.funcs I1.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.input B)) (hH : HooksSim S.opt.input B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I1.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f g f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hg : I1.srcProg.func? n = some g)
    (hf' : (prog S.opt.input).func? n = some f')
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.opt.input S.opt.input.results) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.input (BinCheck.roByte S.opt.input S.opt.data) f'
      (StackBound.stackFn S.opt.input f') r args' cs'.mem)
    (hr : ClifRun S.opt.input B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I1.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.opt.input f').fb (art S.opt.input f').base (xreg 30 r)
          (step S.opt.input B file) r (RelocAt S.opt.input) (.returned vals' cm)) ∧
    ((∀ K, TrapsExplicit (Clif.linkEnvN (prog S.opt.input) B.env K) (prog S.opt.input).bare cs') →
      Opt.Legal.NoMemTrap B.env I1.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefines (art S.opt.input f').fb (art S.opt.input f').base (xreg 30 r)
        (step S.opt.input B file) r (RelocAt S.opt.input) (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) M
  have hcp' := fun (m : Nat) => compileExeOpt_correct_sourceCp h hcp hsrc B hB hH hkeep hlegal hsig hg hf' hc
    hX ho hr hcs1 (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm) (hmem.trans hmem1.symm) hbnd m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨m, hm⟩ := hret vals cm hrun
    have := (hcp' m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨m, hm⟩ := htrap c hrun
    exact (hcp' m).2 htr hnmt c hm

/-- **`Link.compileExeOpt_correct_source_peakCp` about the bundle's unoptimised program** (module doc): the call-depth
bound `d` of `I0`'s source run from `cs` carried to `I1`'s run from `midEntry g cs` by
`Link.midProgAt_depth`. -/
theorem compileExeOpt_correct_source_peakMidS {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) {I0 I1 : LinkInput}
    (hcp : S.funcs = I1.funcs.map FnInput.cp) (hsrc : SrcScopeB I1 = true)
    (hv : Opt.FunsSimMUAt (fun n => S.opt.input.syms.lookup n)
      I0.srcProg.funcs I1.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.input B)) (hH : HooksSim S.opt.input B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I1.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f g f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hg : I1.srcProg.func? n = some g)
    (hf' : (prog S.opt.input).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.input (BinCheck.roByte S.opt.input S.opt.data) f'
      (frameDrop (art S.opt.input f').af + (S.opt.input.D * d + pbMax S.opt.input)) r args' cs'.mem)
    (hr : ClifRun S.opt.input B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I1.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env I0.srcProg d cs) (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.opt.input f').fb (art S.opt.input f').base (xreg 30 r)
          (step S.opt.input B file) r (RelocAt S.opt.input) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.opt.input) B.env F d) (prog S.opt.input).bare cs') →
      Opt.Legal.NoMemTrap B.env I1.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefines (art S.opt.input f').fb (art S.opt.input f').base (xreg 30 r)
        (step S.opt.input B file) r (RelocAt S.opt.input) (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt_depth hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) hd M
  have hcp' := fun (hd1 : Clif.DepthLe B.env I1.srcProg d (midEntry g cs)) (m : Nat) =>
    compileExeOpt_correct_source_peakCp h hcp hsrc B hB hH hkeep hlegal hsig
    hg hf' d hX ho hr hcs1 (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm)
    (hmem.trans hmem1.symm) hbnd hd1 m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨⟨m, hm⟩, hd1⟩ := hret vals cm hrun
    have := (hcp' hd1 m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨⟨m, hm⟩, hd1⟩ := htrap c hrun
    exact (hcp' hd1 m).2 htr hnmt c hm

end Link

namespace Link.DeadCleanup

set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128

/-- **`Link.DeadCleanup.compileExeOpt_correct_sourceCp` about the bundle's unoptimised program** (module doc): the theorem at
the compiled inputs `I1`, composed with `Link.midProgAt`; a return (trap) of `I0`'s source run from
`f`'s entry `cs` is the executable's return of the results split by `f`'s return groups (the same
trap). -/
theorem compileExeOpt_correct_sourceMidS {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) {I0 I1 : LinkInput}
    (hcp : S.funcs = I1.funcs.map FnInput.cp) (hsrc : SrcScopeB I1 = true)
    (hv : Opt.FunsSimMUAt (fun n => S.opt.inputCleanup.syms.lookup n)
      I0.srcProg.funcs I1.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.inputCleanup B)) (hH : HooksSim S.opt.inputCleanup B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I1.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f g f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hg : I1.srcProg.func? n = some g)
    (hf' : (prog S.opt.inputCleanup).func? n = some f')
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.opt.inputCleanup S.opt.inputCleanup.resultsCleanup) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.inputCleanup (BinCheck.roByte S.opt.inputCleanup S.opt.data) f'
      (DeadCleanupStackBound.stackFn S.opt.inputCleanup f') r args' cs'.mem)
    (hr : ClifRun S.opt.inputCleanup B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I1.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
          (step S.opt.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.opt.inputCleanup) (.returned vals' cm)) ∧
    ((∀ K, TrapsExplicit (Clif.linkEnvN (prog S.opt.inputCleanup) B.env K) (prog S.opt.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env I1.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefines (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
        (step S.opt.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.opt.inputCleanup) (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) M
  have hcp' := fun (m : Nat) => compileExeOpt_correct_sourceCp h hcp hsrc B hB hH hkeep hlegal hsig hg hf' hc
    hX ho hr hcs1 (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm) (hmem.trans hmem1.symm) hbnd m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨m, hm⟩ := hret vals cm hrun
    have := (hcp' m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨m, hm⟩ := htrap c hrun
    exact (hcp' m).2 htr hnmt c hm

/-- **`Link.DeadCleanup.compileExeOpt_correct_source_peakCp` about the bundle's unoptimised program** (module doc): the call-depth
bound `d` of `I0`'s source run from `cs` carried to `I1`'s run from `midEntry g cs` by
`Link.midProgAt_depth`. -/
theorem compileExeOpt_correct_source_peakMidS {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) {I0 I1 : LinkInput}
    (hcp : S.funcs = I1.funcs.map FnInput.cp) (hsrc : SrcScopeB I1 = true)
    (hv : Opt.FunsSimMUAt (fun n => S.opt.inputCleanup.syms.lookup n)
      I0.srcProg.funcs I1.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.inputCleanup B)) (hH : HooksSim S.opt.inputCleanup B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I1.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f g f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hg : I1.srcProg.func? n = some g)
    (hf' : (prog S.opt.inputCleanup).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.inputCleanup (BinCheck.roByte S.opt.inputCleanup S.opt.data) f'
      (frameDrop (art S.opt.inputCleanup f').af + (S.opt.inputCleanup.D * d + pbMax S.opt.inputCleanup)) r args' cs'.mem)
    (hr : ClifRun S.opt.inputCleanup B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I1.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env I0.srcProg d cs) (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
          (step S.opt.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.opt.inputCleanup) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.opt.inputCleanup) B.env F d) (prog S.opt.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env I1.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefines (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
        (step S.opt.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.opt.inputCleanup) (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt_depth hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) hd M
  have hcp' := fun (hd1 : Clif.DepthLe B.env I1.srcProg d (midEntry g cs)) (m : Nat) =>
    compileExeOpt_correct_source_peakCp h hcp hsrc B hB hH hkeep hlegal hsig
    hg hf' d hX ho hr hcs1 (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm)
    (hmem.trans hmem1.symm) hbnd hd1 m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨⟨m, hm⟩, hd1⟩ := hret vals cm hrun
    have := (hcp' hd1 m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨⟨m, hm⟩, hd1⟩ := htrap c hrun
    exact (hcp' hd1 m).2 htr hnmt c hm

end Link.DeadCleanup

namespace Link.DeadCleanup

set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128

/-- **`Link.DeadCleanup.compileExeT_correct_sourceCp` about the bundle's unoptimised program** (module doc): the theorem at
the compiled inputs `I1`, composed with `Link.midProgAt`; a return (trap) of `I0`'s source run from
`f`'s entry `cs` is the executable's return of the results split by `f`'s return groups (the same
trap). -/
theorem compileExeT_correct_sourceMidS {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeT S file0 = .ok file) {I0 I1 : LinkInput}
    (hcp : S.funcs = I1.funcs.map FnInput.cp) (hsrc : SrcScopeB I1 = true)
    (hv : Opt.FunsSimMUAt (fun n => S.inputCleanup.syms.lookup n)
      I0.srcProg.funcs I1.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I1.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f g f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hg : I1.srcProg.func? n = some g)
    (hf' : (prog S.inputCleanup).func? n = some f')
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f'
      (DeadCleanupStackBound.stackFn S.inputCleanup f') r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I1.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
          (xreg 30 r) (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env I1.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
        (xreg 30 r) (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) M
  have hcp' := fun (m : Nat) => compileExeT_correct_sourceCp h hcp hsrc B hB hH hkeep hlegal hsig hg hf' hc
    hX ho hr hcs1 (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm) (hmem.trans hmem1.symm) hbnd m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨m, hm⟩ := hret vals cm hrun
    have := (hcp' m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨m, hm⟩ := htrap c hrun
    exact (hcp' m).2 htr hnmt c hm

/-- **`Link.DeadCleanup.compileExeT_correct_source_peakCp` about the bundle's unoptimised program** (module doc): the call-depth
bound `d` of `I0`'s source run from `cs` carried to `I1`'s run from `midEntry g cs` by
`Link.midProgAt_depth`. -/
theorem compileExeT_correct_source_peakMidS {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeT S file0 = .ok file) {I0 I1 : LinkInput}
    (hcp : S.funcs = I1.funcs.map FnInput.cp) (hsrc : SrcScopeB I1 = true)
    (hv : Opt.FunsSimMUAt (fun n => S.inputCleanup.syms.lookup n)
      I0.srcProg.funcs I1.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I1.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f g f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hg : I1.srcProg.func? n = some g)
    (hf' : (prog S.inputCleanup).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f'
      (frameDrop (art S.inputCleanup f').af + (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I1.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env I0.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
          (xreg 30 r) (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env I1.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
        (xreg 30 r) (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt_depth hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) hd M
  have hcp' := fun (hd1 : Clif.DepthLe B.env I1.srcProg d (midEntry g cs)) (m : Nat) =>
    compileExeT_correct_source_peakCp h hcp hsrc B hB hH hkeep hlegal hsig
    hg hf' d hX ho hr hcs1 (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm)
    (hmem.trans hmem1.symm) hbnd hd1 m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨⟨m, hm⟩, hd1⟩ := hret vals cm hrun
    have := (hcp' hd1 m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨⟨m, hm⟩, hd1⟩ := htrap c hrun
    exact (hcp' hd1 m).2 htr hnmt c hm

end Link.DeadCleanup

namespace Link.ReturnPinCompilerWith

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128
variable {lower : ProductionLowering}

/-- **`Link.ReturnPinCompilerWith.attempt_correct_sourceCp` about the bundle's unoptimised program** (module doc): the theorem at
the compiled inputs `I1`, composed with `Link.midProgAt`; a return (trap) of `I0`'s source run from
`f`'s entry `cs` is the executable's return of the results split by `f`'s return groups (the same
trap). -/
theorem attempt_correct_sourceMidS {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) {I0 I1 : LinkInput}
    (hcp : S.funcs = I1.funcs.map FnInput.cp) (hsrc : SrcScopeB I1 = true)
    (hv : Opt.FunsSimMUAt (fun n => (input lower S cleanup).syms.lookup n)
      I0.srcProg.funcs I1.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S cleanup) B))
    (hH : HooksSim (input lower S cleanup) B) (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I1.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S cleanup)).funcs, ¬ Clif.IndFree g) →
      ∀ n, B.env.sigOf n = none)
    {n : String} {f g f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hg : I1.srcProg.func? n = some g)
    (hf' : (prog (input lower S cleanup)).func? n = some f')
    (hc : ¬ SemanticStackBound.CycleFrom
      (SemanticStackBound.Calls (input lower S cleanup) (input lower S cleanup).results) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) f'
      (SemanticStackBound.stackFn (input lower S cleanup) f') r args' cs'.mem)
    (hr : ClifRun (input lower S cleanup) B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I1.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art (input lower S cleanup) f').fb (art (input lower S cleanup) f').base
          (xreg 30 r) (step (input lower S cleanup) B file) r
          (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results)
          (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog (input lower S cleanup)) B.env M)
        (prog (input lower S cleanup)).bare cs') →
      Opt.Legal.NoMemTrap B.env I1.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefines (art (input lower S cleanup) f').fb (art (input lower S cleanup) f').base
        (xreg 30 r) (step (input lower S cleanup) B file) r
        (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results)
        (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) M
  have hcp' := fun (m : Nat) => attempt_correct_sourceCp h hcp hsrc B hB hH hkeep hlegal hsig hg hf' hc
    hX ho hr hcs1 (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm) (hmem.trans hmem1.symm) hbnd m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨m, hm⟩ := hret vals cm hrun
    have := (hcp' m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨m, hm⟩ := htrap c hrun
    exact (hcp' m).2 htr hnmt c hm

/-- **`Link.ReturnPinCompilerWith.attempt_correct_source_peakCp` about the bundle's unoptimised program** (module doc): the call-depth
bound `d` of `I0`'s source run from `cs` carried to `I1`'s run from `midEntry g cs` by
`Link.midProgAt_depth`. -/
theorem attempt_correct_source_peakMidS {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) {I0 I1 : LinkInput}
    (hcp : S.funcs = I1.funcs.map FnInput.cp) (hsrc : SrcScopeB I1 = true)
    (hv : Opt.FunsSimMUAt (fun n => (input lower S cleanup).syms.lookup n)
      I0.srcProg.funcs I1.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S cleanup) B))
    (hH : HooksSim (input lower S cleanup) B) (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I1.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S cleanup)).funcs, ¬ Clif.IndFree g) →
      ∀ n, B.env.sigOf n = none)
    {n : String} {f g f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hg : I1.srcProg.func? n = some g)
    (hf' : (prog (input lower S cleanup)).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) f'
      (frameDrop (art (input lower S cleanup) f').af +
        ((input lower S cleanup).D * d + pbMax (input lower S cleanup))) r args' cs'.mem)
    (hr : ClifRun (input lower S cleanup) B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I1.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env I0.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art (input lower S cleanup) f').fb (art (input lower S cleanup) f').base
          (xreg 30 r) (step (input lower S cleanup) B file) r
          (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results)
          (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog (input lower S cleanup)) B.env F d)
        (prog (input lower S cleanup)).bare cs') →
      Opt.Legal.NoMemTrap B.env I1.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefines (art (input lower S cleanup) f').fb (art (input lower S cleanup) f').base
        (xreg 30 r) (step (input lower S cleanup) B file) r
        (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results)
        (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt_depth hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) hd M
  have hcp' := fun (hd1 : Clif.DepthLe B.env I1.srcProg d (midEntry g cs)) (m : Nat) =>
    attempt_correct_source_peakCp h hcp hsrc B hB hH hkeep hlegal hsig
    hg hf' d hX ho hr hcs1 (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm)
    (hmem.trans hmem1.symm) hbnd hd1 m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨⟨m, hm⟩, hd1⟩ := hret vals cm hrun
    have := (hcp' hd1 m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨⟨m, hm⟩, hd1⟩ := htrap c hrun
    exact (hcp' hd1 m).2 htr hnmt c hm

end Link.ReturnPinCompilerWith

namespace Link.SemanticCompilerWith

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128
variable {lower : ProductionLowering}

/-- **`Link.SemanticCompilerWith.attempt_correct_sourceCp` about the bundle's unoptimised program** (module doc): the theorem at
the compiled inputs `I1`, composed with `Link.midProgAt`; a return (trap) of `I0`'s source run from
`f`'s entry `cs` is the executable's return of the results split by `f`'s return groups (the same
trap). -/
theorem attempt_correct_sourceMidS {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) {I0 I1 : LinkInput}
    (hcp : S.funcs = I1.funcs.map FnInput.cp) (hsrc : SrcScopeB I1 = true)
    (hv : Opt.FunsSimMUAt (fun n => (input lower S cleanup).syms.lookup n)
      I0.srcProg.funcs I1.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S cleanup) B))
    (hH : HooksSim (input lower S cleanup) B) (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I1.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S cleanup)).funcs, ¬ Clif.IndFree g) →
      ∀ n, B.env.sigOf n = none)
    {n : String} {f g f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hg : I1.srcProg.func? n = some g)
    (hf' : (prog (input lower S cleanup)).func? n = some f')
    (hc : ¬ SemanticStackBound.CycleFrom
      (SemanticStackBound.Calls (input lower S cleanup) (input lower S cleanup).results) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) f'
      (SemanticStackBound.stackFn (input lower S cleanup) f') r args' cs'.mem)
    (hr : ClifRun (input lower S cleanup) B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I1.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art (input lower S cleanup) f').fb (art (input lower S cleanup) f').base
          (xreg 30 r) (step (input lower S cleanup) B file) r
          (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results)
          (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog (input lower S cleanup)) B.env M)
        (prog (input lower S cleanup)).bare cs') →
      Opt.Legal.NoMemTrap B.env I1.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefines (art (input lower S cleanup) f').fb (art (input lower S cleanup) f').base
        (xreg 30 r) (step (input lower S cleanup) B file) r
        (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results)
        (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) M
  have hcp' := fun (m : Nat) => attempt_correct_sourceCp h hcp hsrc B hB hH hkeep hlegal hsig hg hf' hc
    hX ho hr hcs1 (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm) (hmem.trans hmem1.symm) hbnd m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨m, hm⟩ := hret vals cm hrun
    have := (hcp' m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨m, hm⟩ := htrap c hrun
    exact (hcp' m).2 htr hnmt c hm

/-- **`Link.SemanticCompilerWith.attempt_correct_source_peakCp` about the bundle's unoptimised program** (module doc): the call-depth
bound `d` of `I0`'s source run from `cs` carried to `I1`'s run from `midEntry g cs` by
`Link.midProgAt_depth`. -/
theorem attempt_correct_source_peakMidS {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) {I0 I1 : LinkInput}
    (hcp : S.funcs = I1.funcs.map FnInput.cp) (hsrc : SrcScopeB I1 = true)
    (hv : Opt.FunsSimMUAt (fun n => (input lower S cleanup).syms.lookup n)
      I0.srcProg.funcs I1.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S cleanup) B))
    (hH : HooksSim (input lower S cleanup) B) (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I1.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S cleanup)).funcs, ¬ Clif.IndFree g) →
      ∀ n, B.env.sigOf n = none)
    {n : String} {f g f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hg : I1.srcProg.func? n = some g)
    (hf' : (prog (input lower S cleanup)).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) f'
      (frameDrop (art (input lower S cleanup) f').af +
        ((input lower S cleanup).D * d + pbMax (input lower S cleanup))) r args' cs'.mem)
    (hr : ClifRun (input lower S cleanup) B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I1.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env I0.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art (input lower S cleanup) f').fb (art (input lower S cleanup) f').base
          (xreg 30 r) (step (input lower S cleanup) B file) r
          (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results)
          (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog (input lower S cleanup)) B.env F d)
        (prog (input lower S cleanup)).bare cs') →
      Opt.Legal.NoMemTrap B.env I1.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefines (art (input lower S cleanup) f').fb (art (input lower S cleanup) f').base
        (xreg 30 r) (step (input lower S cleanup) B file) r
        (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results)
        (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt_depth hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) hd M
  have hcp' := fun (hd1 : Clif.DepthLe B.env I1.srcProg d (midEntry g cs)) (m : Nat) =>
    attempt_correct_source_peakCp h hcp hsrc B hB hH hkeep hlegal hsig
    hg hf' d hX ho hr hcs1 (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm)
    (hmem.trans hmem1.symm) hbnd hd1 m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨⟨m, hm⟩, hd1⟩ := hret vals cm hrun
    have := (hcp' hd1 m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨⟨m, hm⟩, hd1⟩ := htrap c hrun
    exact (hcp' hd1 m).2 htr hnmt c hm

end Link.SemanticCompilerWith

namespace Link.SemanticCompilerWith

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128
variable {lower : ProductionLowering}

/-- **`Link.SemanticCompilerWith.attemptT_correct_sourceCp` about the bundle's unoptimised program** (module doc): the theorem at
the compiled inputs `I1`, composed with `Link.midProgAt`; a return (trap) of `I0`'s source run from
`f`'s entry `cs` is the executable's return of the results split by `f`'s return groups (the same
trap). -/
theorem attemptT_correct_sourceMidS {S : LinkSpec} {file0 file : ByteArray}
    (h : attemptT lower S file0 = .ok file) {I0 I1 : LinkInput}
    (hcp : S.funcs = I1.funcs.map FnInput.cp) (hsrc : SrcScopeB I1 = true)
    (hv : Opt.FunsSimMUAt (fun n => (input lower S true).syms.lookup n)
      I0.srcProg.funcs I1.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S true) B))
    (hH : HooksSim (input lower S true) B) (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I1.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S true)).funcs, ¬ Clif.IndFree g) →
      ∀ n, B.env.sigOf n = none)
    {n : String} {f g f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hg : I1.srcProg.func? n = some g)
    (hf' : (prog (input lower S true)).func? n = some f')
    (hc : ¬ SemanticStackBound.CycleFrom
      (SemanticStackBound.Calls (input lower S true) (input lower S true).results) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S true) (BinCheck.roByte (input lower S true) S.data) f'
      (SemanticStackBound.stackFn (input lower S true) f') r args' cs'.mem)
    (hr : ClifRun (input lower S true) B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I1.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecBytes.ExecRefinesT (art (input lower S true) f').fb (art (input lower S true) f').base
          (xreg 30 r) (step (input lower S true) B file) r
          (RelocAtWithResults (input lower S true) (input lower S true).results)
          (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog (input lower S true)) B.env M)
        (prog (input lower S true)).bare cs') →
      Opt.Legal.NoMemTrap B.env I1.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecBytes.ExecRefinesT (art (input lower S true) f').fb (art (input lower S true) f').base
        (xreg 30 r) (step (input lower S true) B file) r
        (RelocAtWithResults (input lower S true) (input lower S true).results)
        (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) M
  have hcp' := fun (m : Nat) => attemptT_correct_sourceCp h hcp hsrc B hB hH hkeep hlegal hsig hg hf' hc
    hX ho hr hcs1 (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm) (hmem.trans hmem1.symm) hbnd m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨m, hm⟩ := hret vals cm hrun
    have := (hcp' m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨m, hm⟩ := htrap c hrun
    exact (hcp' m).2 htr hnmt c hm

/-- **`Link.SemanticCompilerWith.attemptT_correct_source_peakCp` about the bundle's unoptimised program** (module doc): the call-depth
bound `d` of `I0`'s source run from `cs` carried to `I1`'s run from `midEntry g cs` by
`Link.midProgAt_depth`. -/
theorem attemptT_correct_source_peakMidS {S : LinkSpec} {file0 file : ByteArray}
    (h : attemptT lower S file0 = .ok file) {I0 I1 : LinkInput}
    (hcp : S.funcs = I1.funcs.map FnInput.cp) (hsrc : SrcScopeB I1 = true)
    (hv : Opt.FunsSimMUAt (fun n => (input lower S true).syms.lookup n)
      I0.srcProg.funcs I1.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S true) B))
    (hH : HooksSim (input lower S true) B) (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I1.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S true)).funcs, ¬ Clif.IndFree g) →
      ∀ n, B.env.sigOf n = none)
    {n : String} {f g f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hg : I1.srcProg.func? n = some g)
    (hf' : (prog (input lower S true)).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S true) (BinCheck.roByte (input lower S true) S.data) f'
      (frameDrop (art (input lower S true) f').af +
        ((input lower S true).D * d + pbMax (input lower S true))) r args' cs'.mem)
    (hr : ClifRun (input lower S true) B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I1.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env I0.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecBytes.ExecRefinesT (art (input lower S true) f').fb (art (input lower S true) f').base
          (xreg 30 r) (step (input lower S true) B file) r
          (RelocAtWithResults (input lower S true) (input lower S true).results)
          (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog (input lower S true)) B.env F d)
        (prog (input lower S true)).bare cs') →
      Opt.Legal.NoMemTrap B.env I1.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecBytes.ExecRefinesT (art (input lower S true) f').fb (art (input lower S true) f').base
        (xreg 30 r) (step (input lower S true) B file) r
        (RelocAtWithResults (input lower S true) (input lower S true).results)
        (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt_depth hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) hd M
  have hcp' := fun (hd1 : Clif.DepthLe B.env I1.srcProg d (midEntry g cs)) (m : Nat) =>
    attemptT_correct_source_peakCp h hcp hsrc B hB hH hkeep hlegal hsig
    hg hf' d hX ho hr hcs1 (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm)
    (hmem.trans hmem1.symm) hbnd hd1 m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨⟨m, hm⟩, hd1⟩ := hret vals cm hrun
    have := (hcp' hd1 m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨⟨m, hm⟩, hd1⟩ := htrap c hrun
    exact (hcp' hd1 m).2 htr hnmt c hm

end Link.SemanticCompilerWith

namespace Link.TypedCompilerWith

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128
open Link.SemanticCompilerWith
variable {lower : ProductionLowering}

/-- **`Link.TypedCompilerWith.attempt_correct_sourceCp` about the bundle's unoptimised program** (module doc): the theorem at
the compiled inputs `I1`, composed with `Link.midProgAt`; a return (trap) of `I0`'s source run from
`f`'s entry `cs` is the executable's return of the results split by `f`'s return groups (the same
trap). -/
theorem attempt_correct_sourceMidS {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) {I0 I1 : LinkInput}
    (hcp : S.funcs = I1.funcs.map FnInput.cp) (hsrc : SrcScopeB I1 = true)
    (hv : Opt.FunsSimMUAt (fun n => (input lower S cleanup).syms.lookup n)
      I0.srcProg.funcs I1.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S cleanup) B))
    (hH : HooksSim (input lower S cleanup) B) (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I1.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S cleanup)).funcs, ¬ Clif.IndFree g) →
      ∀ n, B.env.sigOf n = none)
    {n : String} {f g f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hg : I1.srcProg.func? n = some g)
    (hf' : (prog (input lower S cleanup)).func? n = some f')
    (hc : ¬ SemanticStackBound.CycleFrom
      (SemanticStackBound.Calls (input lower S cleanup) (input lower S cleanup).results) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) f'
      (SemanticStackBound.stackFn (input lower S cleanup) f') r args' cs'.mem)
    (hr : ClifRun (input lower S cleanup) B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I1.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecBytes.ExecRefinesT (art (input lower S cleanup) f').fb (art (input lower S cleanup) f').base
          (xreg 30 r) (step (input lower S cleanup) B file) r
          (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results)
          (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog (input lower S cleanup)) B.env M)
        (prog (input lower S cleanup)).bare cs') →
      Opt.Legal.NoMemTrap B.env I1.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecBytes.ExecRefinesT (art (input lower S cleanup) f').fb (art (input lower S cleanup) f').base
        (xreg 30 r) (step (input lower S cleanup) B file) r
        (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results)
        (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) M
  have hcp' := fun (m : Nat) => attempt_correct_sourceCp h hcp hsrc B hB hH hkeep hlegal hsig hg hf' hc
    hX ho hr hcs1 (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm) (hmem.trans hmem1.symm) hbnd m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨m, hm⟩ := hret vals cm hrun
    have := (hcp' m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨m, hm⟩ := htrap c hrun
    exact (hcp' m).2 htr hnmt c hm

/-- **`Link.TypedCompilerWith.attempt_correct_source_peakCp` about the bundle's unoptimised program** (module doc): the call-depth
bound `d` of `I0`'s source run from `cs` carried to `I1`'s run from `midEntry g cs` by
`Link.midProgAt_depth`. -/
theorem attempt_correct_source_peakMidS {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) {I0 I1 : LinkInput}
    (hcp : S.funcs = I1.funcs.map FnInput.cp) (hsrc : SrcScopeB I1 = true)
    (hv : Opt.FunsSimMUAt (fun n => (input lower S cleanup).syms.lookup n)
      I0.srcProg.funcs I1.srcProg.funcs)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S cleanup) B))
    (hH : HooksSim (input lower S cleanup) B) (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I1.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S cleanup)).funcs, ¬ Clif.IndFree g) →
      ∀ n, B.env.sigOf n = none)
    {n : String} {f g f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hg : I1.srcProg.func? n = some g)
    (hf' : (prog (input lower S cleanup)).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) f'
      (frameDrop (art (input lower S cleanup) f').af +
        ((input lower S cleanup).D * d + pbMax (input lower S cleanup))) r args' cs'.mem)
    (hr : ClifRun (input lower S cleanup) B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I1.srcProg (midEntry g cs) s' →
      Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env I0.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecBytes.ExecRefinesT (art (input lower S cleanup) f').fb (art (input lower S cleanup) f').base
          (xreg 30 r) (step (input lower S cleanup) B file) r
          (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results)
          (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog (input lower S cleanup)) B.env F d)
        (prog (input lower S cleanup)).bare cs') →
      Opt.Legal.NoMemTrap B.env I1.srcProg (midEntry g cs) → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecBytes.ExecRefinesT (art (input lower S cleanup) f').fb (art (input lower S cleanup) f').base
        (xreg 30 r) (step (input lower S cleanup) B file) r
        (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results)
        (.trapped c)) := by
  have hgs := (midProgAt_sim hv hf hg).sig
  obtain ⟨hcs1, hsl1, hmem1, hret, htrap⟩ := midProgAt_depth hv hkeep hf hg hcs
    (by rw [← hmem]; exact ho.symbols) hd M
  have hcp' := fun (hd1 : Clif.DepthLe B.env I1.srcProg d (midEntry g cs)) (m : Nat) =>
    attempt_correct_source_peakCp h hcp hsrc B hB hH hkeep hlegal hsig
    hg hf' d hX ho hr hcs1 (by rw [hgs]; exact hexp) (hsl.trans hsl1.symm)
    (hmem.trans hmem1.symm) hbnd hd1 m
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨⟨m, hm⟩, hd1⟩ := hret vals cm hrun
    have := (hcp' hd1 m).1 vals cm hm
    rw [hgs] at this
    exact this
  · obtain ⟨⟨m, hm⟩, hd1⟩ := htrap c hrun
    exact (hcp' hd1 m).2 htr hnmt c hm

end Link.TypedCompilerWith
