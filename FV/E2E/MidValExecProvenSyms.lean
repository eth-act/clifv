import FV.E2E.MidValExecProven
import FV.Link.MidProgSyms

/-! # The binary check's theorems about the unoptimised program, hoisting mode (#1119)

`FV/E2E/MidValExecProven.lean`'s `_mid` theorems with the premise at the executable's symbol
table: the `_midS` theorem takes `hv : Opt.FunsSimMUAt (fun n => I.syms.lookup n) P0.funcs
(prog I).funcs` (the functions of `P0`, the unoptimised dumps, simulated by those compiled at
the symbol table of the image, the one the outside call premise fixes for `cs0`'s memory:
`OutsideCall.symbols`), through `Link.midProgAt` / `Link.midProgAt_depth`. `link-check` decides it
by `Link.midValidatedSymsB` on `I.syms` (`Link.midValidatedSymsB_sound`): the pairs `midPairB`
accepts, and those the hoisting mode accepts where the global values of the compared copy of the
unoptimised function resolve in the image (Cranelift's loop-invariant code motion hoists
`symbol_value` out of loops). Every `_mid` premise gives this one (`ValidatedC.funsSimMU`,
`FunsSimMU.at`); the `_mid` theorems are unchanged. Premises otherwise as the `_mid` theorems'.
-/

namespace E2E.ReturnPinExecBytes
open Backend Backend.Proof E2E.LinkCheck E2E.SemanticBinary E2E.BinCheck E2E.SemanticExecBytes
set_option autoImplicit false

/-- **`E2E.ReturnPinExecBytes.binary_correct_exec_proven` about the unoptimised program** (module doc): a return
of `P0`'s run from `f0`'s entry `cs0` is the executable's return of the same values and memory; a
trap (the compiled program's run from `midEntry f cs0` with its traps explicit) is the same trap. -/
theorem binary_correct_exec_proven_midS {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : ReturnPinStackBound.okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOkWithResults I I.results D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {P0 : Clif.Program} (hv : Opt.FunsSimMUAt (fun n => I.syms.lookup n) P0.funcs (prog I).funcs)
    (hkeep : Opt.EnvKeepsSymbols B.env) {n : String} {f0 f : Clif.Function}
    (hf0 : P0.func? n = some f0) (hf : (prog I).func? n = some f)
    (hc : ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls I I.results) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs0 : Clif.State} (hX : (imageOf file).Intact r)
    (hcs0 : ClifEntry f0 args cs0)
    (ho : OutsideCall I (BinCheck.roByte I D) f (SemanticStackBound.stackFn I f) r args cs0.mem)
    (hav : OutsideAvoids (GotSlot I file) f (SemanticStackBound.stackFn I f) r args cs0.mem)
    (hr : ClifRun I B f r args (midEntry f cs0)) :
    (∀ vals cm, Clif.runLoop B.env P0 M cs0 = .returned vals cm →
      ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
        (RelocAtWithResults I I.results) (.returned vals cm)) ∧
    ((∀ K, TrapsExplicit (Clif.linkEnvN (prog I) B.env K) (prog I).bare (midEntry f cs0)) → ∀ c,
      Clif.runLoop B.env P0 M cs0 = .trapped c →
      ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
        (RelocAtWithResults I I.results) (.trapped c)) := by
  obtain ⟨hcs1, -, hmem1, hret, htrap⟩ := Link.midProgAt hv hkeep hf0 hf hcs0 ho.symbols M
  have ho' : OutsideCall I (BinCheck.roByte I D) f (SemanticStackBound.stackFn I f) r args
      (midEntry f cs0).mem := by rw [hmem1]; exact ho
  have hav' : OutsideAvoids (GotSlot I file) f (SemanticStackBound.stackFn I f) r args
      (midEntry f cs0).mem := by rw [hmem1]; exact hav
  have hL := (ReturnPinBinary.okB_sound hI (baseOk_F hB) fun _ _ => trivial :
    (SemanticStackBound.ofInput I B fun _ => True).OkSemanticReturnPins)
  have hfm := (Clif.Program.func?_some hf).1
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (prog I) k (midEntry f cs0) = o) → o ≠ .outOfFuel →
      (∀ K, Clif.runLoop B.env (prog I) (K + 1) (midEntry f cs0) = o →
        TrapsExplicit (Clif.linkEnvN (prog I) B.env K) (prog I).bare (midEntry f cs0)) →
      ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
        (RelocAtWithResults I I.results) o := by
    rintro o ⟨k, hk⟩ hof htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ K =>
      have := binary_correct_exec_proven hI hcm hbin hgot B hB hH hf hc K hX ho' hav' hr (htr K hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr c hrun => ?_⟩
  · obtain ⟨m, hm⟩ := hret vals cm hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) fun K hK =>
      ReturnPinBinary.trapsExplicit_of_run hL hfm hcs1 (by rw [hmem1]; exact ho.symbols) hK
  · obtain ⟨m, hm⟩ := htrap c hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) fun K _ => htr K

/-- **`E2E.ReturnPinExecBytes.binary_correct_exec_peak_proven` about the unoptimised program** (module doc): the
stack for the call depth `d` of `P0`'s run (`Clif.DepthLe`); a return of `P0`'s run from `f0`'s
entry `cs0` is the executable's return of the same values and memory, a trap the same trap. -/
theorem binary_correct_exec_peak_proven_midS {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : ReturnPinStackBound.okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOkWithResults I I.results D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {P0 : Clif.Program} (hv : Opt.FunsSimMUAt (fun n => I.syms.lookup n) P0.funcs (prog I).funcs)
    (hkeep : Opt.EnvKeepsSymbols B.env) {n : String} {f0 f : Clif.Function}
    (hf0 : P0.func? n = some f0) (hf : (prog I).func? n = some f)
    (d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs0 : Clif.State}
    (hX : (imageOf file).Intact r) (hcs0 : ClifEntry f0 args cs0)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r args cs0.mem)
    (hav : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r args cs0.mem)
    (hr : ClifRun I B f r args (midEntry f cs0)) (hd : Clif.DepthLe B.env P0 d cs0) (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env P0 M cs0 = .returned vals cm →
      ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
        (RelocAtWithResults I I.results) (.returned vals cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare (midEntry f cs0)) →
      ∀ c, Clif.runLoop B.env P0 M cs0 = .trapped c →
      ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
        (RelocAtWithResults I I.results) (.trapped c)) := by
  obtain ⟨hcs1, -, hmem1, hret, htrap⟩ := Link.midProgAt_depth hv hkeep hf0 hf hcs0 ho.symbols hd M
  have ho' : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r args
      (midEntry f cs0).mem := by rw [hmem1]; exact ho
  have hav' : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r args
      (midEntry f cs0).mem := by rw [hmem1]; exact hav
  have hL := (ReturnPinBinary.okB_sound hI (baseOk_F hB) fun _ _ => trivial :
    (SemanticStackBound.ofInput I B fun _ => True).OkSemanticReturnPins)
  have hfm := (Clif.Program.func?_some hf).1
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (prog I) k (midEntry f cs0) = o) → o ≠ .outOfFuel →
      Clif.DepthLe B.env (prog I) d (midEntry f cs0) →
      (∀ F, Clif.runLoop B.env (prog I) (F + 1) (midEntry f cs0) = o →
        TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare (midEntry f cs0)) →
      ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
        (RelocAtWithResults I I.results) o := by
    rintro o ⟨k, hk⟩ hof hdT htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ F =>
      have := binary_correct_exec_peak_proven hI hcm hbin hgot B hB hH hf F d hX ho' hav' hr hdT
        (htr F hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr c hrun => ?_⟩
  · obtain ⟨⟨m, hm⟩, hdT⟩ := hret vals cm hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) hdT fun F hF =>
      ReturnPinBinary.trapsExplicit_of_runD hL hfm hcs1 (by rw [hmem1]; exact ho.symbols) hdT hF
  · obtain ⟨⟨m, hm⟩, hdT⟩ := htrap c hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) hdT fun F _ => htr F

end E2E.ReturnPinExecBytes

namespace E2E.SemanticExecBytes
open Backend Backend.Proof E2E.LinkCheck E2E.SemanticBinary E2E.BinCheck
set_option autoImplicit false

/-- **`E2E.SemanticExecBytes.binary_correct_exec_provenTS` about the unoptimised program** (module doc): a return
of `P0`'s run from `f0`'s entry `cs0` is the executable's return of the same values and memory; a
trap (the compiled program's run from `midEntry f cs0` with its traps explicit) is the same trap. -/
theorem binary_correct_exec_provenTS_midS {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : SemanticStackBound.okBTS I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOkWithResults I I.results D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {P0 : Clif.Program} (hv : Opt.FunsSimMUAt (fun n => I.syms.lookup n) P0.funcs (prog I).funcs)
    (hkeep : Opt.EnvKeepsSymbols B.env) {n : String} {f0 f : Clif.Function}
    (hf0 : P0.func? n = some f0) (hf : (prog I).func? n = some f)
    (hc : ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls I I.results) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs0 : Clif.State} (hX : (imageOf file).Intact r)
    (hcs0 : ClifEntry f0 args cs0)
    (ho : OutsideCall I (BinCheck.roByte I D) f (SemanticStackBound.stackFn I f) r args cs0.mem)
    (hav : OutsideAvoids (GotSlot I file) f (SemanticStackBound.stackFn I f) r args cs0.mem)
    (hr : ClifRun I B f r args (midEntry f cs0)) :
    (∀ vals cm, Clif.runLoop B.env P0 M cs0 = .returned vals cm →
      ExecBytes.ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
        (RelocAtWithResults I I.results) (.returned vals cm)) ∧
    ((∀ K, TrapsExplicit (Clif.linkEnvN (prog I) B.env K) (prog I).bare (midEntry f cs0)) → ∀ c,
      Clif.runLoop B.env P0 M cs0 = .trapped c →
      ExecBytes.ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
        (RelocAtWithResults I I.results) (.trapped c)) := by
  obtain ⟨hcs1, -, hmem1, hret, htrap⟩ := Link.midProgAt hv hkeep hf0 hf hcs0 ho.symbols M
  have ho' : OutsideCall I (BinCheck.roByte I D) f (SemanticStackBound.stackFn I f) r args
      (midEntry f cs0).mem := by rw [hmem1]; exact ho
  have hav' : OutsideAvoids (GotSlot I file) f (SemanticStackBound.stackFn I f) r args
      (midEntry f cs0).mem := by rw [hmem1]; exact hav
  have hL := (SemanticStackBound.okBTS_sound hI (baseOk_F hB) fun _ _ => trivial :
    (SemanticStackBound.ofInput I B fun _ => True).OkT)
  have hfm := (Clif.Program.func?_some hf).1
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (prog I) k (midEntry f cs0) = o) → o ≠ .outOfFuel →
      (∀ K, Clif.runLoop B.env (prog I) (K + 1) (midEntry f cs0) = o →
        TrapsExplicit (Clif.linkEnvN (prog I) B.env K) (prog I).bare (midEntry f cs0)) →
      ExecBytes.ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
        (RelocAtWithResults I I.results) o := by
    rintro o ⟨k, hk⟩ hof htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ K =>
      have := binary_correct_exec_provenTS hI hcm hbin hgot B hB hH hf hc K hX ho' hav' hr (htr K hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr c hrun => ?_⟩
  · obtain ⟨m, hm⟩ := hret vals cm hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) fun K hK =>
      E2E.SemanticBinary.trapsExplicit_of_runTS hL hfm hcs1 (by rw [hmem1]; exact ho.symbols) hK
  · obtain ⟨m, hm⟩ := htrap c hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) fun K _ => htr K

/-- **`E2E.SemanticExecBytes.binary_correct_exec_peak_provenTS` about the unoptimised program** (module doc): the
stack for the call depth `d` of `P0`'s run (`Clif.DepthLe`); a return of `P0`'s run from `f0`'s
entry `cs0` is the executable's return of the same values and memory, a trap the same trap. -/
theorem binary_correct_exec_peak_provenTS_midS {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : SemanticStackBound.okBTS I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOkWithResults I I.results D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {P0 : Clif.Program} (hv : Opt.FunsSimMUAt (fun n => I.syms.lookup n) P0.funcs (prog I).funcs)
    (hkeep : Opt.EnvKeepsSymbols B.env) {n : String} {f0 f : Clif.Function}
    (hf0 : P0.func? n = some f0) (hf : (prog I).func? n = some f)
    (d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs0 : Clif.State}
    (hX : (imageOf file).Intact r) (hcs0 : ClifEntry f0 args cs0)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r args cs0.mem)
    (hav : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r args cs0.mem)
    (hr : ClifRun I B f r args (midEntry f cs0)) (hd : Clif.DepthLe B.env P0 d cs0) (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env P0 M cs0 = .returned vals cm →
      ExecBytes.ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
        (RelocAtWithResults I I.results) (.returned vals cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare (midEntry f cs0)) →
      ∀ c, Clif.runLoop B.env P0 M cs0 = .trapped c →
      ExecBytes.ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
        (RelocAtWithResults I I.results) (.trapped c)) := by
  obtain ⟨hcs1, -, hmem1, hret, htrap⟩ := Link.midProgAt_depth hv hkeep hf0 hf hcs0 ho.symbols hd M
  have ho' : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r args
      (midEntry f cs0).mem := by rw [hmem1]; exact ho
  have hav' : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r args
      (midEntry f cs0).mem := by rw [hmem1]; exact hav
  have hL := (SemanticStackBound.okBTS_sound hI (baseOk_F hB) fun _ _ => trivial :
    (SemanticStackBound.ofInput I B fun _ => True).OkT)
  have hfm := (Clif.Program.func?_some hf).1
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (prog I) k (midEntry f cs0) = o) → o ≠ .outOfFuel →
      Clif.DepthLe B.env (prog I) d (midEntry f cs0) →
      (∀ F, Clif.runLoop B.env (prog I) (F + 1) (midEntry f cs0) = o →
        TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare (midEntry f cs0)) →
      ExecBytes.ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
        (RelocAtWithResults I I.results) o := by
    rintro o ⟨k, hk⟩ hof hdT htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ F =>
      have := binary_correct_exec_peak_provenTS hI hcm hbin hgot B hB hH hf F d hX ho' hav' hr hdT
        (htr F hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr c hrun => ?_⟩
  · obtain ⟨⟨m, hm⟩, hdT⟩ := hret vals cm hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) hdT fun F hF =>
      E2E.SemanticBinary.trapsExplicit_of_runDTS hL hfm hcs1 (by rw [hmem1]; exact ho.symbols) hdT hF
  · obtain ⟨⟨m, hm⟩, hdT⟩ := htrap c hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) hdT fun F _ => htr F

end E2E.SemanticExecBytes

namespace E2E.DeadCleanupExecBytes
open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck
set_option autoImplicit false

/-- **`E2E.DeadCleanupExecBytes.binary_correct_exec_provenT` about the unoptimised program** (module doc): a return
of `P0`'s run from `f0`'s entry `cs0` is the executable's return of the same values and memory; a
trap (the compiled program's run from `midEntry f cs0` with its traps explicit) is the same trap. -/
theorem binary_correct_exec_provenT_midS {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okBCleanupT I = true) (hcm : codeMapB I (tabOf I.resultsCleanup) = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {P0 : Clif.Program} (hv : Opt.FunsSimMUAt (fun n => I.syms.lookup n) P0.funcs (prog I).funcs)
    (hkeep : Opt.EnvKeepsSymbols B.env) {n : String} {f0 f : Clif.Function}
    (hf0 : P0.func? n = some f0) (hf : (prog I).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls I I.resultsCleanup) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs0 : Clif.State} (hX : (imageOf file).Intact r)
    (hcs0 : ClifEntry f0 args cs0)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs0.mem)
    (hav : OutsideAvoids (GotSlot I file) f (DeadCleanupStackBound.stackFn I f) r args cs0.mem)
    (hr : ClifRun I B f r args (midEntry f cs0)) :
    (∀ vals cm, Clif.runLoop B.env P0 M cs0 = .returned vals cm →
      ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
        (DeadCleanupBinCheck.RelocAt I) (.returned vals cm)) ∧
    ((∀ K, TrapsExplicit (Clif.linkEnvN (prog I) B.env K) (prog I).bare (midEntry f cs0)) → ∀ c,
      Clif.runLoop B.env P0 M cs0 = .trapped c →
      ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
        (DeadCleanupBinCheck.RelocAt I) (.trapped c)) := by
  obtain ⟨hcs1, -, hmem1, hret, htrap⟩ := Link.midProgAt hv hkeep hf0 hf hcs0 ho.symbols M
  have ho' : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args
      (midEntry f cs0).mem := by rw [hmem1]; exact ho
  have hav' : OutsideAvoids (GotSlot I file) f (DeadCleanupStackBound.stackFn I f) r args
      (midEntry f cs0).mem := by rw [hmem1]; exact hav
  have hL := (okBCleanup_soundT hI (baseOk_F hB) fun _ _ => trivial :
    (LinkSys.ofInputCleanup I B fun _ => True).OkT)
  have hfm := (Clif.Program.func?_some hf).1
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (prog I) k (midEntry f cs0) = o) → o ≠ .outOfFuel →
      (∀ K, Clif.runLoop B.env (prog I) (K + 1) (midEntry f cs0) = o →
        TrapsExplicit (Clif.linkEnvN (prog I) B.env K) (prog I).bare (midEntry f cs0)) →
      ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
        (DeadCleanupBinCheck.RelocAt I) o := by
    rintro o ⟨k, hk⟩ hof htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ K =>
      have := binary_correct_exec_provenT hI hcm hbin hgot B hB hH hf hc K hX ho' hav' hr (htr K hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr c hrun => ?_⟩
  · obtain ⟨m, hm⟩ := hret vals cm hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) fun K hK =>
      Link.DeadCleanup.trapsExplicit_of_runT hL hfm hcs1 (by rw [hmem1]; exact ho.symbols) hK
  · obtain ⟨m, hm⟩ := htrap c hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) fun K _ => htr K

/-- **`E2E.DeadCleanupExecBytes.binary_correct_exec_peak_provenT` about the unoptimised program** (module doc): the
stack for the call depth `d` of `P0`'s run (`Clif.DepthLe`); a return of `P0`'s run from `f0`'s
entry `cs0` is the executable's return of the same values and memory, a trap the same trap. -/
theorem binary_correct_exec_peak_provenT_midS {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okBCleanupT I = true) (hcm : codeMapB I (tabOf I.resultsCleanup) = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {P0 : Clif.Program} (hv : Opt.FunsSimMUAt (fun n => I.syms.lookup n) P0.funcs (prog I).funcs)
    (hkeep : Opt.EnvKeepsSymbols B.env) {n : String} {f0 f : Clif.Function}
    (hf0 : P0.func? n = some f0) (hf : (prog I).func? n = some f)
    (d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs0 : Clif.State}
    (hX : (imageOf file).Intact r) (hcs0 : ClifEntry f0 args cs0)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r args cs0.mem)
    (hav : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r args cs0.mem)
    (hr : ClifRun I B f r args (midEntry f cs0)) (hd : Clif.DepthLe B.env P0 d cs0) (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env P0 M cs0 = .returned vals cm →
      ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
        (DeadCleanupBinCheck.RelocAt I) (.returned vals cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare (midEntry f cs0)) →
      ∀ c, Clif.runLoop B.env P0 M cs0 = .trapped c →
      ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
        (DeadCleanupBinCheck.RelocAt I) (.trapped c)) := by
  obtain ⟨hcs1, -, hmem1, hret, htrap⟩ := Link.midProgAt_depth hv hkeep hf0 hf hcs0 ho.symbols hd M
  have ho' : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r args
      (midEntry f cs0).mem := by rw [hmem1]; exact ho
  have hav' : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r args
      (midEntry f cs0).mem := by rw [hmem1]; exact hav
  have hL := (okBCleanup_soundT hI (baseOk_F hB) fun _ _ => trivial :
    (LinkSys.ofInputCleanup I B fun _ => True).OkT)
  have hfm := (Clif.Program.func?_some hf).1
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (prog I) k (midEntry f cs0) = o) → o ≠ .outOfFuel →
      Clif.DepthLe B.env (prog I) d (midEntry f cs0) →
      (∀ F, Clif.runLoop B.env (prog I) (F + 1) (midEntry f cs0) = o →
        TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare (midEntry f cs0)) →
      ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
        (DeadCleanupBinCheck.RelocAt I) o := by
    rintro o ⟨k, hk⟩ hof hdT htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ F =>
      have := binary_correct_exec_peak_provenT hI hcm hbin hgot B hB hH hf F d hX ho' hav' hr hdT
        (htr F hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr c hrun => ?_⟩
  · obtain ⟨⟨m, hm⟩, hdT⟩ := hret vals cm hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) hdT fun F hF =>
      Link.DeadCleanup.trapsExplicit_of_runDT hL hfm hcs1 (by rw [hmem1]; exact ho.symbols) hdT hF
  · obtain ⟨⟨m, hm⟩, hdT⟩ := htrap c hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) hdT fun F _ => htr F

end E2E.DeadCleanupExecBytes
