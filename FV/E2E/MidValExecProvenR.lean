import FV.E2E.MidValExecProvenSyms
import FV.E2E.SemanticExecTSR

/-! # The typed Stock binary check's theorems about the unoptimised program, register-guarded calls (#753)

`FV/E2E/MidValExecProven.lean`'s and `FV/E2E/MidValExecProvenSyms.lean`'s `_mid` and `_midS`
theorems of the typed Stock checker for the checks with the register-guarded calls `okBTSR`
(`binary_correct_exec{,_peak}_provenTSR`, `trapsExplicit_of_run{,D}TSR`): `link-check`'s typed
Stock mode decides `okBTSR` since #753 (`FVTest/E2E/BinVerdict.lean`). Statements as the `TS`
theorems' with `okBTSR` for `okBTS`.
-/

namespace E2E.SemanticExecBytes
open Backend Backend.Proof E2E.LinkCheck E2E.SemanticBinary E2E.BinCheck
set_option autoImplicit false

/-- **`E2E.SemanticExecBytes.binary_correct_exec_provenTSR` about the unoptimised program** (module doc): a return
of `P0`'s run from `f0`'s entry `cs0` is the executable's return of the same values and memory; a
trap (the compiled program's run from `midEntry f cs0` with its traps explicit) is the same trap. -/
theorem binary_correct_exec_provenTSR_mid {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : SemanticStackBound.okBTSR I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOkWithResults I I.results D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {P0 : Clif.Program} (hv : Opt.MidVal.ValidatedC P0.funcs (prog I).funcs)
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
  obtain ⟨hcs1, -, hmem1, hret, htrap⟩ := Link.midProg hv hkeep hf0 hf hcs0 M
  have ho' : OutsideCall I (BinCheck.roByte I D) f (SemanticStackBound.stackFn I f) r args
      (midEntry f cs0).mem := by rw [hmem1]; exact ho
  have hav' : OutsideAvoids (GotSlot I file) f (SemanticStackBound.stackFn I f) r args
      (midEntry f cs0).mem := by rw [hmem1]; exact hav
  have hL := (SemanticStackBound.okBTS_soundR hI (baseOk_F hB) fun _ _ => trivial :
    (SemanticStackBound.ofInput I B fun _ => True).OkTR)
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
      have := binary_correct_exec_provenTSR hI hcm hbin hgot B hB hH hf hc K hX ho' hav' hr (htr K hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr c hrun => ?_⟩
  · obtain ⟨m, hm⟩ := hret vals cm hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) fun K hK =>
      E2E.SemanticBinary.trapsExplicit_of_runTSR hL hfm hcs1 (by rw [hmem1]; exact ho.symbols) hK
  · obtain ⟨m, hm⟩ := htrap c hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) fun K _ => htr K

/-- **`E2E.SemanticExecBytes.binary_correct_exec_peak_provenTSR` about the unoptimised program** (module doc): the
stack for the call depth `d` of `P0`'s run (`Clif.DepthLe`); a return of `P0`'s run from `f0`'s
entry `cs0` is the executable's return of the same values and memory, a trap the same trap. -/
theorem binary_correct_exec_peak_provenTSR_mid {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : SemanticStackBound.okBTSR I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOkWithResults I I.results D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {P0 : Clif.Program} (hv : Opt.MidVal.ValidatedC P0.funcs (prog I).funcs)
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
  obtain ⟨hcs1, -, hmem1, hret, htrap⟩ := Link.midProg_depth hv hkeep hf0 hf hcs0 hd M
  have ho' : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r args
      (midEntry f cs0).mem := by rw [hmem1]; exact ho
  have hav' : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r args
      (midEntry f cs0).mem := by rw [hmem1]; exact hav
  have hL := (SemanticStackBound.okBTS_soundR hI (baseOk_F hB) fun _ _ => trivial :
    (SemanticStackBound.ofInput I B fun _ => True).OkTR)
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
      have := binary_correct_exec_peak_provenTSR hI hcm hbin hgot B hB hH hf F d hX ho' hav' hr hdT
        (htr F hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr c hrun => ?_⟩
  · obtain ⟨⟨m, hm⟩, hdT⟩ := hret vals cm hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) hdT fun F hF =>
      E2E.SemanticBinary.trapsExplicit_of_runDTSR hL hfm hcs1 (by rw [hmem1]; exact ho.symbols) hdT hF
  · obtain ⟨⟨m, hm⟩, hdT⟩ := htrap c hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) hdT fun F _ => htr F

/-- **`E2E.SemanticExecBytes.binary_correct_exec_provenTSR` about the unoptimised program** (module doc): a return
of `P0`'s run from `f0`'s entry `cs0` is the executable's return of the same values and memory; a
trap (the compiled program's run from `midEntry f cs0` with its traps explicit) is the same trap. -/
theorem binary_correct_exec_provenTSR_midS {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : SemanticStackBound.okBTSR I = true) (hcm : codeMapB I (tabOf I.results) = true)
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
  have hL := (SemanticStackBound.okBTS_soundR hI (baseOk_F hB) fun _ _ => trivial :
    (SemanticStackBound.ofInput I B fun _ => True).OkTR)
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
      have := binary_correct_exec_provenTSR hI hcm hbin hgot B hB hH hf hc K hX ho' hav' hr (htr K hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr c hrun => ?_⟩
  · obtain ⟨m, hm⟩ := hret vals cm hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) fun K hK =>
      E2E.SemanticBinary.trapsExplicit_of_runTSR hL hfm hcs1 (by rw [hmem1]; exact ho.symbols) hK
  · obtain ⟨m, hm⟩ := htrap c hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) fun K _ => htr K

/-- **`E2E.SemanticExecBytes.binary_correct_exec_peak_provenTSR` about the unoptimised program** (module doc): the
stack for the call depth `d` of `P0`'s run (`Clif.DepthLe`); a return of `P0`'s run from `f0`'s
entry `cs0` is the executable's return of the same values and memory, a trap the same trap. -/
theorem binary_correct_exec_peak_provenTSR_midS {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : SemanticStackBound.okBTSR I = true) (hcm : codeMapB I (tabOf I.results) = true)
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
  have hL := (SemanticStackBound.okBTS_soundR hI (baseOk_F hB) fun _ _ => trivial :
    (SemanticStackBound.ofInput I B fun _ => True).OkTR)
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
      have := binary_correct_exec_peak_provenTSR hI hcm hbin hgot B hB hH hf F d hX ho' hav' hr hdT
        (htr F hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr c hrun => ?_⟩
  · obtain ⟨⟨m, hm⟩, hdT⟩ := hret vals cm hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) hdT fun F hF =>
      E2E.SemanticBinary.trapsExplicit_of_runDTSR hL hfm hcs1 (by rw [hmem1]; exact ho.symbols) hdT hF
  · obtain ⟨⟨m, hm⟩, hdT⟩ := htrap c hrun
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) hdT fun F _ => htr F

end E2E.SemanticExecBytes
