import FV.Link.Exe
import FV.Link.SemanticCompileWith
import FV.Link.ProductionImageWithProof
import FV.E2E.SemanticExecProven

/-! Closed correctness of the successful production executable attempt.
No program-specific premise beyond the original machine/source boundary remains. -/
set_option autoImplicit false
namespace Link.SemanticCompilerWith
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes Backend
variable {lower : ProductionLowering}

abbrev input (lower : ProductionLowering) (S : LinkSpec) (cleanup : Bool) : SemanticStackBound.CompilerInput :=
  {toLinkInput := S.inputProductionWith lower cleanup,cleanup,lower}

theorem attempt_spec {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) :
    SemanticStackBound.okB (input lower S cleanup) = true ∧
    leanLinkProductionWith lower S file0 cleanup = .ok file := by
  cases cleanup <;> simp [attempt] at h
  all_goals
    split at h
    · cases h
    · split at h
      · rename_i checked
        exact ⟨checked,h⟩
      · cases h


theorem codeMap_leanLink {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : leanLinkProductionWith lower S file0 cleanup = .ok file) :
    codeMapB (input lower S cleanup) (tabOf (input lower S cleanup).results) = true := by
  obtain ⟨_,_,_,_,_,_,_,hc,_⟩ := ProductionImageWithProof.spec h
  exact hc

theorem leanLink_gotSlot {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : leanLinkProductionWith lower S file0 cleanup = .ok file) (a : BitVec 64) : ¬ GotSlot (input lower S cleanup) file a := by
  rintro ⟨e, he, rl, hrl, ht, rd, G, hrd, -, -, -, h1, -⟩
  change e ∈ tabOf (ProductionImageWithProof.resultsFor lower S cleanup) at he
  obtain ⟨tp, -, hw⟩ := ProductionImageWithProof.words h
  obtain ⟨hv, -, himg⟩ := hw e he
  simp only [relocsOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hv
  obtain ⟨hnd, hall⟩ := hv
  have hok := hall rl hrl
  have hra := relocAt?_of_mem hnd hrl rfl
  obtain ⟨o, ty, sym, add⟩ := rl
  simp only at ht h1 hra
  subst ht
  simp only [relocOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨ho4, hon⟩, hok⟩ := hok
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.any_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨-, h1'⟩, -⟩, -⟩, ⟨r', hr', ⟨⟨ho', ht'⟩, -⟩, -⟩⟩, -⟩ := hok
  have hra' := relocAt?_of_mem hnd hr' ho'
  have hx1 := himg (o / 4 + 1) h1'
  rw [show 4 * (o / 4 + 1) = o + 4 by omega] at hx1
  simp only [resolveWord, show 4 * (o / 4 + 1) = o + 4 by omega, hra', ht', loOf,
    Nat.add_sub_cancel, hra] at hx1
  simp only [fileWord] at h1
  rw [hx1, Option.some.injEq] at h1
  exact addW_ne_ldrW (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (by omega) (by omega) (by omega) h1

/-- **`GotOk` of `leanLink`'s output** (no GOT slot). -/
theorem gotOk_leanLink {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : leanLinkProductionWith lower S file0 cleanup = .ok file) : GotOk (input lower S cleanup) file :=
  fun a ha => (leanLink_gotSlot h a ha).elim

/-- The outside caller avoids `leanLink`'s GOT slots (there is none). -/
theorem outsideAvoids_leanLink {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : leanLinkProductionWith lower S file0 cleanup = .ok file) (f : Clif.Function) (N : Nat) (r : Arm.ArmState)
    (args : List Clif.Val) (cm : Clif.Mem) : OutsideAvoids (GotSlot (input lower S cleanup) file) f N r args cm where
  stack a ha := (leanLink_gotSlot h a ha).elim
  args _ _ _ k _ hs := leanLink_gotSlot h _ hs
  valid _ _ _ _ _ hs := leanLink_gotSlot h _ hs

theorem attempt_correct {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) (B : BaseEnv) (hB : BaseOk (sys (input lower S cleanup) B))
    (hH : HooksSim (input lower S cleanup) B) {n : String} {f : Clif.Function} (hf : (prog (input lower S cleanup)).func? n = some f)
    (hc : ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls (input lower S cleanup) (input lower S cleanup).results) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) f (SemanticStackBound.stackFn (input lower S cleanup) f) r
      args cs.mem)
    (hr : ClifRun (input lower S cleanup) B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog (input lower S cleanup)) B.env M) (prog (input lower S cleanup)).bare cs) :
    ExecRefines (art (input lower S cleanup) f).fb (art (input lower S cleanup) f).base (xreg 30 r) (step (input lower S cleanup) B file) r
      (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results) (Clif.runLoop B.env (prog (input lower S cleanup)) (M + 1) cs) := by
  obtain ⟨hin, hl⟩ := attempt_spec h
  exact binary_correct_exec_proven hin
    (codeMap_leanLink hl) (ProductionImageWithProof.bin_ok hl) (gotOk_leanLink hl) B hB hH hf hc M hX ho
    (outsideAvoids_leanLink hl _ _ _ _ _) hr htr

/-- **The executable compiler is correct for recursive programs** (L1d): `attempt_correct`
without the call-graph premise `¬ CycleFrom`. The outside caller of `f` provides
`frameDrop (art (input lower S cleanup) f).af + ((input lower S cleanup).D * M + pbMax (input lower S cleanup))`
bytes of stack (#581: the deepest activation's stack probes write up to `pbMax` bytes below its
frame; `(input lower S cleanup).D`: the largest frame of
the program, `LinkSpec.input`), where `M + 1` bounds the whole-program CLIF run's steps; for that
run (returning, or trapping explicitly) the executable machine run of `file`'s own words refines
it (`ExecRefines`). The stack is proportional to the fuel `M`, not to the run's actual peak call
depth: an overestimate of what the code uses (docs/contracts/e2e.md, "Recursive programs"). -/
theorem attempt_correct_depth {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) (B : BaseEnv) (hB : BaseOk (sys (input lower S cleanup) B))
    (hH : HooksSim (input lower S cleanup) B) {n : String} {f : Clif.Function} (hf : (prog (input lower S cleanup)).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) f
      (frameDrop (art (input lower S cleanup) f).af +
        ((input lower S cleanup).D * M + pbMax (input lower S cleanup))) r args cs.mem)
    (hr : ClifRun (input lower S cleanup) B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog (input lower S cleanup)) B.env M) (prog (input lower S cleanup)).bare cs) :
    ExecRefines (art (input lower S cleanup) f).fb (art (input lower S cleanup) f).base (xreg 30 r) (step (input lower S cleanup) B file) r
      (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results) (Clif.runLoop B.env (prog (input lower S cleanup)) (M + 1) cs) := by
  obtain ⟨hin, hl⟩ := attempt_spec h
  exact binary_correct_exec_depth_proven hin
    (codeMap_leanLink hl) (ProductionImageWithProof.bin_ok hl) (gotOk_leanLink hl) B hB hH hf M hX ho
    (outsideAvoids_leanLink hl _ _ _ _ _) hr htr

/-- **The executable compiler is correct for recursive programs, with the stack of the run's peak
call depth** (L1d): `attempt_correct_depth` with
`frameDrop (art (input lower S cleanup) f).af + ((input lower S cleanup).D * d + pbMax (input lower S cleanup))`
(#581: the deepest activation's stack probes write up to `pbMax` bytes below its frame)
bytes of stack, where `d` bounds the call depth of the whole-program CLIF run (`Clif.DepthLe`:
every state the run from `cs` reaches has at most `d` callers, i.e. at most `d + 1` live
activations), independent of its length (at most `F + 1` steps). For that run (returning, or
trapping explicitly; `TrapsExplicit` under the environment whose program callees run with fuel
`F` and at most `d - 1` callers of their own, `Clif.linkEnvD`) the executable machine run of
`file`'s own words refines it (`ExecRefines`). Each level is charged the largest frame of the
program (`(input lower S cleanup).D`). -/
theorem attempt_correct_peak {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) (B : BaseEnv) (hB : BaseOk (sys (input lower S cleanup) B))
    (hH : HooksSim (input lower S cleanup) B) {n : String} {f : Clif.Function} (hf : (prog (input lower S cleanup)).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) f
      (frameDrop (art (input lower S cleanup) f).af +
        ((input lower S cleanup).D * d + pbMax (input lower S cleanup))) r args cs.mem)
    (hr : ClifRun (input lower S cleanup) B f r args cs)
    (hd : Clif.DepthLe B.env (prog (input lower S cleanup)) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog (input lower S cleanup)) B.env F d) (prog (input lower S cleanup)).bare cs) :
    ExecRefines (art (input lower S cleanup) f).fb (art (input lower S cleanup) f).base (xreg 30 r) (step (input lower S cleanup) B file) r
      (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results) (Clif.runLoop B.env (prog (input lower S cleanup)) (F + 1) cs) := by
  obtain ⟨hin, hl⟩ := attempt_spec h
  exact binary_correct_exec_peak_proven hin
    (codeMap_leanLink hl) (ProductionImageWithProof.bin_ok hl) (gotOk_leanLink hl) B hB hH hf F d hX ho
    (outsideAvoids_leanLink hl _ _ _ _ _) hr hd htr


end Link.SemanticCompilerWith
