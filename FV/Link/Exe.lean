import FV.Link.Correct
import FV.Link.Compile
import FV.E2E.ExecProven
import FV.E2E.LinkScopeInput

/-! # The executable compiler is correct (L1, docs/TO-PROVE.md §1)

`compileExe S file0` (`FV/Link/Compile.lean`): the input conditions `InScopeIn`, then the Lean
linker `leanLink`. The proofs below use `InScopeP`, which `InScopeIn` implies
(`inScopeP_of_input`; `compileExe_spec`).

**`compileExe_correct`**: for `compileExe S file0 = .ok file`, the executable machine run of
`file`'s own words refines the CLIF run of the program (`binary_correct_exec_proven`) — no
per-program check, certificate or `native_decide` left: `okB` of the placed input (whose results
are the compiler's, `LinkSpec.input_results`) is `okT_of_inScope` with the linker's facts
`leanLink_linkerOk`; `BinOk` is `binOk_leanLink`; `codeMapB` is `leanLink`'s check; the GOT has
no slot (`leanLink_gotSlot`: `leanLink` resolves every GOT pair to `adrp`+`add`, so `GotOk` and
`OutsideAvoids` of the slots hold vacuously); definite assignment is proven
(`E2E.spillDefinedHyp`). Premises left:

* the outside code's contracts: `BaseOk`, `HooksSim`, the boundary contract `OutsideCall` and the
  choice of the reference CLIF run `ClifRun`, `TrapsExplicit` of that run;
* no call cycle reachable from the entered function (`CycleFrom`, a property of the CLIF
  program: the stack bound of a non-recursive call graph).

**`compileExe_correct_depth`** (L1d): the same for recursive programs — no call-graph premise; the
outside caller provides `frameDrop + (D * M + pbMax)` bytes of stack for the CLIF run's fuel `M`
(`binary_correct_exec_depth_proven`) instead of the static stack bound `stackFn`.

**`compileExe_correct_peak`** (L1d): the same with `frameDrop + (D * d + pbMax)` bytes of stack for the CLIF
run's peak call depth `d` (`Clif.DepthLe`: no state of the run has more than `d` callers),
whatever its length (`binary_correct_exec_peak_proven`).
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.Binary E2E.ExecBytes Backend LinkSpec

/-- The placed input's stack depth is its results' (`withDepth` is the identity on it). -/
theorem LinkSpec.input_withDepth (S : LinkSpec) : S.input.withDepth S.input.resultsT = S.input :=
  rfl

/-- `InScopeP` reads the program and the CLIF image's symbols, not the depth. -/
theorem LinkSpec.inScope_input (S : LinkSpec) : InScopeP S.input = InScopeP S.input0 := rfl

/-- **`okB` of `leanLink`'s input** (the compiler's results), no check: `okT_of_inScope` with
the linker's facts by construction. -/
theorem okB_leanLink {S : LinkSpec} {file0 file : ByteArray}
    (hin : InScopeP S.input = true) (h : leanLink S file0 = .ok file) : okB S.input = true := by
  have := okT_of_inScope spillDefinedHyp hin (leanLink_linkerOk h)
  rw [S.input_withDepth] at this
  rw [okB_fallback rfl]
  exact this

/-- **The code map of `leanLink`'s output** (`leanLink`'s check `codeMapB`). -/
theorem codeMap_leanLink {S : LinkSpec} {file0 file : ByteArray}
    (h : leanLink S file0 = .ok file) : codeMapB S.input (tabOf S.input.results) = true := by
  obtain ⟨-, -, -, -, -, -, -, hcm, -⟩ := leanLink_spec h
  rw [S.input_results]
  exact hcm

/-- `add` and `ldr` (unsigned offset) encodings differ. -/
theorem addW_ne_ldrW {rd rn imm rt rn' imm' : Nat} (h1 : rd < 32) (h2 : rn < 32) (h3 : imm < 4096)
    (h4 : rt < 32) (h5 : rn' < 32) (h6 : imm' < 4096) : addW rd rn imm ≠ ldrW rt rn' imm' := by
  intro h
  have := congrArg BitVec.toNat h
  simp only [addW, ldrW, BitVec.toNat_ofNat] at this
  omega

/-- **`leanLink`'s output has no GOT slot**: the second word of every GOT pair is `add`
(`resolveWord` resolves `ADR_GOT_PAGE`+`LD64_GOT_LO12_NC` directly), never the slot's `ldr`. -/
theorem leanLink_gotSlot {S : LinkSpec} {file0 file : ByteArray}
    (h : leanLink S file0 = .ok file) (a : BitVec 64) : ¬ GotSlot S.input file a := by
  rintro ⟨e, he, rl, hrl, ht, rd, G, hrd, -, -, -, h1, -⟩
  rw [S.input_results] at he
  obtain ⟨tp, -, hw⟩ := leanLink_words h
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
theorem gotOk_leanLink {S : LinkSpec} {file0 file : ByteArray}
    (h : leanLink S file0 = .ok file) : GotOk S.input file :=
  fun a ha => (leanLink_gotSlot h a ha).elim

/-- The outside caller avoids `leanLink`'s GOT slots (there is none). -/
theorem outsideAvoids_leanLink {S : LinkSpec} {file0 file : ByteArray}
    (h : leanLink S file0 = .ok file) (f : Clif.Function) (N : Nat) (r : Arm.ArmState)
    (args : List Clif.Val) (cm : Clif.Mem) : OutsideAvoids (GotSlot S.input file) f N r args cm where
  stack a ha := (leanLink_gotSlot h a ha).elim
  args _ _ _ k _ hs := leanLink_gotSlot h _ hs
  valid _ _ _ _ _ hs := leanLink_gotSlot h _ hs

/-- `compileExe`'s success: the input conditions hold and `leanLink` succeeds. -/
theorem compileExe_spec {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) : InScopeP S.input = true ∧ leanLink S file0 = .ok file := by
  unfold compileExe at h
  split at h
  · rename_i hs
    exact ⟨by rw [S.inScope_input]; exact inScopeP_of_input (by rw [← inScopeInPar_eq]; exact hs),
      h⟩
  · cases h

/-- **The executable compiler is correct** (L1): for `compileExe S file0 = .ok file` and an
outside call of a function `f` of the program (no call cycle reachable from it), the executable
machine run of `file`'s own words from the machine state `r` refines the whole-program CLIF run
(`ExecRefines`). The program `prog S.input` is the input's CLIF functions
(`progOf_resultsT`); every per-program fact is proven (`okB_leanLink`, `binOk_leanLink`,
`codeMap_leanLink`, `gotOk_leanLink`, `outsideAvoids_leanLink`), no open hypothesis about the
compiler. -/
theorem compileExe_correct {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.input B))
    (hH : HooksSim S.input B) {n : String} {f : Clif.Function} (hf : (prog S.input).func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.input S.input.results) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) f (StackBound.stackFn S.input f) r
      args cs.mem)
    (hr : ClifRun S.input B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog S.input) B.env M) (prog S.input).bare cs) :
    ExecRefines (art S.input f).fb (art S.input f).base (xreg 30 r) (step S.input B file) r
      (RelocAt S.input) (Clif.runLoop B.env (prog S.input) (M + 1) cs) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact binary_correct_exec_proven (okB_leanLink hin hl)
    (codeMap_leanLink hl) (binOk_leanLink hl) (gotOk_leanLink hl) B hB hH hf hc M hX ho
    (outsideAvoids_leanLink hl _ _ _ _ _) hr htr

/-- **The executable compiler is correct for recursive programs** (L1d): `compileExe_correct`
without the call-graph premise `¬ CycleFrom`. The outside caller of `f` provides
`frameDrop (art S.input f).af + (S.input.D * M + pbMax S.input)` bytes of stack (`S.input.D`: the
largest frame of the program, `LinkSpec.input`; `pbMax S.input`, #581: the most bytes a function's
stack probes write below its frame, `0` without probes, so the former `D * M` is too small for a
program with probes), where `M + 1` bounds the whole-program CLIF run's steps; for that
run (returning, or trapping explicitly) the executable machine run of `file`'s own words refines
it (`ExecRefines`). The stack is proportional to the fuel `M`, not to the run's actual peak call
depth: an overestimate of what the code uses (docs/contracts/e2e.md, "Recursive programs"). -/
theorem compileExe_correct_depth {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.input B))
    (hH : HooksSim S.input B) {n : String} {f : Clif.Function} (hf : (prog S.input).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) f
      (frameDrop (art S.input f).af + (S.input.D * M + pbMax S.input)) r args cs.mem)
    (hr : ClifRun S.input B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog S.input) B.env M) (prog S.input).bare cs) :
    ExecRefines (art S.input f).fb (art S.input f).base (xreg 30 r) (step S.input B file) r
      (RelocAt S.input) (Clif.runLoop B.env (prog S.input) (M + 1) cs) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact binary_correct_exec_depth_proven (okB_leanLink hin hl)
    (codeMap_leanLink hl) (binOk_leanLink hl) (gotOk_leanLink hl) B hB hH hf M hX ho
    (outsideAvoids_leanLink hl _ _ _ _ _) hr htr

/-- **The executable compiler is correct for recursive programs, with the stack of the run's peak
call depth** (L1d): `compileExe_correct_depth` with
`frameDrop (art S.input f).af + (S.input.D * d + pbMax S.input)` (#581: `pbMax`, the stack probes
of the deepest activation)
bytes of stack, where `d` bounds the call depth of the whole-program CLIF run (`Clif.DepthLe`:
every state the run from `cs` reaches has at most `d` callers, i.e. at most `d + 1` live
activations), independent of its length (at most `F + 1` steps). For that run (returning, or
trapping explicitly; `TrapsExplicit` under the environment whose program callees run with fuel
`F` and at most `d - 1` callers of their own, `Clif.linkEnvD`) the executable machine run of
`file`'s own words refines it (`ExecRefines`). Each level is charged the largest frame of the
program (`S.input.D`). -/
theorem compileExe_correct_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.input B))
    (hH : HooksSim S.input B) {n : String} {f : Clif.Function} (hf : (prog S.input).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) f
      (frameDrop (art S.input f).af + (S.input.D * d + pbMax S.input)) r args cs.mem)
    (hr : ClifRun S.input B f r args cs)
    (hd : Clif.DepthLe B.env (prog S.input) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog S.input) B.env F d) (prog S.input).bare cs) :
    ExecRefines (art S.input f).fb (art S.input f).base (xreg 30 r) (step S.input B file) r
      (RelocAt S.input) (Clif.runLoop B.env (prog S.input) (F + 1) cs) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact binary_correct_exec_peak_proven (okB_leanLink hin hl)
    (codeMap_leanLink hl) (binOk_leanLink hl) (gotOk_leanLink hl) B hB hH hf F d hX ho
    (outsideAvoids_leanLink hl _ _ _ _ _) hr hd htr

end Link
