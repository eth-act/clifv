import FV.Link.Correct
import FV.Link.Compile
import FV.E2E.ExecProven

/-! # The executable compiler is correct (L1, docs/TO-PROVE.md §1)

`compileExe S file0` (`FV/Link/Compile.lean`): the input conditions `InScopeP`, then the Lean
linker `leanLink`.

**`compileExe_correct`**: for `compileExe S file0 = .ok file`, the executable machine run of
`file`'s own words refines the CLIF run of the program (`binary_correct_exec_proven`) — no
per-program check, certificate or `native_decide` left: `okB` of the placed input (whose results
are the compiler's, `LinkSpec.input_results`) is `okT_of_inScope` with the linker's facts
`leanLink_linkerOk`; `BinOk` is `binOk_leanLink`; `codeMapB` is `leanLink`'s check; the GOT has
no slot (`leanLink_gotSlot`: `leanLink` resolves every GOT pair to `adrp`+`add`, so `GotOk` and
`OutsideAvoids` of the slots hold vacuously). Premises left:

* `LowerDefinedHyp` (definite assignment of `lowerFunction`'s VCode; open, program-independent);
* the outside code's contracts: `BaseOk`, `HooksSim`, the boundary contract `OutsideCall` and the
  choice of the reference CLIF run `ClifRun`, `TrapsExplicit` of that run;
* no call cycle reachable from the entered function (`CycleFrom`, a property of the CLIF
  program: the stack bound of a non-recursive call graph).
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
theorem okB_leanLink (hD : SpillDefinedHyp) {S : LinkSpec} {file0 file : ByteArray}
    (hin : InScopeP S.input = true) (h : leanLink S file0 = .ok file) : okB S.input = true := by
  have := okT_of_inScope hD hin (leanLink_linkerOk h)
  rw [S.input_withDepth] at this
  rw [okB_fallback rfl]
  exact this

/-- **The code map of `leanLink`'s output** (`leanLink`'s check `codeMapB`). -/
theorem codeMap_leanLink {S : LinkSpec} {file0 file : ByteArray}
    (h : leanLink S file0 = .ok file) : codeMapB S.input (tabOf S.input.results) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hcm, -⟩ := leanLink_spec h
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
  · exact ⟨by rw [S.inScope_input]; assumption, h⟩
  · cases h

/-- **The executable compiler is correct** (L1): for `compileExe S file0 = .ok file` and an
outside call of a function `f` of the program (no call cycle reachable from it), the executable
machine run of `file`'s own words from the machine state `r` refines the whole-program CLIF run
(`ExecRefines`). The program `prog S.input` is the input's CLIF functions
(`progOf_resultsT`); every per-program fact is proven (`okB_leanLink`, `binOk_leanLink`,
`codeMap_leanLink`, `gotOk_leanLink`, `outsideAvoids_leanLink`). -/
theorem compileExe_correct (hM : LowerDefinedHyp) {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.input B))
    (hH : HooksSim S.input B) {n : String} {f : Clif.Function} (hf : (prog S.input).func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.input S.input.results) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) f (StackBound.stackFn S.input f) r
      args cs.mem)
    (hr : ClifRun S.input B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog S.input) B.env M) ((prog S.input).only f) cs) :
    ExecRefines (art S.input f).fb (art S.input f).base (xreg 30 r) (step S.input B file) r
      (RelocAt S.input) (Clif.runLoop B.env (prog S.input) (M + 1) cs) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact binary_correct_exec_proven (okB_leanLink (spillDefinedHyp_of_lower hM) hin hl)
    (codeMap_leanLink hl) (binOk_leanLink hl) (gotOk_leanLink hl) B hB hH hf hc M hX ho
    (outsideAvoids_leanLink hl _ _ _ _ _) hr htr

end Link
