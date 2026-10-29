import FV.Link.ExeUCompile
import FV.Link.DeadCleanupExeSource
import FV.E2E.DeadCleanupExecTrap

/-! # The shipped executable compiler with callee traps (S9d, #377)

`Link.DeadCleanup.compileExe_correct{,_peak}` and `compileExe_correct_source{,_peak}` take the
run premise `TrapsExplicit`: every trap of the run is an explicit trap of the entered function,
so a run that traps inside a callee (a function of the program, a panic or a `__*ti3` helper
dividing by zero outside it) is excluded. Here the same executables, `compileExeU S file0 = .ok
file` (`compileExe` with the unwind tables checked, what `lake exe lean-link` decides), with
the run premise `TrapsD` (no memory-access trap; traps of callees allowed) and the executable's
trap observable `TrapAtE` (`ExecRefinesC`): a trap site of any compiled function, or a call of a
compiled function whose callee outside the program traps.

* `compileExe_correct_trap` (entries without a reachable call cycle), `compileExe_correct_trap_peak`
  (the run's peak call depth): `ExecRefinesC` of the whole-program run, every outcome;
* `compileExe_correct_source_trap{,_peak}`: the original (pre-`i128`-legalisation) program's
  trap; the legaliser's `__*ti3` helpers are base externs, their traps covered by the outside
  code's trap contract `BaseTrapsOk`.

The premises beyond the old theorems': `BaseTrapsOk` (the outside code does not return where its
CLIF semantics traps), no `try_call` terminator in the program (S9b, #375), and `TrapsD` in
place of `TrapsExplicit`. `lowerCheckU` of every function is `compileExeU`'s (`lowerU_of`).
-/

namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend Backend.Proof.Driver LinkSpec Opt.Legalize128

/-- **`compileExeU` decides the lowering's unwinding validator** for every compiled function. -/
theorem lowerU_of {S : LinkSpec} {file0 file : ByteArray} (h : compileExeU S file0 = .ok file) :
    ∀ g ∈ (prog S.inputCleanup).funcs, lowerCheckU g (art S.inputCleanup g).vc = true := by
  obtain ⟨hc, hu⟩ := compileExeU_spec h
  obtain ⟨hin, hl⟩ := compileExe_spec hc
  have hI := okB_leanLink hin hl
  simp only [unwOkB, Bool.and_eq_true, parResultsCleanupT_input] at hu
  intro g hg
  simp [lowerCheckU, (factsCleanup hI hg).lowerOk, (EhCheck.unwFnsB_sound hu.2 hg).1]

/-- **The shipped executable compiler is correct with callee traps** (entries without a reachable
call cycle): for `compileExeU S file0 = .ok file`, an outside call of a function `f` of the
program (no `try_call` terminator in the program, the outside code's trap contract
`BaseTrapsOk`), the executable machine run of `file`'s own words from `r` refines the
whole-program CLIF run under the run premise `TrapsD` (`ExecRefinesC`): a return as
`compileExe_correct`; a trap with `c` (of `f`, of a function of the program it calls, or of a
callee outside the program) is an executable state at a trap site with `c` of a compiled function
or at a call whose callee outside the program traps with `c`. -/
theorem compileExe_correct_trap {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeU S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
    (hH : HooksSim S.inputCleanup B) (hBT : (sys S.inputCleanup B).BaseTrapsOk)
    (hnoTry : ∀ g ∈ (prog S.inputCleanup).funcs, ∀ b ∈ g.blocks, b.term.isTry = false)
    {n : String} {f : Clif.Function} (hf : (prog S.inputCleanup).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f
      (DeadCleanupStackBound.stackFn S.inputCleanup f) r args cs.mem)
    (hr : ClifRun S.inputCleanup B f r args cs)
    (htr : (sys S.inputCleanup B).std.TrapsD M f cs) :
    ExecRefinesC S.inputCleanup B (xreg 30 r) (step S.inputCleanup B file) r
      (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (Clif.runLoop B.env (prog S.inputCleanup) (M + 1) cs) := by
  obtain ⟨he, -⟩ := compileExeU_spec h
  obtain ⟨hin, hl⟩ := compileExe_spec he
  have hok := okB_leanLink hin hl
  have hL : (LinkSys.ofInputCleanup S.inputCleanup B fun _ => True).Ok :=
    okBCleanup_sound hok (baseOk_F hB) fun _ _ => trivial
  have hfm := (Clif.Program.func?_some hf).1
  cases hrun : Clif.runLoop B.env (prog S.inputCleanup) (M + 1) cs with
  | returned vals cm =>
    have := compileExe_correct he B hB hH hf hc M hX ho hr
      (trapsExplicit_of_run hL hfm hr.entry ho.symbols hrun)
    rw [hrun] at this
    exact ExecRefines.toC hfm this
  | trapped tc =>
    exact binary_correct_exec_trap hok (codeMap_leanLink hl) (binOk_leanLink hl)
      (leanLink_gotSlot hl) B hB hH (lowerU_of h) hnoTry hBT hf hc M hX ho hr htr hrun
  | stuck _ => trivial
  | outOfFuel => trivial

/-- **The shipped executable compiler is correct with callee traps, recursive programs included**
(`compileExe_correct_trap` for the run's peak call depth `d`, as `compileExe_correct_peak`): the
outside caller provides `frameDrop + (D * d + pbMax)` bytes of stack (#581), the run premise `TrapsD` is of the
callees running with fuel `F` and at most `d - 1` callers of their own (`LinkSys.peak`). -/
theorem compileExe_correct_trap_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeU S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
    (hH : HooksSim S.inputCleanup B) (hBT : (sys S.inputCleanup B).BaseTrapsOk)
    (hnoTry : ∀ g ∈ (prog S.inputCleanup).funcs, ∀ b ∈ g.blocks, b.term.isTry = false)
    {n : String} {f : Clif.Function} (hf : (prog S.inputCleanup).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f
      (frameDrop (art S.inputCleanup f).af + (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args
      cs.mem)
    (hr : ClifRun S.inputCleanup B f r args cs)
    (hd : Clif.DepthLe B.env (prog S.inputCleanup) d cs)
    (htr : ((sys S.inputCleanup B).peak F).TrapsD d f cs) :
    ExecRefinesC S.inputCleanup B (xreg 30 r) (step S.inputCleanup B file) r
      (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (Clif.runLoop B.env (prog S.inputCleanup) (F + 1) cs) := by
  obtain ⟨he, -⟩ := compileExeU_spec h
  obtain ⟨hin, hl⟩ := compileExe_spec he
  have hok := okB_leanLink hin hl
  have hL : (LinkSys.ofInputCleanup S.inputCleanup B fun _ => True).Ok :=
    okBCleanup_sound hok (baseOk_F hB) fun _ _ => trivial
  have hfm := (Clif.Program.func?_some hf).1
  cases hrun : Clif.runLoop B.env (prog S.inputCleanup) (F + 1) cs with
  | returned vals cm =>
    have := compileExe_correct_peak he B hB hH hf F d hX ho hr hd
      (E2E.Binary.trapsExplicit_of_runD hL hfm hr.entry ho.symbols hd hrun)
    rw [hrun] at this
    exact ExecRefines.toC hfm this
  | trapped tc =>
    exact binary_correct_exec_trap_peak hok (codeMap_leanLink hl) (binOk_leanLink hl)
      (leanLink_gotSlot hl) B hB hH (lowerU_of h) hnoTry hBT hf F d hX ho hr hd htr hrun
  | stuck _ => trivial
  | outOfFuel => trivial

/-- **The shipped executable compiler refines the original source program, callee traps
included** (`compileExe_correct_source` with `compileExe_correct_trap`): a return as there; a
trap of the source run (without load/store traps; the target runs under the run premise `TrapsD`
at every fuel) is an executable state at a trap with the same code (`ExecRefinesC`). The
legaliser's `__*ti3` helpers are base externs: a helper's trap (an `i128` division by zero) is
covered by `BaseTrapsOk`. -/
theorem compileExe_correct_source_trap {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeU S file0 = .ok file) (hsrc : SrcScopeB S.inputCleanup = true)
    (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hBT : (sys S.inputCleanup B).BaseTrapsOk)
    (hnoTry : ∀ g ∈ (prog S.inputCleanup).funcs, ∀ b ∈ g.blocks, b.term.isTry = false)
    (hlegal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : S.inputCleanup.srcProg.func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) (legalize f))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) (legalize f)
      (DeadCleanupStackBound.stackFn S.inputCleanup (legalize f)) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env S.inputCleanup.srcProg cs s' →
      Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.inputCleanup.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ K, (sys S.inputCleanup B).std.TrapsD K (legalize f) cs') →
      Opt.Legal.NoMemTrap B.env S.inputCleanup.srcProg cs → ∀ c,
      Clif.runLoop B.env S.inputCleanup.srcProg M cs = .trapped c →
      ExecRefinesC S.inputCleanup B (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  obtain ⟨he, -⟩ := compileExeU_spec h
  obtain ⟨hin, hl⟩ := compileExe_spec he
  have hok := okB_leanLink hin hl
  have hL : (LinkSys.ofInputCleanup S.inputCleanup B fun _ => True).Ok :=
    okBCleanup_sound hok (baseOk_F hB) fun _ _ => trivial
  have hpe := prog_eq_legal S
  have hpe' : S.inputCleanup.prog = prog S.inputCleanup := (prog_eq S).symm
  have hC : ProgCtx S.inputCleanup.srcProg B.env (fun n => S.inputCleanup.syms.lookup n) :=
    srcCtx hsrc (by rw [hpe']; exact hL.names) (by rw [hpe']; exact hL.free)
      (by rw [hpe']; exact hL.declSig) (by rw [hpe']; exact hL.indScope) hlegal
      (by rw [hpe']; exact hsig)
  have hfP := (Clif.Program.func?_some hf).1
  have hf' : (prog S.inputCleanup).func? n = some (legalize f) := by
    rw [hpe]; exact hC.func?_some hf
  have hcs' := hr.entry
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hE : EntryRel f args args' cs.frame cs'.frame :=
    ⟨hcs.func, hcs'.func, ⟨b, hb, h2, h3, h4, h5⟩, ⟨b', hb', h2', h3', h5'⟩, hsl, hexp⟩
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hst' : (⟨cs'.frame, [], cs.mem⟩ : Clif.State) = cs' := by rw [← hcs'.callers, ← hmem]
  have hLe : Clif.LInv S.inputCleanup.srcProg cs := by
    rw [← hst]; exact ⟨hE.lframe hfP, fun _ h => nomatch h⟩
  have hsym : SomeInd (legalProg S.inputCleanup.srcProg) →
      Opt.EnvKeepsSymbols B.env ∧ cs.mem.symbols = fun n => S.inputCleanup.syms.lookup n := by
    intro hI
    refine ⟨(hC.ind hI).1.keep, ?_⟩
    rw [← hmem]; exact ho.symbols
  refine ⟨(compileExe_correct_source he hsrc B hB hH hlegal hsig hf hc hX ho hr hcs hexp hsl hmem
    hbnd M).1, fun htr hnmt c hrun => ?_⟩
  have hG : GoodFrom B.env S.inputCleanup.srcProg (SomeInd (legalProg S.inputCleanup.srcProg))
      (fun n => S.inputCleanup.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
    rw [hst]
    exact goodFrom_of hC.free hLe hbnd hnmt hsym
  rw [← hst] at hrun
  obtain ⟨k, hk⟩ := (legalProg_refines hC hfP hE hG M).2 c hrun
  rw [hst'] at hk
  cases k with
  | zero => simp [Clif.runLoop] at hk
  | succ K =>
    rw [← hpe] at hk
    have := compileExe_correct_trap h B hB hH hBT hnoTry hf' hc K hX ho hr (htr K)
    rw [hk] at this
    exact this

/-- **The shipped executable compiler refines the original source program, callee traps and
recursive programs included** (`compileExe_correct_source_peak` with
`compileExe_correct_trap_peak`): the stack from the source run's call depth `d`; a trap of the
source run (without load/store traps; the target runs under `TrapsD` of `LinkSys.peak` at every
fuel) is an executable state at a trap with the same code (`ExecRefinesC`). -/
theorem compileExe_correct_source_trap_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeU S file0 = .ok file) (hsrc : SrcScopeB S.inputCleanup = true)
    (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hBT : (sys S.inputCleanup B).BaseTrapsOk)
    (hnoTry : ∀ g ∈ (prog S.inputCleanup).funcs, ∀ b ∈ g.blocks, b.term.isTry = false)
    (hlegal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : S.inputCleanup.srcProg.func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) (legalize f)
      (frameDrop (art S.inputCleanup (legalize f)).af +
        (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env S.inputCleanup.srcProg cs s' →
      Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env S.inputCleanup.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.inputCleanup.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ F, ((sys S.inputCleanup B).peak F).TrapsD d (legalize f) cs') →
      Opt.Legal.NoMemTrap B.env S.inputCleanup.srcProg cs → ∀ c,
      Clif.runLoop B.env S.inputCleanup.srcProg M cs = .trapped c →
      ExecRefinesC S.inputCleanup B (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  obtain ⟨he, -⟩ := compileExeU_spec h
  obtain ⟨hin, hl⟩ := compileExe_spec he
  have hok := okB_leanLink hin hl
  have hL : (LinkSys.ofInputCleanup S.inputCleanup B fun _ => True).Ok :=
    okBCleanup_sound hok (baseOk_F hB) fun _ _ => trivial
  have hpe := prog_eq_legal S
  have hpe' : S.inputCleanup.prog = prog S.inputCleanup := (prog_eq S).symm
  have hC : ProgCtx S.inputCleanup.srcProg B.env (fun n => S.inputCleanup.syms.lookup n) :=
    srcCtx hsrc (by rw [hpe']; exact hL.names) (by rw [hpe']; exact hL.free)
      (by rw [hpe']; exact hL.declSig) (by rw [hpe']; exact hL.indScope) hlegal
      (by rw [hpe']; exact hsig)
  have hfP := (Clif.Program.func?_some hf).1
  have hf' : (prog S.inputCleanup).func? n = some (legalize f) := by
    rw [hpe]; exact hC.func?_some hf
  have hcs' := hr.entry
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hE : EntryRel f args args' cs.frame cs'.frame :=
    ⟨hcs.func, hcs'.func, ⟨b, hb, h2, h3, h4, h5⟩, ⟨b', hb', h2', h3', h5'⟩, hsl, hexp⟩
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hst' : (⟨cs'.frame, [], cs.mem⟩ : Clif.State) = cs' := by rw [← hcs'.callers, ← hmem]
  have hLe : Clif.LInv S.inputCleanup.srcProg cs := by
    rw [← hst]; exact ⟨hE.lframe hfP, fun _ h => nomatch h⟩
  have hd' : Clif.DepthLe B.env S.inputCleanup.srcProg d ⟨cs.frame, [], cs.mem⟩ := by
    rw [hst]; exact hd
  have hsym : SomeInd (legalProg S.inputCleanup.srcProg) →
      Opt.EnvKeepsSymbols B.env ∧ cs.mem.symbols = fun n => S.inputCleanup.syms.lookup n := by
    intro hI
    refine ⟨(hC.ind hI).1.keep, ?_⟩
    rw [← hmem]; exact ho.symbols
  refine ⟨(compileExe_correct_source_peak he hsrc B hB hH hlegal hsig hf d hX ho hr hcs hexp hsl
    hmem hbnd hd M).1, fun htr hnmt c hrun => ?_⟩
  have hG : GoodFrom B.env S.inputCleanup.srcProg (SomeInd (legalProg S.inputCleanup.srcProg))
      (fun n => S.inputCleanup.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
    rw [hst]
    exact goodFrom_of hC.free hLe hbnd hnmt hsym
  rw [← hst] at hrun
  obtain ⟨⟨k, hk⟩, hdT⟩ := (legalProg_refines_depth hC hfP hE hG hd' M).2 c hrun
  rw [hst'] at hk hdT
  rw [← hpe] at hdT
  cases k with
  | zero => simp [Clif.runLoop] at hk
  | succ F =>
    rw [← hpe] at hk
    have := compileExe_correct_trap_peak h B hB hH hBT hnoTry hf' F d hX ho hr hdT (htr F)
    rw [hk] at this
    exact this

end Link.DeadCleanup
