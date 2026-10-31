import FV.Link.DeadCleanupExeSource
import FV.E2E.DeadCleanupExecMemFault

/-! # The shipped executable compiler with memory faults (A3, #412, slice F8d)

`docs/plans/memfault.md`. `Link.DeadCleanup.compileExe_correct_memtrap{,_peak}` and
`compileExe_correct_source_memtrap{,_peak}` (`FV/Link/DeadCleanupExeMemTrap.lean`) say, for the
executable's run under the fault-aware machine `stepF mp`, only that **if** it reaches the
trapping atomic, its `ldaxr` faults under the map; they do not say that no earlier step of the
run faults under `mp`. Here the trap halves of the same executables with the additional premise
`MapRelRW mp` (F8): every byte the map does not allow to be written lies outside the reserved
stack `N`, the stack arguments and every allocation of the entry's CLIF memory, and the program's
code is readable — so every byte valid in the entry's CLIF memory is mapped read-write (read-only
data included; F8a, #472, will relax it), and no earlier step of the run faults under `mp`:
the observable is `ExecTrapF` (`E2E.DeadCleanupExecBytes.ExecTrapF`), a trap site of the entry
function with the code whose instruction errs (`udf`) or faults under `mp`, with no faulting step
before it and its step there errs.

* `compileExe_correct_memtrapF_rw`, `compileExe_correct_memtrapF_rw_peak`: the whole-program run's
  trap, every fuel (`M + 1`, peak `F + 1`);
* `compileExe_correct_source_memtrapF_rw{,_peak}`: the trap of the original
  (pre-`i128`-legalisation) program's run (the source run without load/store traps,
  `Opt.Legal.NoMemTrap`, which allows atomic traps) under the target's `TrapsExplicitM` and
  `MapFaults mp` at every fuel.
-/

namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend Backend.Proof.Driver LinkSpec Opt.Legalize128

/-- **The shipped executable compiler is correct with memory faults** (entries without a
reachable call cycle; the trap half of `compileExe_correct_memtrap` with the `MapRelRW` premise):
for `compileExe S file0 = .ok file` and an outside call of a function `f` of the program, a
whole-program CLIF run that traps with `tc` under `TrapsExplicitM` and `MapFaults mp` makes the
fault-aware executable machine `stepF mp` run from `r` to a trap site of `f` with `tc` whose
instruction errs (`udf`) or faults under `mp`, with no faulting step before it (`ExecTrapF`). -/
theorem compileExe_correct_memtrapF_rw {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
    (hH : HooksSim S.inputCleanup B) {n : String} {f : Clif.Function}
    (hf : (prog S.inputCleanup).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f
      (DeadCleanupStackBound.stackFn S.inputCleanup f) r args cs.mem)
    (hr : ClifRun S.inputCleanup B f r args cs)
    {mp : ArmFault.MemMap}
    (htr : TrapsExplicitM (Clif.linkEnvN (prog S.inputCleanup) B.env M) (prog S.inputCleanup).bare cs)
    (hmf : MapFaults mp (Clif.linkEnvN (prog S.inputCleanup) B.env M) (prog S.inputCleanup).bare cs)
    (hmap : MapRelRW mp S.inputCleanup f (DeadCleanupStackBound.stackFn S.inputCleanup f) r args
      cs.mem) :
    ∀ tc, Clif.runLoop B.env (prog S.inputCleanup) (M + 1) cs = .trapped tc →
      ExecTrapF mp S.inputCleanup B file f tc r := by
  intro tc hrun
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact binary_correct_exec_memtrapF_rw (okB_leanLink hin hl) (codeMap_leanLink hl)
    (binOk_leanLink hl) (leanLink_gotSlot hl) B hB hH hf hc M hX ho hr htr hmf hmap hrun

/-- **The shipped executable compiler is correct with memory faults, recursive programs
included** (`compileExe_correct_memtrapF_rw` for the run's peak call depth `d`, as
`compileExe_correct_memtrap_peak`): the outside caller provides `frameDrop + (D * d + pbMax)` bytes of
stack, the run premises are of the callees running with fuel `F` and at most `d - 1` callers of
their own (`Clif.linkEnvD`). -/
theorem compileExe_correct_memtrapF_rw_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
    (hH : HooksSim S.inputCleanup B) {n : String} {f : Clif.Function}
    (hf : (prog S.inputCleanup).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f
      (frameDrop (art S.inputCleanup f).af + (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args
      cs.mem)
    (hr : ClifRun S.inputCleanup B f r args cs)
    (hd : Clif.DepthLe B.env (prog S.inputCleanup) d cs)
    {mp : ArmFault.MemMap}
    (htr : TrapsExplicitM (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs)
    (hmf : MapFaults mp (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs)
    (hmap : MapRelRW mp S.inputCleanup f
      (frameDrop (art S.inputCleanup f).af + (S.inputCleanup.D * d + pbMax S.inputCleanup))
      r args cs.mem) :
    ∀ tc, Clif.runLoop B.env (prog S.inputCleanup) (F + 1) cs = .trapped tc →
      ExecTrapF mp S.inputCleanup B file f tc r := by
  intro tc hrun
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact binary_correct_exec_memtrapF_rw_peak (okB_leanLink hin hl) (codeMap_leanLink hl)
    (binOk_leanLink hl) (leanLink_gotSlot hl) B hB hH hf F d hX ho hr hd htr hmf hmap hrun

/-- **The shipped executable compiler refines the original source program, memory faults
included** (the trap half of `compileExe_correct_source_memtrap` with the `MapRelRW` premise): a
trap of the source run (without load/store traps; atomic traps allowed) under the target's
`TrapsExplicitM` and `MapFaults mp` at every fuel makes the fault-aware executable machine
`stepF mp` run from `r` to a trap site of the entry function with the same code whose instruction
errs (`udf`) or faults under `mp`, with no faulting step before it (`ExecTrapF`). -/
theorem compileExe_correct_source_memtrapF_rw {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (hsrc : SrcScopeB S.inputCleanup = true)
    (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
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
    (M : Nat) (mp : ArmFault.MemMap)
    (hmap : MapRelRW mp S.inputCleanup (legalize f)
      (DeadCleanupStackBound.stackFn S.inputCleanup (legalize f)) r args' cs'.mem)
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env S.inputCleanup.srcProg cs s' →
      Opt.Legal.MemBounded s'.mem) :
    (∀ K, TrapsExplicitM (Clif.linkEnvN (prog S.inputCleanup) B.env K) (prog S.inputCleanup).bare cs' ∧
      MapFaults mp (Clif.linkEnvN (prog S.inputCleanup) B.env K) (prog S.inputCleanup).bare cs') →
    Opt.Legal.NoMemTrap B.env S.inputCleanup.srcProg cs → ∀ c,
    Clif.runLoop B.env S.inputCleanup.srcProg M cs = .trapped c →
    ExecTrapF mp S.inputCleanup B file (legalize f) c r := by
  have he := h
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
  intro htr hnmt c hrun
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
    exact compileExe_correct_memtrapF_rw h B hB hH hf' hc K hX ho hr (htr K).1 (htr K).2 hmap c hk

/-- **The shipped executable compiler refines the original source program, memory faults and
recursive programs included** (the trap half of `compileExe_correct_source_memtrap_peak` with the
`MapRelRW` premise): as `compileExe_correct_source_memtrapF_rw`, about the runs' peak call depth
`d` (the stack from the units' run's call depth `d`, the target's run premises of the callees
running with fuel `F` and at most `d - 1` callers of their own, at every fuel). -/
theorem compileExe_correct_source_memtrapF_rw_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (hsrc : SrcScopeB S.inputCleanup = true)
    (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
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
    (M : Nat) (mp : ArmFault.MemMap)
    (hmap : MapRelRW mp S.inputCleanup (legalize f)
      (frameDrop (art S.inputCleanup (legalize f)).af +
        (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args' cs'.mem)
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env S.inputCleanup.srcProg cs s' →
      Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env S.inputCleanup.srcProg d cs) :
    (∀ F, TrapsExplicitM (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs' ∧
      MapFaults mp (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs') →
    Opt.Legal.NoMemTrap B.env S.inputCleanup.srcProg cs → ∀ c,
    Clif.runLoop B.env S.inputCleanup.srcProg M cs = .trapped c →
    ExecTrapF mp S.inputCleanup B file (legalize f) c r := by
  have he := h
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
  intro htr hnmt c hrun
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
    exact compileExe_correct_memtrapF_rw_peak h B hB hH hf' F d hX ho hr hdT (htr F).1 (htr F).2
      hmap c hk

end Link.DeadCleanup
