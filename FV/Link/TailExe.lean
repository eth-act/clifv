import FV.Link.TailCompile
import FV.Link.DeadCleanupOptExe
import FV.E2E.TailLoopSim

/-! # The executable compiler with self tail calls as loops is correct (S8, #32)

`Link.DeadCleanup.compileExeTail S = compileExe S.tail` (`FV/Link/TailCompile.lean`). Its theorems
are about the input's program (after the `i128` legalisation, before the tail-loop transform),
whose functions may `return_call` themselves: `compileExeTail_correct` (entries reaching no call
cycle of the transformed program) and **`compileExeTail_correct_peak`** (any entry, with
`frameDrop + (D·d + pbMax)` bytes of stack (#581: the deepest activation's stack probes write up to
`pbMax` bytes below its frame) for the **input** program's peak call depth `d`: a self
`return_call` keeps the callers, so the stack does not grow per tail call). They compose
`Link.DeadCleanup.compileExe_correct{,_peak}` on `S.tail` with the transform's refinement
`Opt.TailLoop.TailRel.refines` (`FV/E2E/TailLoopSim.lean`). Extra premises: the externs keep the
slot-placement oracle (`Clif.EnvKeepsPlace`) and the input run's entry has a consistent oracle
stack (`Opt.TailLoop.SpsOk`; `spsOk_none` without the oracle, `spsOk_entry`). Totality:
`compileExeTail_total_reach_input` (`compileExe_total_reach_input` on `S.tail`).
-/

namespace Link

open E2E.LinkCheck

theorem _root_.E2E.LinkCheck.FnInput.tail_func (fi : FnInput) :
    fi.tail.func = fi.func ∨ fi.tail.func = Opt.TailLoop.loop fi.func := by
  unfold FnInput.tail
  dsimp only
  split
  · exact .inl rfl
  · split
    · rename_i h; exact .inr (of_decide_eq_true h)
    · exact .inl rfl

theorem LinkSpec.tailRel (S : LinkSpec) : Opt.TailLoop.TailRel S.input.prog S.tail.input.prog := by
  show Opt.Pw2 Opt.TailLoop.TP (S.funcs.map FnInput.func) ((S.funcs.map FnInput.tail).map FnInput.func)
  rw [List.map_map]
  induction S.funcs with
  | nil => exact .nil
  | cons fi fs ih => exact .cons fi.tail_func ih

theorem withSizes_tail (S : LinkSpec) (z : List Nat) : (S.withSizes z).tail = S.tail.withSizes z := by
  obtain ⟨funcs, names, sizes, outside, data, symNames, R⟩ := S
  simp only [LinkSpec.withSizes, LinkSpec.tail, LinkSpec.mk.injEq, List.map_map, true_and,
    and_true]
  refine List.map_congr_left fun fi _ => ?_
  rcases fi.tail_func with h | h
  · simp [h]
  · simp [h, (Opt.TailLoop.loop_hdr fi.func).1]

end Link

namespace Opt.TailLoop

theorem TailRel.names {P P' : Clif.Program} (h : TailRel P P') :
    P'.funcs.map (·.name) = P.funcs.map (·.name) := by
  have : ∀ {fs gs : List Clif.Function}, Pw2 TP fs gs → gs.map (·.name) = fs.map (·.name) := by
    intro fs gs hp
    induction hp with
    | nil => rfl
    | cons hq _ ih => simp only [List.map_cons, tp_name hq, ih]
  exact this h

end Opt.TailLoop

namespace Link.DeadCleanup
set_option autoImplicit false

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  Backend LinkSpec

theorem compileExeTail_spec {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeTail S file0 = .ok file) : compileExe S.tail file0 = .ok file := h

theorem tailRel_prog (S : LinkSpec) :
    Opt.TailLoop.TailRel (prog S.inputCleanup) (prog S.tail.inputCleanup) := by
  rw [prog_eq, prog_eq]; exact S.tailRel

/-- The linked system of the transformed input is `Ok`. -/
theorem linkOk_tail {S : LinkSpec} {file0 file : ByteArray} (h : compileExeTail S file0 = .ok file)
    (B : BaseEnv) (hB : BaseOk (sys S.tail.inputCleanup B)) :
    (LinkSys.ofInputCleanup S.tail.inputCleanup B fun _ => True).Ok := by
  obtain ⟨hin, hl⟩ := compileExe_spec (compileExeTail_spec h)
  exact okBCleanup_sound (okB_leanLink hin hl) (baseOk_F hB) fun _ _ => trivial

/-- Distinct function names in the input's program (those of the transformed program). -/
theorem nodup_tail {S : LinkSpec} {file0 file : ByteArray} (h : compileExeTail S file0 = .ok file)
    (B : BaseEnv) (hB : BaseOk (sys S.tail.inputCleanup B)) :
    ((prog S.inputCleanup).funcs.map (·.name)).Nodup := by
  rw [← (tailRel_prog S).names]
  exact (linkOk_tail h B hB).names

/-- **The executable compiler with self tail calls as loops is correct** (about the input's
program, whose functions may `return_call` themselves): for `compileExeTail S file0 = .ok file`, an
outside call of the compiled code of the transformed function `f'` (named `n`; no call cycle
reachable from it) refines the whole-program run of the input's program from the entry `cs` of
its function `f` named `n` with the call's arguments, slots and memory (a consistent oracle
stack, the externs keeping the oracle): a return is the executable's return of the same values
with the same memory; a trap (the transformed runs' traps explicit) is the same trap. -/
theorem compileExeTail_correct {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeTail S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.tail.inputCleanup B))
    (hH : HooksSim S.tail.inputCleanup B) (hk : Clif.EnvKeepsPlace B.env) {n : String}
    {f f' : Clif.Function} (hf : (prog S.inputCleanup).func? n = some f)
    (hf' : (prog S.tail.inputCleanup).func? n = some f')
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.tail.inputCleanup S.tail.inputCleanup.resultsCleanup) f')
    {r : Arm.ArmState} {args : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.tail.inputCleanup (BinCheck.roByte S.tail.inputCleanup S.tail.data) f'
      (DeadCleanupStackBound.stackFn S.tail.inputCleanup f') r args cs'.mem)
    (hr : ClifRun S.tail.inputCleanup B f' r args cs') (hcs : ClifEntry f args cs)
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hsp : Opt.TailLoop.SpsOk cs) (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env (prog S.inputCleanup) M cs = .returned vals cm →
      ExecRefines (art S.tail.inputCleanup f').fb (art S.tail.inputCleanup f').base (xreg 30 r)
        (step S.tail.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.tail.inputCleanup)
        (.returned vals cm)) ∧
    ((∀ K, TrapsExplicit (Clif.linkEnvN (prog S.tail.inputCleanup) B.env K)
        (prog S.tail.inputCleanup).bare cs') →
      ∀ c, Clif.runLoop B.env (prog S.inputCleanup) M cs = .trapped c →
      ExecRefines (art S.tail.inputCleanup f').fb (art S.tail.inputCleanup f').base (xreg 30 r)
        (step S.tail.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.tail.inputCleanup)
        (.trapped c)) := by
  have hL := linkOk_tail h B hB
  have hcs' := hr.entry
  obtain ⟨m, h1, h2, -⟩ := (tailRel_prog S).refines (nodup_tail h B hB) hk hf hf' hcs hcs' hsl
    hmem hsp M
  have hfP' : f' ∈ (prog S.tail.inputCleanup).funcs := (Clif.Program.func?_some hf').1
  have hexec : ∀ {o : Clif.Outcome} {m : Nat}, Clif.runLoop B.env (prog S.tail.inputCleanup) m cs' = o →
      o ≠ .outOfFuel → (∀ K, Clif.runLoop B.env (prog S.tail.inputCleanup) (K + 1) cs' = o →
        TrapsExplicit (Clif.linkEnvN (prog S.tail.inputCleanup) B.env K)
          (prog S.tail.inputCleanup).bare cs') →
      ExecRefines (art S.tail.inputCleanup f').fb (art S.tail.inputCleanup f').base (xreg 30 r)
        (step S.tail.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.tail.inputCleanup) o := by
    intro o m hm hof htr
    cases m with
    | zero => exact absurd hm.symm (by simpa using hof)
    | succ K =>
      have := compileExe_correct (compileExeTail_spec h) B hB hH hf' hc K hX ho hr (htr K hm)
      rw [hm] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr c hrun => ?_⟩
  · exact hexec (h1 vals cm hrun) (fun h => by cases h)
      fun K hK => trapsExplicit_of_run hL hfP' hcs' ho.symbols hK
  · exact hexec (h2 c hrun) (fun h => by cases h) fun K _ => htr K

/-- **The executable compiler with self tail calls as loops is correct for recursive programs,
with the stack of the input run's peak call depth**: `compileExeTail_correct` without the call-graph
premise; the outside caller provides `frameDrop + (D * d + pbMax)` bytes of stack (#581: the
deepest activation's stack probes write up to `pbMax` bytes below its frame), where `d` bounds the call
depth of the **input** program's run from `cs` (`Clif.DepthLe`). A self `return_call` does not
add a caller, in the input's run as in the loop, so the stack does not grow per tail call. -/
theorem compileExeTail_correct_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeTail S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.tail.inputCleanup B))
    (hH : HooksSim S.tail.inputCleanup B) (hk : Clif.EnvKeepsPlace B.env) {n : String}
    {f f' : Clif.Function} (hf : (prog S.inputCleanup).func? n = some f)
    (hf' : (prog S.tail.inputCleanup).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.tail.inputCleanup (BinCheck.roByte S.tail.inputCleanup S.tail.data) f'
      (frameDrop (art S.tail.inputCleanup f').af + (S.tail.inputCleanup.D * d + pbMax S.tail.inputCleanup))
      r args cs'.mem)
    (hr : ClifRun S.tail.inputCleanup B f' r args cs') (hcs : ClifEntry f args cs)
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hsp : Opt.TailLoop.SpsOk cs) (hd : Clif.DepthLe B.env (prog S.inputCleanup) d cs) (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env (prog S.inputCleanup) M cs = .returned vals cm →
      ExecRefines (art S.tail.inputCleanup f').fb (art S.tail.inputCleanup f').base (xreg 30 r)
        (step S.tail.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.tail.inputCleanup)
        (.returned vals cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.tail.inputCleanup) B.env F d)
        (prog S.tail.inputCleanup).bare cs') →
      ∀ c, Clif.runLoop B.env (prog S.inputCleanup) M cs = .trapped c →
      ExecRefines (art S.tail.inputCleanup f').fb (art S.tail.inputCleanup f').base (xreg 30 r)
        (step S.tail.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.tail.inputCleanup)
        (.trapped c)) := by
  have hL := linkOk_tail h B hB
  have hcs' := hr.entry
  obtain ⟨m, h1, h2, h3⟩ := (tailRel_prog S).refines (nodup_tail h B hB) hk hf hf' hcs hcs' hsl
    hmem hsp M
  have hfP' : f' ∈ (prog S.tail.inputCleanup).funcs := (Clif.Program.func?_some hf').1
  have hexec : Clif.DepthLe B.env (prog S.tail.inputCleanup) d cs' →
      ∀ {o : Clif.Outcome} {m : Nat}, Clif.runLoop B.env (prog S.tail.inputCleanup) m cs' = o →
      o ≠ .outOfFuel → (∀ F, Clif.runLoop B.env (prog S.tail.inputCleanup) (F + 1) cs' = o →
        TrapsExplicit (Clif.linkEnvD (prog S.tail.inputCleanup) B.env F d)
          (prog S.tail.inputCleanup).bare cs') →
      ExecRefines (art S.tail.inputCleanup f').fb (art S.tail.inputCleanup f').base (xreg 30 r)
        (step S.tail.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.tail.inputCleanup) o := by
    intro hd' o m hm hof htr
    cases m with
    | zero => exact absurd hm.symm (by simpa using hof)
    | succ F =>
      have := compileExe_correct_peak (compileExeTail_spec h) B hB hH hf' F d hX ho hr hd' (htr F hm)
      rw [hm] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr c hrun => ?_⟩
  · have hd' := h3 (by rw [hrun]; trivial) d hd
    exact hexec hd' (h1 vals cm hrun) (fun h => by cases h)
      fun F hF => E2E.Binary.trapsExplicit_of_runD hL hfP' hcs' ho.symbols hd' hF
  · have hd' := h3 (by rw [hrun]; trivial) d hd
    exact hexec hd' (h2 c hrun) (fun h => by cases h) fun F _ => htr F

/-- **The executable compiler with self tail calls as loops succeeds on input conditions decided
without compiling** (`compileExe_total_reach_input` on the transformed input): on the
transformed input (`InScopeIn`), its layout (`layoutOkB`), the reach of its functions'
references from the region (`reachOkB`), rust-lld's executable `file0` (`file0OkB`), with the
sizes of the transformed functions' compiled code. -/
theorem compileExeTail_total_reach_input {S : LinkSpec} {file0 : ByteArray} {phs : List Phdr}
    (hin : InScopeIn (placed S.tail).input0 = true) (hl : (placed S.tail).layoutOkB = true)
    (hph : phdrs (fileRd file0) = some phs) (hf : (placed S.tail).file0OkB file0 phs = true)
    (hreach : (placed S.tail).reachOkB = true) :
    compileExeTail (S.withSizes (sizesOf S.tail)) file0 =
      .ok (patch file0 (offsetOf phs S.R) (regionOf (placed S.tail) (tpOff phs))) := by
  show compileExe (S.withSizes (sizesOf S.tail)).tail file0 = _
  rw [Link.withSizes_tail]
  exact compileExe_total_reach_input hin hl hph hf hreach

end Link.DeadCleanup
