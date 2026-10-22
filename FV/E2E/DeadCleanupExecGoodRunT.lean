import FV.E2E.DeadCleanupExecGoodRun
import FV.E2E.DeadCleanupBinaryGoodT
import FV.E2E.DeadCleanupExecRunNT
import FV.E2E.ExecGoodRunT
import FV.E2E.DeadCleanupBinaryT
import FV.E2E.BinCheckT
import FV.E2E.BinaryGoodT
import FV.E2E.BinaryT
import FV.E2E.DeadCleanupExecBytesT
import FV.E2E.DeadCleanupLinkCheckT
import FV.E2E.DeadCleanupStackBoundT
import FV.E2E.ExecBytesT
import FV.E2E.ExecRunNT
import FV.E2E.ExecStaticT
import FV.E2E.LinkArmT
import FV.E2E.LinkCheckT
import FV.E2E.LinkGoodT
import FV.E2E.PipelineCheckT
import FV.E2E.StackBoundT

/-! # Typed copies of `FV.E2E.DeadCleanupExecGoodRun` (S11e5 Stage C, slice 8)

The declarations of `FV.E2E.DeadCleanupExecGoodRun` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefinesT`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`). -/

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false
open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck
section Conv
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- The calls through a register of a function of a linked system with `Ok` are through integer
vregs (`LinkSys.OkT.blrRegs`). -/
theorem destsInt_of_okT {L : LinkSys} (hL : L.OkT) {g : Clif.Function} (hg : g ∈ L.P.funcs) :
    (L.A g).vcp.DestsInt := by
  intro b vb k info hb hi r hd
  obtain ⟨t, Lu, Ld, he, -⟩ := hL.blrRegs g hg info ⟨b, vb, k, hb, hi⟩ (fun n => by rw [hd]; simp)
  subst he
  simp only [CallDest.reg.injEq] at hd
  exact ⟨t, hd.symm⟩
end Conv

/-- **`binary_correct_exec_static` with the per-state facts of the register-level proof**: under
the premisesT of `binary_correct_of_checks_acyclic`, the outside-code contract `HooksSim`, the
code map check `codeMapB` and only the memory-read factsT `RunReadsN` (D2, D4) of the model's run,
the executable machine run from `r` refines the whole-program CLIF run. -/
theorem binary_correct_exec_of_readsT {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okBCleanup I = true) (hcm : codeMapB I (tabOf I.resultsCleanup) = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file) (B : BaseEnv) (hB : BaseOk (sys I B)) (hH : HooksSim I B)
    {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls I I.resultsCleanup) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hreads : RunReadsN I B file M f (modelOf I f r)) :
    ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (E2E.DeadCleanupBinCheck.RelocAt I)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hn := (DeadCleanupStackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  obtain ⟨-, -, hG⟩ := binary_correct_of_checksXT hI hbin B hB hn hf M hX ho hr htr
  by_cases hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)
  · have hfm := (Clif.Program.func?_some hf).1
    have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)) := baseOk_F hB
    have hL := okBCleanup_soundT hI hB' fun _ h => .inr h
    have hfacts := binFacts_of_checksT hI hbin
    have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
      hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
    obtain ⟨hent, -⟩ := premisesT hL hfm hro ho hr
    have hL' := okBCleanup_soundT hI (baseOk_F (F' := img I) hB) fun _ h => h
    have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOkT hI hbin hL' hg
    have hra : ∀ k < (art I f).fb.words.size,
        xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
      simp only [xreg, r_modelOf]; exact hent.raOutside
    exact binary_correct_exec_staticNT hI hcm hbin B hB hH hf hc M hX ho hr htr
      (runOkN_of_goodT hI hcm hF (fun g hg => destsInt_of_okT hL' hg) hfm hra (hG hout) hreads)
  · cases h : Clif.runLoop B.env (prog I) (M + 1) cs with
    | returned vals cm => exact absurd (.inl ⟨vals, cm, h⟩) hout
    | trapped c => exact absurd (.inr ⟨c, h⟩) hout
    | stuck _ => trivial
    | outOfFuel => trivial
end E2E.DeadCleanupExecBytes
