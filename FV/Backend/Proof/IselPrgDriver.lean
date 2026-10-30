import FV.Backend.Proof.IselPrgRun
import FV.Backend.Proof.IselPrgTab
import FV.Backend.Proof.IselPrgCover
import FV.Backend.Proof.IselPrgExtSound
import FV.Backend.Proof.IselPrgCtorSound
import FV.Backend.Proof.IselPrgHand
import FV.Backend.Proof.IselPrgTryLast
import FV.Backend.Proof.LowerTotal

/-!
# Progress of the ISLE lowering (V7): the driver's ISLE runs return

`iselProg_of_input`: for input in scope (`dominatedB`, `lowerScopeB`, `extendsWidenB`, the
driver's and the ISLE side's input conditions `driverInB`, `iselInB`), every ISLE run of the
driver in the context `buildCtx f` builds returns as the driver needs (`IselProg`): a statement's
`lower` one single register per result, a terminator's `lower`/`lower_branch` a value, a
`try_call`'s `lower_branch` a value with its code ending in the call.

The pieces: the model of the extern helpers (`aext_sound`, `actor_sound`, `aidata_sound` under
`PInv`), the hand-checked rules (`handOk`), the table check (`prgTab_ok`) and its roots
(`stmtRoots_ok`, `termRoots_ok`), the roots' abstract values (`stmt_root`, `term_root`,
`try_root`), and `progress` (`root_run`). `lowerFunction_ok_input`: `lowerFunction` succeeds.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx}

/-- **The model of the extern helpers** under the context invariant. -/
theorem model_of (hP : PInv f ctx) : Model f ctx aext actor aidata :=
  ⟨fun term a outs must v st h hv => aext_sound hP term a outs must v st h hv,
   fun term as a must vs st h hv => actor_sound hP term as a must vs st h hv,
   fun v hv => aidata_sound hP v hv⟩

/-- A statement form's output is a register vector. -/
theorem stmtOut_regsVec (F : PA) : ∃ n, stmtOut F = .regsVec n := by
  unfold stmtOut
  split <;> exact ⟨_, rfl⟩

/-- The root of an abstract argument list: an entry that surely returns within the fuel. -/
theorem termRoot_entry {q : TermId × List PA} (hq : q ∈ termRoots) :
    ∃ e, tabFind prgTab q.1 q.2 = some e ∧ e.osome = true ∧ e.fu ≤ 1000000 := by
  have h := List.all_eq_true.mp termRoots_ok q hq
  unfold termRootOk at h
  split at h
  · rename_i e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨e, he, h.1, h.2⟩
  · cases h

/-- **Statements.** -/
theorem stmtProg (hP : PInv f ctx) : StmtProg ctx := by
  intro ii info inst s hi hc
  obtain ⟨hγ, hmem, hout⟩ := stmt_root hP hi hc
  have h := List.all_eq_true.mp stmtRoots_ok _ hmem
  unfold stmtRootOk at h
  split at h
  · rename_i e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hos, hle⟩, hfu⟩ := h
    obtain ⟨w, s', tr, hrun, hw⟩ := root_run (model_of hP) (handOk hP rfl prgTab) prgTab_ok
      program_termByName_lower (T := T.lower) (e := e) he hos hfu
      (show γL f ctx [formOf f inst] [.inst ii] from ⟨hγ, trivial⟩) s
    have hw' := le_sound _ _ hle w hw
    obtain ⟨n, hn⟩ := stmtOut_regsVec (formOf f inst)
    rw [hn] at hw'
    obtain ⟨rss, rfl, -, -⟩ := hw'
    refine ⟨rss, s', tr, hrun, fun hne => hout hne rss ?_⟩
    exact le_sound _ _ hle _ hw
  · cases h

variable {ranges : Array (Nat × Nat)} {st0 : LState}

/-- **Terminators.** -/
theorem termProg (hP : PInv f ctx) (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hdom : dominatedB f = true) (hin : iselInB f = true) (hdrv : driverInB f = true) :
    TermProg f ctx := by
  intro ti t data targets s _ hph hB _ hd hlen
  obtain ⟨q, hq, ⟨T, hT, hTid⟩, hγ⟩ := term_root hP hb hdom hin hdrv hph hB hd hlen
  obtain ⟨e, he, hos, hfu⟩ := termRoot_entry hq
  have hP' := pinv_termCtx hP hph data
  rw [← hTid] at he
  obtain ⟨w, s', tr, hrun, -⟩ := root_run (model_of hP') (handOk hP' rfl prgTab) prgTab_ok hT he
    hos hfu hγ s
  exact ⟨w, s', tr, hrun⟩

/-- **`try_call`s.** -/
theorem tryProg (hP : PInv f ctx) (hctx : CtxInv f ctx) (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hdom : dominatedB f = true) (hin : iselInB f = true) : TryProg f ctx := by
  intro ti t et data sig items trs st1 st2 targets s _ hph hB het hd hx hr hlen
  obtain ⟨q, hq, hq1, hγ⟩ := try_root hP hb hdom hin hph hB het hd hx hr hlen
  obtain ⟨e, he, hos, hfu⟩ := termRoot_entry hq
  have hP' := pinv_tryCtx hP hph data trs
  rw [hq1] at he
  obtain ⟨w, s', tr, hrun, -⟩ := root_run (model_of hP') (handOk hP' rfl prgTab) prgTab_ok
    program_termByName_lower_branch (T := T.lower_branch) he hos hfu hγ s
  obtain ⟨c, hc⟩ := tryCall_last hP hctx hd hph (trs := trs) (targets := targets) (s := s) hrun
  exact ⟨w, s', tr, c, hrun, hc⟩

/-- **The ISLE side of the driver's totality**, for input in scope. -/
theorem iselProg_of_input (hdom : dominatedB f = true) (hs : lowerScopeB f = true)
    (hw : extendsWidenB f = true) (hin : iselInB f = true) (hdrv : driverInB f = true)
    (hb : buildCtx f = .ok (ctx, ranges, st0)) : IselProg f ctx :=
  have hP := pinv_build hdom hs hw hin hb
  ⟨stmtProg hP, termProg hP hb hdom hin hdrv,
    tryProg hP (ctxOk_sound (ctxOk_complete (lowerScope_of hs) hb)) hb hdom hin⟩

/-- **`lowerFunction` is total on input in scope.** -/
theorem lowerFunction_ok_input (hE : Compile.functionE f = true) (hsig : sigAbiOk f.sig = true)
    (hdom : dominatedB f = true) (hs : lowerScopeB f = true) (har : Spill.arityOkB f = true)
    (hent : Spill.entryParamsB f = true) (hw : extendsWidenB f = true)
    (hdrv : driverInB f = true) (hin : iselInB f = true) : ∃ vc, lowerFunction f = .ok vc :=
  lowerFunction_ok hE hsig hdom hs har hent hdrv fun _ _ _ hb =>
    iselProg_of_input hdom hs hw hin hdrv hb

end Backend.Proof.Prg
