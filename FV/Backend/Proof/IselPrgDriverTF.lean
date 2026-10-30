import FV.Backend.Proof.IselPrgRun
import FV.Backend.Proof.IselPrgHandF64
import FV.Backend.Proof.IselPrgCoverTermT
import FV.Backend.Proof.IselPrgTryLastT
import FV.Backend.Proof.IselPrgTabTF
import FV.Backend.Proof.IselPrgCoverTF
import FV.Backend.Proof.IselPrgCtxTF
import FV.Backend.Proof.LowerTotalTF

/-!
# Progress of the ISLE lowering over the float scope: the driver's ISLE runs return (S11f, #35)

`iselProgTF_of_input`: for a function of the float scope (`LowerScopeTF`: the typed movement
scope with the S11f float arithmetic, rounding, conversions and `fcmp`) with the input
conditions `dominatedB`, `extendsWidenB`, `iselInB`, `driverInB`, every ISLE run of the driver in
the context `buildCtx f` builds returns as the driver needs (`IselProg`): `iselProgT_of_input`'s
proof over the float scope's table `prgTabTF` (checked with `aextTF`: `def_inst` may find a float
operation), the float scope's statement roots (`stmt_rootTF`), the terminator roots
(`term_rootTB`, `try_rootTB`), the model `model_ofTF` and the hand-checked rules (`handOkG`; the
`f64const` sub-table `f64Tab` checks under `aextTF`, `f64TabF_ok`).

`lowerFunction_ok_inputTF`: `lowerFunction` succeeds on such input (`lowerFunction_okTF` with
`IselProg` discharged).
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx}

/-- **The model of the extern helpers over the float scope** under its context invariant. -/
theorem model_ofTF (hP : PInvTF f ctx) : Model f ctx aextTF actorT aidata :=
  ⟨fun term a outs must v st h hv => aextTF_sound hP term a outs must v st h hv,
   fun term as a must vs st h hv => actorT_soundB hP.toPInvTB term as a must vs st h hv,
   fun v hv => aidata_soundTB hP.toPInvTB v hv⟩

set_option maxRecDepth 100000 in
/-- No `lower` entry of the float scope's table describes a slot without CLIF instruction holding
`f64const` data. -/
theorem prgTabTF_f64Safe : prgTabTF.all f64Safe = true := by
  decide +kernel

/-- The root of an abstract argument list of the float scope's table: an entry that surely
returns within the fuel. -/
theorem termRoot_entryTF {q : TermId × List PA} (hq : q ∈ termRootsT) :
    ∃ e, tabFind prgTabTF q.1 q.2 = some e ∧ e.osome = true ∧ e.fu ≤ 1000000 := by
  have h := List.all_eq_true.mp termRootsTF_ok q hq
  unfold termRootOkTF at h
  split at h
  · rename_i e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨e, he, h.1, h.2⟩
  · cases h

/-- The hand-checked rules of the float scope's table return. -/
theorem handOk_prgTabTF (hP : PInvTF f ctx) : HandOk f ctx program {} prgTabTF handRulesT :=
  handOkG hP.toPInvTB (model_ofTF hP) f64TabF_ok
    (fun _ _ h => instET_of_iconstF (hP.instETF _ h)) rfl prgTabTF prgTabTF_f64Safe

/-- **Statements** over the float scope. -/
theorem stmtProgTF (hP : PInvTF f ctx) : StmtProg ctx := by
  intro ii info inst s hi hc
  obtain ⟨hγ, hmem, hout⟩ := stmt_rootTF hP hi hc
  have h := List.all_eq_true.mp stmtRootsTF_ok _ hmem
  unfold stmtRootOkTF at h
  split at h
  · rename_i e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hos, hle⟩, hfu⟩ := h
    obtain ⟨w, s', tr, hrun, hw⟩ := root_run (model_ofTF hP) (handOk_prgTabTF hP) prgTabTF_ok
      program_termByName_lower (T := T.lower) (e := e) he hos hfu
      (show γL f ctx [formOfTF f inst] [.inst ii] from ⟨hγ, trivial⟩) s
    have hw' := le_sound _ _ hle w hw
    obtain ⟨n, hn⟩ : ∃ n, stmtOut (formOfTF f inst) = .regsVec n := by
      unfold stmtOut; split <;> exact ⟨_, rfl⟩
    rw [hn] at hw'
    obtain ⟨rss, rfl, -, -⟩ := hw'
    refine ⟨rss, s', tr, hrun, fun hne => hout hne rss ?_⟩
    exact le_sound _ _ hle _ hw
  · cases h

variable {ranges : Array (Nat × Nat)} {st0 : LState}

/-- **Terminators** over the float scope. -/
theorem termProgTF (hP : PInvTF f ctx) (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hdom : dominatedB f = true) (hin : iselInB f = true) (hdrv : driverInB f = true) :
    TermProg f ctx := by
  intro ti t data targets s _ hph hB _ hd hlen
  obtain ⟨q, hq, ⟨T, hT, hTid⟩, hγ⟩ := term_rootTB hP.toPInvTB hb hdom hin hdrv hph hB hd hlen
  obtain ⟨e, he, hos, hfu⟩ := termRoot_entryTF hq
  have hP' := pinv_termCtxTF hP hph data
  rw [← hTid] at he
  obtain ⟨w, s', tr, hrun, -⟩ := root_run (model_ofTF hP') (handOk_prgTabTF hP') prgTabTF_ok hT he
    hos hfu hγ s
  exact ⟨w, s', tr, hrun⟩

/-- **`try_call`s** over the float scope. -/
theorem tryProgTF (hP : PInvTF f ctx) (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hdom : dominatedB f = true) (hin : iselInB f = true) : TryProg f ctx := by
  intro ti t et data sig items trs st1 st2 targets s _ hph hB het hd hx hr hlen
  obtain ⟨q, hq, hq1, hγ⟩ := try_rootTB hP.toPInvTB hb hdom hin hph hB het hd hx hr hlen
  obtain ⟨e, he, hos, hfu⟩ := termRoot_entryTF hq
  have hP' := pinv_tryCtxTF hP hph data trs
  rw [hq1] at he
  obtain ⟨w, s', tr, hrun, -⟩ := root_run (model_ofTF hP') (handOk_prgTabTF hP') prgTabTF_ok
    program_termByName_lower_branch (T := T.lower_branch) he hos hfu hγ s
  obtain ⟨c, hc⟩ := tryCall_lastG hP.toPInvTB hP.instETF hB hd hph (trs := trs)
    (targets := targets) (s := s) hrun
  exact ⟨w, s', tr, c, hrun, hc⟩

/-- **The ISLE side of the driver's totality over the float scope**, for input in scope. -/
theorem iselProgTF_of_input (hdom : dominatedB f = true) (hs : LowerScopeTF f)
    (hw : extendsWidenB f = true) (hin : iselInB f = true) (hdrv : driverInB f = true)
    (hb : buildCtx f = .ok (ctx, ranges, st0)) : IselProg f ctx :=
  have hP := pinv_buildTF hdom hs hw hin hb
  ⟨stmtProgTF hP, termProgTF hP hb hdom hin hdrv, tryProgTF hP hb hdom hin⟩

/-- **`lowerFunction` is total on input of the float scope**: the S11f float arithmetic,
rounding, conversions and scalar `fcmp` (`Compile.functionETF`, `LowerScopeTF`) with the input
conditions of `lowerFunction_ok_inputT`. -/
theorem lowerFunction_ok_inputTF (hsig : sigAbiOk f.sig = true) (hdom : dominatedB f = true)
    (hs : LowerScopeTF f) (har : Spill.arityOkB f = true) (hent : Spill.entryParamsB f = true)
    (hw : extendsWidenB f = true) (hdrv : driverInB f = true) (hin : iselInB f = true) :
    ∃ vc, lowerFunction f = .ok vc :=
  lowerFunction_okTF hs hsig hdom har hent hdrv fun _ _ _ hb =>
    iselProgTF_of_input hdom hs hw hin hdrv hb

end Backend.Proof.Prg
