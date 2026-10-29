module

public import FV.Backend.Proof.IselPrgRun
public import FV.Backend.Proof.IselPrgTabT
public import FV.Backend.Proof.IselPrgHandF64
public import FV.Backend.Proof.IselPrgCoverTermT
public import FV.Backend.Proof.IselPrgTryLastT
public import FV.Backend.Proof.LowerTotalT

@[expose] public section

/-!
# Progress of the ISLE lowering over the typed scope: the driver's ISLE runs return

`iselProgT_of_input`: for a function of the typed scope (`LowerScopeT`) with the input conditions
`dominatedB`, `extendsWidenB`, `iselInB`, `driverInB`, every ISLE run of the driver in the context
`buildCtx f` builds returns as the driver needs (`IselProg`): `IselPrgDriver`'s proof over the
typed table `prgTabT`, the typed roots (`stmt_rootT`, `term_rootT`, `try_rootT`), the typed model
(`model_ofT`) and the hand-checked rules of the typed scope (`handOkT`; `prgTabT_f64Safe`: no
`lower` entry of the table describes a slot without CLIF instruction holding `f64const` data).

`lowerFunction_ok_inputT`: `lowerFunction` succeeds on such input (`lowerFunction_okT` with
`IselProg` discharged). Its premises are conjuncts of `E2E.fnScopeInTB` (`LowerScopeT` from
`lowerScopeTB` by `E2E.LinkCheck.lowerScopeT_of`).
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx}

set_option maxRecDepth 100000 in
/-- No `lower` entry of the typed table describes a slot without CLIF instruction holding
`f64const` data. -/
theorem prgTabT_f64Safe : prgTabT.all f64Safe = true := by
  decide +kernel

/-- The root of an abstract argument list of the typed table: an entry that surely returns
within the fuel. -/
theorem termRoot_entryT {q : TermId × List PA} (hq : q ∈ termRootsT) :
    ∃ e, tabFind prgTabT q.1 q.2 = some e ∧ e.osome = true ∧ e.fu ≤ 1000000 := by
  have h := List.all_eq_true.mp termRootsT_ok q hq
  unfold termRootOkT at h
  split at h
  · rename_i e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨e, he, h.1, h.2⟩
  · cases h

/-- The hand-checked rules of the typed table return. -/
theorem handOk_prgTabT (hP : PInvT f ctx) : HandOk f ctx program {} prgTabT handRulesT :=
  handOkT hP rfl prgTabT prgTabT_f64Safe

/-- **Statements** over the typed scope. -/
theorem stmtProgT (hP : PInvT f ctx) : StmtProg ctx := by
  intro ii info inst s hi hc
  obtain ⟨hγ, hmem, hout⟩ := stmt_rootT hP hi hc
  have h := List.all_eq_true.mp stmtRootsT_ok _ hmem
  unfold stmtRootOkT at h
  split at h
  · rename_i e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hos, hle⟩, hfu⟩ := h
    obtain ⟨w, s', tr, hrun, hw⟩ := root_run (model_ofT hP) (handOk_prgTabT hP) prgTabT_ok
      program_termByName_lower (T := T.lower) (e := e) he hos hfu
      (show γL f ctx [formOfT f inst] [.inst ii] from ⟨hγ, trivial⟩) s
    have hw' := le_sound _ _ hle w hw
    obtain ⟨n, hn⟩ : ∃ n, stmtOut (formOfT f inst) = .regsVec n := by
      unfold stmtOut; split <;> exact ⟨_, rfl⟩
    rw [hn] at hw'
    obtain ⟨rss, rfl, -, -⟩ := hw'
    refine ⟨rss, s', tr, hrun, fun hne => hout hne rss ?_⟩
    exact le_sound _ _ hle _ hw
  · cases h

variable {ranges : Array (Nat × Nat)} {st0 : LState}

/-- **Terminators** over the typed scope. -/
theorem termProgT (hP : PInvT f ctx) (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hdom : dominatedB f = true) (hin : iselInB f = true) (hdrv : driverInB f = true) :
    TermProg f ctx := by
  intro ti t data targets s _ hph hB _ hd hlen
  obtain ⟨q, hq, ⟨T, hT, hTid⟩, hγ⟩ := term_rootT hP hb hdom hin hdrv hph hB hd hlen
  obtain ⟨e, he, hos, hfu⟩ := termRoot_entryT hq
  have hP' := pinv_termCtxT hP hph data
  rw [← hTid] at he
  obtain ⟨w, s', tr, hrun, -⟩ := root_run (model_ofT hP') (handOk_prgTabT hP') prgTabT_ok hT he
    hos hfu hγ s
  exact ⟨w, s', tr, hrun⟩

/-- **`try_call`s** over the typed scope. -/
theorem tryProgT (hP : PInvT f ctx) (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hdom : dominatedB f = true) (hin : iselInB f = true) : TryProg f ctx := by
  intro ti t et data sig items trs st1 st2 targets s _ hph hB het hd hx hr hlen
  obtain ⟨q, hq, hq1, hγ⟩ := try_rootT hP hb hdom hin hph hB het hd hx hr hlen
  obtain ⟨e, he, hos, hfu⟩ := termRoot_entryT hq
  have hP' := pinv_tryCtxT hP hph data trs
  rw [hq1] at he
  obtain ⟨w, s', tr, hrun, -⟩ := root_run (model_ofT hP') (handOk_prgTabT hP') prgTabT_ok
    program_termByName_lower_branch (T := T.lower_branch) he hos hfu hγ s
  obtain ⟨c, hc⟩ := tryCall_lastT hP hB hd hph (trs := trs) (targets := targets) (s := s) hrun
  exact ⟨w, s', tr, c, hrun, hc⟩

/-- **The ISLE side of the driver's totality over the typed scope**, for input in scope. -/
theorem iselProgT_of_input (hdom : dominatedB f = true) (hs : LowerScopeT f)
    (hw : extendsWidenB f = true) (hin : iselInB f = true) (hdrv : driverInB f = true)
    (hb : buildCtx f = .ok (ctx, ranges, st0)) : IselProg f ctx :=
  have hP := pinv_buildT hdom hs hw hin hb
  ⟨stmtProgT hP, termProgT hP hb hdom hin hdrv, tryProgT hP hb hdom hin⟩

/-- **`lowerFunction` is total on input of the typed scope**: every premise is a conjunct of
`E2E.fnScopeInTB` (`hs` from `lowerScopeTB` by `E2E.LinkCheck.lowerScopeT_of`). -/
theorem lowerFunction_ok_inputT (hET : Compile.functionET f = true)
    (hsig : sigAbiOk f.sig = true) (hdom : dominatedB f = true) (hs : LowerScopeT f)
    (har : Spill.arityOkB f = true) (hent : Spill.entryParamsB f = true)
    (hw : extendsWidenB f = true) (hdrv : driverInB f = true) (hin : iselInB f = true) :
    ∃ vc, lowerFunction f = .ok vc :=
  lowerFunction_okT hET hsig hdom hs har hent hdrv fun _ _ _ hb =>
    iselProgT_of_input hdom hs hw hin hdrv hb

end Backend.Proof.Prg
