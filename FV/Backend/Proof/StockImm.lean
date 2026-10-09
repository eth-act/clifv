import FV.Backend.Proof.IselScopedProjection
import FV.Backend.Proof.IselFlowGen
import FV.Backend.Proof.StockDFG
import FV.Backend.Proof.IselFamAluBIconst

/-!
Constant materialization runs through the actual stock embedding. Its reachable
constructors retain the legacy base-state behavior, so all five existing machine
semantics proofs apply without assuming source IDs equal register numbers.
No generated program is evaluated or unfolded in these proofs.
-/

namespace Backend.Stock.Proof

open Backend.Proof Isle Isle.Interp Isle.Aarch64

private def immScope : List Nat :=
  [164, 170, 172, 175, 201, 235, 305, 318, 319, 320, 321, 352, 358, 359, 360, 498, 553, 554,
    1823, 1844, 1964, 1989, 1990, 2028, 2029, 2235]

private theorem imm_scope {p : Program} (hp : Data p) (ctx : Ctx) :
    ProjectionScope p (Backend.sem ctx) State.base (Stock.externCtor ctx)
      (fun t => t ∈ immScope) := by
  constructor
  · intro t term hs ht vs st
    simp only [immScope, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp.t164] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t170] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t172] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t175] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t201] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t235] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t305] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t318] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t319] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t320] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t321] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t352] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t358] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t359] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t360] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t498] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t553] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t554] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1823] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1844] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1964] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1989] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1990] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t2028] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t2029] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t2235] at ht
      cases ht
      exact stock_ctor_unchanged ctx _ vs st (by decide)
  · intro t term hs ht flags ex hk r hr
    simp only [immScope, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp.t164] at ht
      cases ht
      cases hk
    · rw [hp.t170] at ht
      cases ht
      cases hk
    · rw [hp.t172] at ht
      cases ht
      rw [hp.r172] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls,
        immScope, rule_prelude_lower_105]
    · rw [hp.t175] at ht
      cases ht
      cases hk
    · rw [hp.t201] at ht
      cases ht
      cases hk
    · rw [hp.t235] at ht
      cases ht
      cases hk
    · rw [hp.t305] at ht
      cases ht
      rw [hp.r305] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls,
        immScope, rule_inst_1592, rule_inst_1593]
    · rw [hp.t318] at ht
      cases ht
      cases hk
    · rw [hp.t319] at ht
      cases ht
      cases hk
    · rw [hp.t320] at ht
      cases ht
      cases hk
    · rw [hp.t321] at ht
      cases ht
      cases hk
    · rw [hp.t352] at ht
      cases ht
      cases hk
    · rw [hp.t358] at ht
      cases ht
      rw [hp.r358] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls,
        immScope, rule_inst_2513]
    · rw [hp.t359] at ht
      cases ht
      rw [hp.r359] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls,
        immScope, rule_inst_2521]
    · rw [hp.t360] at ht
      cases ht
      rw [hp.r360] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls,
        immScope, rule_inst_2529]
    · rw [hp.t498] at ht
      cases ht
      rw [hp.r498] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls,
        immScope, rule_inst_3416]
    · rw [hp.t553] at ht
      cases ht
      rw [hp.r553] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls,
        immScope, rule_inst_3742, rule_inst_3745, rule_inst_3751, rule_inst_3786, rule_inst_3790]
    · rw [hp.t554] at ht
      cases ht
      cases hk
    · rw [hp.t1823] at ht
      cases ht
      cases hk
    · rw [hp.t1844] at ht
      cases ht
      cases hk
    · rw [hp.t1964] at ht
      cases ht
      cases hk
    · rw [hp.t1989] at ht
      cases ht
      cases hk
    · rw [hp.t1990] at ht
      cases ht
      cases hk
    · rw [hp.t2028] at ht
      cases ht
      cases hk
    · rw [hp.t2029] at ht
      cases ht
      cases hk

    · rw [hp.t2235] at ht
      cases ht
      cases hk

theorem stock_imm_projects {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (hc : cfg.checkOverlap = false) (n : Nat) (args : List V) :
    Projects State.base (applyTerm p (Stock.sem ctx) cfg n 27 553 args)
      (applyTerm p (Backend.sem ctx) cfg n 27 553 args) :=
  (evaluation_scoped_restate p (Backend.sem ctx) cfg hc State.base
    (Stock.externCtor ctx) (fun t v st => Backend.externExtract ctx t v st.base)
    (fun t => t ∈ immScope) (imm_scope hp ctx) (fun _ _ _ => rfl) n).term
    27 553 args (by decide)

theorem stock_imm_ok {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (hR : Refines F isem) {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    {e : Nat} (he : e = 0 ∨ e = 1) {i : Int} {st st' : State} {tr tr' : Array RuleId}
    {n : Nat} {v : V}
    (h : (applyTerm p (Stock.sem ctx) cfg (n + 40) 27 553 (immArgs w e i)).run (st, tr) =
      .ok (some v, st', tr')) : ImmOut F isem w e (u64 i) st.base st'.base v := by
  have hpj := stock_imm_projects hp ctx cfg hc (n + 40) (immArgs w e i) st tr
  rw [h] at hpj
  simp only [projectResult] at hpj
  exact imm_ok hp ctx hc hR hw he hpj.symm

private theorem legacy_imm_nine {p : Program} (hp : Data p) (ctx : Ctx) (st : LState) :
    ∃ st' tr',
      (applyTerm p (Backend.sem ctx) {} 2000 27 553 (immArgs 8 1 9)).run (st, #[]) =
        .ok (some (.reg (st.fresh .int).1), st', tr') := by
  have hm := match_3742 hp ctx (cfg := {}) st #[] 1987 (w := 8) (i := 9)
    (mw := ⟨9, 0⟩) (Or.inl rfl) rfl
  obtain ⟨tr', he⟩ := rhs_3742 hp ctx (cfg := {}) rfl st #[] 1969
    (w := 8) (i := 9) (mw := ⟨9, 0⟩) (by decide)
  cases hp
  refine ⟨(st.fresh .int).2.emit (.movWide .movZ (st.fresh .int).1 ⟨9, 0⟩ (szOf 8)),
    tr'.push rule_inst_3742.id, ?_⟩
  isel_eval [*, R.imm]

private theorem self_refines : Refines (fun _ => True) ispec :=
  fun _ _ _ _ w' _ h => ⟨w', h, SameWorld.refl _ _⟩

private theorem stock_imm_nine {p : Program} (hp : Data p) (ctx : Ctx) (st : State) :
    ∃ st' tr',
      (applyTerm p (Stock.sem ctx) {} 2000 27 553 (immArgs 8 1 9)).run (st, #[]) =
        .ok (some (.reg (st.base.fresh .int).1), st', tr') ∧
      ImmOut (fun _ => True) ispec 8 1 9 st.base st'.base (.reg (st.base.fresh .int).1) := by
  obtain ⟨base', trace, hlegacy⟩ := legacy_imm_nine hp ctx st.base
  have hpj := stock_imm_projects hp ctx {} rfl 2000 (immArgs 8 1 9) st #[]
  rw [hlegacy] at hpj
  cases hstock : (applyTerm p (Stock.sem ctx) {} 2000 27 553 (immArgs 8 1 9)).run (st, #[]) with
  | error e => simp only [hstock, projectResult] at hpj; cases hpj
  | ok result =>
    rcases result with ⟨v, st', tr'⟩
    simp only [hstock, projectResult, Except.ok.injEq, Prod.mk.injEq] at hpj
    obtain ⟨rfl, hbase, htrace⟩ := hpj
    exact ⟨st', tr', rfl, stock_imm_ok hp ctx rfl self_refines
      (n := 1960) (Or.inl rfl) (Or.inr rfl) hstock⟩

theorem stock_imm_projects_witness :
    ∃ st' tr',
      (applyTerm program (Stock.sem sinkCtx) {} 2000 27 553 (immArgs 8 1 9)).run (sinkState, #[]) =
        .ok (some (.reg (.vreg 194 .int)), st', tr') ∧
      projectResult State.base
        ((applyTerm program (Stock.sem sinkCtx) {} 2000 27 553 (immArgs 8 1 9)).run (sinkState, #[])) =
        (applyTerm program (Backend.sem sinkCtx) {} 2000 27 553 (immArgs 8 1 9)).run (sinkState.base, #[]) := by
  obtain ⟨st', tr', hstock, _⟩ := stock_imm_nine data_program sinkCtx sinkState
  exact ⟨st', tr', hstock, stock_imm_projects data_program sinkCtx {} rfl 2000 _ sinkState #[]⟩

theorem stock_imm_ok_witness :
    ∃ st' tr',
      (applyTerm program (Stock.sem sinkCtx) {} 2000 27 553 (immArgs 8 1 9)).run (sinkState, #[]) =
        .ok (some (.reg (.vreg 194 .int)), st', tr') ∧
      ImmOut (fun _ => True) ispec 8 1 9 sinkState.base st'.base (.reg (.vreg 194 .int)) :=
  stock_imm_nine data_program sinkCtx sinkState

private theorem iconst_scoped : RuleScoped (fun t => t ∈ immScope) rule_lower_53 := by
  simp [RuleScoped, IfLetsScoped, ExprScoped, rule_lower_53, exprCalls, argCalls, immScope]

private theorem immEvaluation {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (hc : cfg.checkOverlap = false) (n : Nat) :
    EvaluationScopedProjects p (Backend.sem ctx) cfg State.base (Stock.externCtor ctx)
      (fun t v st => Backend.externExtract ctx t v st.base) (fun t => t ∈ immScope) n :=
  evaluation_scoped_restate p (Backend.sem ctx) cfg hc State.base
    (Stock.externCtor ctx) (fun t v st => Backend.externExtract ctx t v st.base)
    (fun t => t ∈ immScope) (imm_scope hp ctx) (fun _ _ _ => rfl) n

private def frameCtor (ctx : Ctx) (t : Term) (args : List V) (st : State) :
    ExtResult (V × State) :=
  match Backend.externCtor ctx t args st.base with
  | .ok (v, base) => .ok (v, { st with base })
  | .fail => .fail
  | .unmodeled e => .unmodeled e

private def frameSem (ctx : Ctx) : Isle.Sem V State :=
  (Backend.sem ctx).restate (frameCtor ctx)
    (fun t v st => Backend.externExtract ctx t v st.base)

private def scheduling (st : State) : State := { st with base := default }

private theorem frame_presAt (p : Program) (ctx : Ctx) (cfg : Config) (n : Nat) :
    PresAt p (frameSem ctx) cfg (fun st next => scheduling next = scheduling st) n := by
  apply presAt (R := fun st next => scheduling next = scheduling st)
    (fun _ => rfl) (fun _ _ _ hab hbc => hbc.trans hab)
  intro term vs st v next h
  change frameCtor ctx term vs st = .ok (v, next) at h
  unfold frameCtor at h
  split at h
  · cases h
    rfl
  · cases h
  · cases h

private theorem imm_frame_scope {p : Program} (hp : Data p) (ctx : Ctx) :
    ProjectionScope p (frameSem ctx) id (Stock.externCtor ctx)
      (fun t => t ∈ immScope) := by
  refine ⟨?_, (imm_scope hp ctx).rules⟩
  intro t term hs ht vs st
  have hn : term.id ∉ revisedCtors := by
    simp only [immScope, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp.t164] at ht
      cases ht
      decide
    · rw [hp.t170] at ht
      cases ht
      decide
    · rw [hp.t172] at ht
      cases ht
      decide
    · rw [hp.t175] at ht
      cases ht
      decide
    · rw [hp.t201] at ht
      cases ht
      decide
    · rw [hp.t235] at ht
      cases ht
      decide
    · rw [hp.t305] at ht
      cases ht
      decide
    · rw [hp.t318] at ht
      cases ht
      decide
    · rw [hp.t319] at ht
      cases ht
      decide
    · rw [hp.t320] at ht
      cases ht
      decide
    · rw [hp.t321] at ht
      cases ht
      decide
    · rw [hp.t352] at ht
      cases ht
      decide
    · rw [hp.t358] at ht
      cases ht
      decide
    · rw [hp.t359] at ht
      cases ht
      decide
    · rw [hp.t360] at ht
      cases ht
      decide
    · rw [hp.t498] at ht
      cases ht
      decide
    · rw [hp.t553] at ht
      cases ht
      decide
    · rw [hp.t554] at ht
      cases ht
      decide
    · rw [hp.t1823] at ht
      cases ht
      decide
    · rw [hp.t1844] at ht
      cases ht
      decide
    · rw [hp.t1964] at ht
      cases ht
      decide
    · rw [hp.t1989] at ht
      cases ht
      decide
    · rw [hp.t1990] at ht
      cases ht
      decide
    · rw [hp.t2028] at ht
      cases ht
      decide
    · rw [hp.t2029] at ht
      cases ht
      decide
    · rw [hp.t2235] at ht
      cases ht
      decide
  change projectCtor id (Stock.externCtor ctx term vs st) = frameCtor ctx term vs st
  rw [stock_ctor_baseOnly _ _ _ _ hn]
  unfold frameCtor
  cases Backend.externCtor ctx term vs st.base with
  | ok pair => cases pair; rfl
  | fail => rfl
  | unmodeled e => rfl

private theorem immFrameEvaluation {p : Program} (hp : Data p) (ctx : Ctx)
    (cfg : Config) (hc : cfg.checkOverlap = false) (n : Nat) :
    EvaluationScopedProjects p (frameSem ctx) cfg id (Stock.externCtor ctx)
      (fun t v st => Backend.externExtract ctx t v st.base) (fun t => t ∈ immScope) n :=
  evaluation_scoped_restate p (frameSem ctx) cfg hc id
    (Stock.externCtor ctx) (fun t v st => Backend.externExtract ctx t v st.base)
    (fun t => t ∈ immScope) (imm_frame_scope hp ctx) (fun _ _ _ => rfl) n

/-- Matching the actual constant rule preserves all scheduling fields, even
when its if-let expressions are evaluated by the stock interpreter. -/
theorem stock_iconst_match_frame {p : Program} (hp : Data p) (ctx : Ctx)
    {cfg : Config} (hc : cfg.checkOverlap = false) {n : Nat} {vs : List V}
    {st next : State} {tr trace : Array RuleId} {out : Option (Isle.Interp.Env V)}
    (h : (matchRule p (Stock.sem ctx) cfg n rule_lower_53 vs).run (st, tr) =
      .ok (out, next, trace)) : next = { st with base := next.base } := by
  have hj := (immFrameEvaluation hp ctx cfg hc n).rule rule_lower_53 vs iconst_scoped st tr
  change projectResult id
      ((matchRule p (Stock.sem ctx) cfg n rule_lower_53 vs).run (st, tr)) =
    (matchRule p (frameSem ctx) cfg n rule_lower_53 vs).run (st, tr) at hj
  rw [h] at hj
  simp only [projectResult, id_eq] at hj
  have hf := (frame_presAt p ctx cfg n).mrule _ _ _ _ _ _ _ hj.symm
  have he := congrArg (fun s => { s with base := next.base }) hf
  simpa only [scheduling] using he

/-- Actual evaluation of the selected constant RHS preserves every scheduling
field. Only its legacy machine-code state can change. -/
theorem stock_iconst_rhs_frame {p : Program} (hp : Data p) (ctx : Ctx)
    {cfg : Config} (hc : cfg.checkOverlap = false) {n : Nat}
    {env : Isle.Interp.Env V} {st next : State} {tr trace : Array RuleId} {out : Option V}
    (h : (evalExpr p (Stock.sem ctx) cfg n rule_lower_53.rhs env).run (st, tr) =
      .ok (out, next, trace)) : next = { st with base := next.base } := by
  have hj := (immFrameEvaluation hp ctx cfg hc n).expr
    rule_lower_53.rhs env iconst_scoped.2 st tr
  change projectResult id
      ((evalExpr p (Stock.sem ctx) cfg n rule_lower_53.rhs env).run (st, tr)) =
    (evalExpr p (frameSem ctx) cfg n rule_lower_53.rhs env).run (st, tr) at hj
  rw [h] at hj
  simp only [projectResult, id_eq] at hj
  have hf := (frame_presAt p ctx cfg n).expr _ _ _ _ _ _ _ hj.symm
  have he := congrArg (fun s => { s with base := next.base }) hf
  simpa only [scheduling] using he

/-- The selected stock constant rule produces fresh code holding the source
constant under a mapped context. Input register numbering is unrestricted. -/
theorem stock_iconst_ok {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : MappedCtxInv f ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hic : info.clif = some inst)
    {cfg : Config} (hc : cfg.checkOverlap = false)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (hR : Refines F isem)
    {m n : Nat} (hm : 2 ≤ m) (hn : 50 ≤ n)
    {st s1 st' : State} {tr tr1 tr' : Array RuleId} {env' : Isle.Interp.Env V} {out : V}
    (hmatch : (matchRule p (Stock.sem ctx) cfg m rule_lower_53 [.inst ii]).run (st, tr) =
      .ok (some env', s1, tr1))
    (heval : (evalExpr p (Stock.sem ctx) cfg n rule_lower_53.rhs env').run (s1, tr1) =
      .ok (some out, st', tr')) :
    ∃ (ty : Clif.Ty) (imm : BitVec ty.width) (ms : List MInst) (d : Nat),
      inst = .iconst ty imm ∧ out = .regsVec [[.vreg d .int]] ∧
      CodeShape st.base st'.base ms d st.base.nextVreg ∧
      ∀ ρ, ∃ ρ', PRun F isem ms ρ ρ' ∧ VHolds ⟨ty, imm⟩ (ρ' d) := by
  have hmatch' := (immEvaluation hp ctx cfg hc m).rule rule_lower_53 [.inst ii]
    iconst_scoped st tr
  change projectResult State.base
      ((matchRule p (Stock.sem ctx) cfg m rule_lower_53 [.inst ii]).run (st, tr)) =
    (matchRule p (Backend.sem ctx) cfg m rule_lower_53 [.inst ii]).run (st.base, tr) at hmatch'
  rw [hmatch] at hmatch'
  simp only [projectResult] at hmatch'
  have heval' := (immEvaluation hp ctx cfg hc n).expr rule_lower_53.rhs env'
    iconst_scoped.2 s1 tr1
  change projectResult State.base
      ((evalExpr p (Stock.sem ctx) cfg n rule_lower_53.rhs env').run (s1, tr1)) =
    (evalExpr p (Backend.sem ctx) cfg n rule_lower_53.rhs env').run (s1.base, tr1) at heval'
  rw [heval] at heval'
  simp only [projectResult] at heval'
  have hmatch := hmatch'.symm
  have heval := heval'.symm
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 50 := ⟨n - 50, by omega⟩
  obtain ⟨info', fs, hi', hd⟩ := root_match_data hp ctx (r := rule_lower_53) rfl hp.t2482
    term_2482_kind hp.t2341 term_2341_kind (m := m' + 1) hmatch
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hic
  rw [hd] at hdat
  obtain ⟨hf, ho⟩ := instData_inv_names hdat
  rw [fb_variantNames_UnaryImm] at hf
  rw [fb_variantNames_Iconst] at ho
  have hnm : instNames inst = ("UnaryImm", "Iconst") :=
    Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  obtain ⟨ty, imm, rfl⟩ := fb_instNames_iconst hnm
  obtain ⟨hety, rfl⟩ := fb_instData_iconst hdat
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii info _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  have hhead : info.resTys.head? = some (.int ty.width) := by
    rw [hres]; simp [ofClif_int_width]
  have hw := eTy_width hety
  rw [match_53 hp ctx st.base tr m' hi hhead hd] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, hbase, htrace⟩ := hmatch
  rw [← hbase, ← htrace] at heval
  obtain ⟨v, s2, hA, hout⟩ := rhs_53_inv hp ctx hc st.base tr n' heval
  obtain ⟨ms, d, rfl, hsh, hrun⟩ :=
    imm_ok hp ctx hc hR (eTy_widths hety) (.inr rfl) (n := n' + 7) hA
  obtain ⟨rfl, hs'⟩ := hout _ rfl
  change st'.base = s2.1 at hs'
  rw [hs']
  refine ⟨ty, imm, ms, d, rfl, rfl, hsh, ?_⟩
  intro ρ
  obtain ⟨ρ', X, hr, hx, hX, -⟩ := hrun ρ
  refine ⟨ρ', hr, vholds_of_lo64 hw hx ?_⟩
  have hp64 : 2 ^ ty.width ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  rw [hX, fb_u64_imm64 hw, fb_u64_nat (by have := imm.isLt; omega),
    Nat.mod_eq_of_lt imm.isLt]

private theorem legacy_iconst_rhs_nine {p : Program} (hp : Data p) (ctx : Ctx) (st : LState) :
    ∃ st' tr',
      (evalExpr p (Backend.sem ctx) {} 2003 rule_lower_53.rhs (env2 (.ty (.int 8)) (.int 9))).run
        (st, #[]) = .ok (some (.regsVec [[(st.fresh .int).1]]), st', tr') := by
  obtain ⟨st', tr', he⟩ := legacy_imm_nine hp ctx st
  have ho := output_reg_run hp ctx (cfg := {}) rfl st' tr' 1992 (st.fresh .int).1
  cases hp
  refine ⟨st', tr'.push rule_prelude_lower_105.id, ?_⟩
  isel_eval [*, rule_lower_53]

private theorem stock_iconst_rhs_nine {p : Program} (hp : Data p) (ctx : Ctx) (st : State) :
    ∃ st' tr',
      (evalExpr p (Stock.sem ctx) {} 2003 rule_lower_53.rhs (env2 (.ty (.int 8)) (.int 9))).run
        (st, #[]) = .ok (some (.regsVec [[(st.base.fresh .int).1]]), st', tr') := by
  obtain ⟨base', trace, he⟩ := legacy_iconst_rhs_nine hp ctx st.base
  have hpj := (immEvaluation hp ctx {} rfl 2003).expr rule_lower_53.rhs
    (env2 (.ty (.int 8)) (.int 9)) iconst_scoped.2 st #[]
  change projectResult State.base
      ((evalExpr p (Stock.sem ctx) {} 2003 rule_lower_53.rhs
        (env2 (.ty (.int 8)) (.int 9))).run (st, #[])) = _ at hpj
  rw [he] at hpj
  cases hs : (evalExpr p (Stock.sem ctx) {} 2003 rule_lower_53.rhs
      (env2 (.ty (.int 8)) (.int 9))).run (st, #[]) with
  | error e => simp only [hs, projectResult] at hpj; cases hpj
  | ok result =>
    rcases result with ⟨out, st', tr'⟩
    simp only [hs, projectResult, Except.ok.injEq, Prod.mk.injEq] at hpj
    obtain ⟨rfl, _, _⟩ := hpj
    exact ⟨st', tr', rfl⟩

private theorem stock_iconst_match_nine {p : Program} (hp : Data p) (ctx : Ctx)
    (st : State) {info : IInfo} (hi : ctx.insts[0]? = some info)
    (hty : info.resTys.head? = some (.int 8))
    (hd : info.data = .data 152 35 [.data 151 57 [], .int 9]) :
    (matchRule p (Stock.sem ctx) {} 2 rule_lower_53 [.inst 0]).run (st, #[]) =
      .ok (some (env2 (.ty (.int 8)) (.int 9)), st, #[]) := by
  have h1 := ext_inst_data_value ctx st.base hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_u64_from_imm64 ctx st.base 9
  cases hp
  isel_eval [*, rule_lower_53, Stock.sem]
  rfl

set_option maxRecDepth 4096 in
theorem stock_iconst_ok_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (info : IInfo) (st' : State) (tr' : Array RuleId),
      MappedCtxInv f ctx ∧ ctx.valueReg? 2 = some (.vreg 193 .int) ∧
      ctx.insts[0]? = some info ∧ info.clif = some (.iconst .i8 9) ∧
      info.results = [2] ∧
      (matchRule program (Stock.sem ctx) {} 2 rule_lower_53 [.inst 0]).run (sinkState, #[]) =
        .ok (some (env2 (.ty (.int 8)) (.int 9)), sinkState, #[]) ∧
      (evalExpr program (Stock.sem ctx) {} 2003 rule_lower_53.rhs
        (env2 (.ty (.int 8)) (.int 9))).run (sinkState, #[]) =
        .ok (some (.regsVec [[.vreg 194 .int]]), st', tr') ∧
      (∃ (ty : Clif.Ty) (imm : BitVec ty.width) (ms : List MInst) (d : Nat),
        Clif.Inst.iconst .i8 9 = .iconst ty imm ∧ .regsVec [[.vreg 194 .int]] = V.regsVec [[.vreg d .int]] ∧
        CodeShape sinkState.base st'.base ms d sinkState.base.nextVreg ∧
        ∀ ρ, ∃ ρ', PRun (fun _ => True) ispec ms ρ ρ' ∧ VHolds ⟨ty, imm⟩ (ρ' d)) := by
  obtain ⟨_, _, hctx, hreg⟩ := buildCtx_mappedInv_witness
  let f := (fun {f : Clif.Function} {ctx : Ctx} (_ : MappedCtxInv f ctx) => f) hctx
  let ctx := (fun {f : Clif.Function} {ctx : Ctx} (_ : MappedCtxInv f ctx) => ctx) hctx
  have hctx' : MappedCtxInv f ctx := hctx
  let info := ctx.insts[0]!
  have hi : ctx.insts[0]? = some info := rfl
  have hic : info.clif = some (.iconst .i8 9) := rfl
  have hm := stock_iconst_match_nine data_program ctx sinkState hi rfl rfl
  obtain ⟨st', tr', he⟩ := stock_iconst_rhs_nine data_program ctx sinkState
  refine ⟨f, ctx, info, st', tr', hctx', hreg, hi, hic, rfl, hm, he, ?_⟩
  exact stock_iconst_ok data_program hctx' hi hic rfl self_refines (by decide) (by decide) hm he


/-- The actual driver's RHS fuel, rather than a reduced demonstration fuel. -/
private theorem legacy_imm_nine_large {p : Program} (hp : Data p) (ctx : Ctx) (st : LState) :
    ∃ st' tr',
      (applyTerm p (Backend.sem ctx) {} 999996 27 553 (immArgs 8 1 9)).run (st, #[]) =
        .ok (some (.reg (st.fresh .int).1), st', tr') := by
  have hm := match_3742 hp ctx (cfg := {}) st #[] 999983 (w := 8) (i := 9)
    (mw := ⟨9, 0⟩) (Or.inl rfl) rfl
  obtain ⟨tr', he⟩ := rhs_3742 hp ctx (cfg := {}) rfl st #[] 999965
    (w := 8) (i := 9) (mw := ⟨9, 0⟩) (by decide)
  cases hp
  refine ⟨(st.fresh .int).2.emit (.movWide .movZ (st.fresh .int).1 ⟨9, 0⟩ (szOf 8)),
    tr'.push rule_inst_3742.id, ?_⟩
  isel_eval [*, R.imm]

private theorem legacy_iconst_rhs_nine_large {p : Program} (hp : Data p) (ctx : Ctx) (st : LState) :
    ∃ st' tr',
      (evalExpr p (Backend.sem ctx) {} 999999 rule_lower_53.rhs (env2 (.ty (.int 8)) (.int 9))).run
        (st, #[]) = .ok (some (.regsVec [[(st.fresh .int).1]]), st', tr') := by
  obtain ⟨st', tr', he⟩ := legacy_imm_nine_large hp ctx st
  have ho := output_reg_run hp ctx (cfg := {}) rfl st' tr' 999988 (st.fresh .int).1
  cases hp
  refine ⟨st', tr'.push rule_prelude_lower_105.id, ?_⟩
  isel_eval [*, rule_lower_53]

theorem stock_iconst_rhs_nine_large {p : Program} (hp : Data p) (ctx : Ctx) (st : State) :
    ∃ st' tr',
      (evalExpr p (Stock.sem ctx) {} 999999 rule_lower_53.rhs (env2 (.ty (.int 8)) (.int 9))).run
        (st, #[]) = .ok (some (.regsVec [[(st.base.fresh .int).1]]), st', tr') := by
  obtain ⟨base', trace, he⟩ := legacy_iconst_rhs_nine_large hp ctx st.base
  have hpj := (immEvaluation hp ctx {} rfl 999999).expr rule_lower_53.rhs
    (env2 (.ty (.int 8)) (.int 9)) iconst_scoped.2 st #[]
  change projectResult State.base
      ((evalExpr p (Stock.sem ctx) {} 999999 rule_lower_53.rhs
        (env2 (.ty (.int 8)) (.int 9))).run (st, #[])) = _ at hpj
  rw [he] at hpj
  cases hs : (evalExpr p (Stock.sem ctx) {} 999999 rule_lower_53.rhs
      (env2 (.ty (.int 8)) (.int 9))).run (st, #[]) with
  | error e => simp only [hs, projectResult] at hpj; cases hpj
  | ok result =>
    rcases result with ⟨out, st', tr'⟩
    simp only [hs, projectResult, Except.ok.injEq, Prod.mk.injEq] at hpj
    obtain ⟨rfl, _, _⟩ := hpj
    exact ⟨st', tr', rfl⟩


theorem stock_iconst_rhs_nine_large_witness :
    ∃ st' tr',
      (evalExpr program (Stock.sem sinkCtx) {} 999999 rule_lower_53.rhs
        (env2 (.ty (.int 8)) (.int 9))).run (sinkState, #[]) =
          .ok (some (.regsVec [[.vreg 194 .int]]), st', tr') :=
  stock_iconst_rhs_nine_large data_program sinkCtx sinkState


theorem stock_iconst_match_frame_witness :
    ∃ ctx : Ctx,
      (matchRule program (Stock.sem ctx) {} 2 rule_lower_53 [.inst 0]).run (sinkState, #[]) =
        .ok (some (env2 (.ty (.int 8)) (.int 9)), sinkState, #[]) ∧
      sinkState = { sinkState with base := sinkState.base } := by
  obtain ⟨f, ctx, info, next, trace, _, _, _, _, _, hm, _⟩ := stock_iconst_ok_witness
  exact ⟨ctx, hm, stock_iconst_match_frame data_program ctx rfl hm⟩

/-- A real generated constant RHS emits code while preserving its incoming
aliases, demand counts, sink flags, colors and opportunistic definitions. -/
theorem stock_iconst_rhs_frame_witness :
    ∃ next trace,
      (evalExpr program (Stock.sem sinkCtx) {} 999999 rule_lower_53.rhs
        (env2 (.ty (.int 8)) (.int 9))).run (sinkState, #[]) =
        .ok (some (.regsVec [[.vreg 194 .int]]), next, trace) ∧
      next = { sinkState with base := next.base } ∧ next.alias = sinkState.alias := by
  obtain ⟨next, trace, h⟩ := stock_iconst_rhs_nine_large data_program sinkCtx sinkState
  have hf := stock_iconst_rhs_frame data_program sinkCtx rfl h
  refine ⟨next, trace, h, hf, ?_⟩
  rw [hf]


end Backend.Stock.Proof
