import FV.Backend.Proof.DefGenSoundAt
import FV.Backend.Proof.DefGenTab
import FV.Backend.Proof.KillDriver

/-!
# Definedness of the ISLE lowering: the driver's runs (`DefRunsHyp`)

The flow-sensitive abstract interpreter (`DefGen*`) instantiated for the three calls of the
driver, as `KillDriver.lean` does for the killed-vreg invariant. For a run reaching from the
values `S` and started at `s` the parameters are `sc ctx S s.nextVreg root`: fresh vregs from
`s.nextVreg`, the reached CLIF values `Reach ctx S`, the instructions defining them, and the root
instruction (the statement, resp. the terminator slot). The root arguments (`.inst root`,
`.labels targets`) fit the root summaries; the run keeps `IsD` (whence `RunDef`), and a
statement's result is clean (whence `OutDef`: its registers are vregs, of reached values or
defined by the run).

* `stmt_def`: a statement's `lower` (`nop`'s rule 587 by hand: it matches only an instruction
  without results; 636/637 never match);
* `term_def`: a terminator's run in `termCtx` (`lower` on `return`/`trap`, else `lower_branch`);
* `try_def`: a `try_call`'s `lower_branch` in `tryCtx` (the `try_call` registers are vregs).

`defRunsHyp_of` takes the generic soundness of a root term (`DRootHyp`, `DefGenSoundAt.dRoot`),
the decided tables (`TabHyp`, `DefGenTab`) and the model (`DModelHyp`, `DefGenModel.dModel`).
-/

namespace Backend.Proof.DefRun

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Spill Backend.Proof.Driver
  Backend.Proof.Kill Backend.Proof.DefGen Isle Isle.Interp Isle.Aarch64

/-! ## The deliverables the driver builds on -/

/-- The statement of `DefGen.dRoot` (`DefGenSoundAt.lean`): soundness of a root term. -/
def DRootHyp : Prop :=
  ∀ {p : Program} {ctx : Ctx} {c : SC} {s0 : LState} {T : TermId → Prop} {cfg : Config},
    DModel p ctx c s0 → TabOK p T → cfg.checkOverlap = false →
    ∀ (Q : LState → V → Prop) (Hand : Rule → Prop) (ins : List A) (out : A)
      {n : Nat} {ty : TypeId} {t : TermId} {term : Term} {flags : TermFlags}
      {ex : Option Extractor} {vs : List V},
    termOf p t = .ok term → term.kind = .decl flags (some .internal) ex →
    flags.isMulti = false →
    (∀ rl ∈ p.rulesOf t,
      ((∀ u ∈ ruleTerms rl, T u) ∧ aRule p ins out rl = true) ∨ Hand rl ∨
        ∀ m st env st1, (matchRule p (sem ctx) cfg m rl vs).run st ≠ .ok (some env, st1)) →
    (∀ rl ∈ p.rulesOf t, Hand rl →
      ∀ k m s tr env s1 tr1 r s2 tr2, n = k + 1 → m + 2 ≤ k →
        k ≤ m + 2 + (p.rulesOf t).length → (∀ env, γL c ins (Dn ctx c s0 s) env vs) →
        IsD ctx c s0 s →
        (matchRule p (sem ctx) cfg m rl vs).run (s, tr) = .ok (some env, (s1, tr1)) →
        (evalExpr p (sem ctx) cfg k rl.rhs env).run (s1, tr1) = .ok (r, (s2, tr2)) →
        IsD ctx c s0 s2 ∧ RsD s s2 ∧ ∀ v, r = some v → Q s2 v) →
    ∀ {s s' : LState} {tr tr' : Array RuleId} {r : Option V},
    (∀ env, γL c ins (Dn ctx c s0 s) env vs) → IsD ctx c s0 s →
    (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    IsD ctx c s0 s' ∧ RsD s s' ∧
      ∀ v, r = some v → (∃ env, γ c out (Dn ctx c s0 s') env v) ∨ Q s' v

/-- The decided tables (`DefGenTab.lean`: `tabOK`, `rootLower`, `rootBranch`). -/
def TabHyp : Prop :=
  TabOK program (· ∈ defTab) ∧
  (∀ rl ∈ program.rulesOf TId.lower, rl.id ≠ 587 → rl.id ≠ 636 → rl.id ≠ 637 →
    (∀ u ∈ ruleTerms rl, u ∈ defTab) ∧
      aRule program [.cl true false] (.cl false false) rl = true) ∧
  (∀ rl ∈ program.rulesOf TId.lower_branch,
    (∀ u ∈ ruleTerms rl, u ∈ defTab) ∧
      aRule program [.cl true false, .cl false false] (.cl false false) rl = true)

/-- The conditions of the model (`DefGenModel.dModel`) on a run's context `ctx` and
parameters `c`. -/
structure DCond (ctx : Ctx) (c : SC) : Prop where
  reg : ∀ x r, ctx.valueReg? x = some r → r = .vreg x .int
  regLt : ValRegK ctx
  root : ∀ info, ctx.insts[c.root]? = some info → DataOk c.R info.data
  inst : ∀ j info, c.I j → ctx.insts[j]? = some info →
    DataOk c.R info.data ∧ ∀ n ∈ info.results, c.R n
  defI : ∀ n j, c.R n → ctx.defInst? n = some j → c.I j
  args : ∀ n j info cl, c.R n → ctx.defInst? n = some j → ctx.insts[j]? = some info →
    info.clif = some cl → ∀ y ∈ Driver.instArgs cl, c.R y
  tryR : ∀ r ∈ ctx.tryRegs.1 ++ ctx.tryRegs.2, ∃ n cl, r = .vreg n cl

/-- The model (`DefGenModel.lean`: `dModel`). -/
def DModelHyp : Prop :=
  ∀ (ctx : Ctx) (c : SC) (s0 : LState), DCond ctx c → DModel program ctx c s0

/-! ## The parameters of a run -/

/-- The parameters of a run reaching from `S` (of context `ctx`), fresh vregs from `lo`. -/
def sc (ctx : Ctx) (S : List Nat) (lo root : Nat) : SC where
  lo := lo
  R := Reach ctx S
  I := fun j => ∃ n, Reach ctx S n ∧ ctx.defInst? n = some j
  root := root

theorem isD_start {ctx : Ctx} {c : SC} {s : LState} (h : c.lo ≤ s.nextVreg) : IsD ctx c s s :=
  ⟨⟨[], by simp, fun k m hm => by simp at hm⟩, h⟩

/-- **`RunDef` from the state invariant** (the run's context `ctx'` has `ctx`'s values). -/
theorem runDef_of {ctx ctx' : Ctx} {S : List Nat} {lo root : Nat} {s0 s : LState}
    (hlo : lo = s0.nextVreg) (hsz : ctx'.valDef.size = ctx.valDef.size)
    (h : IsD ctx' (sc ctx S lo root) s0 s) : RunDef ctx S s0 s := by
  obtain ⟨⟨ms, hms, hu⟩, -⟩ := h
  refine ⟨ms, hms, fun k m hm u hu' => ?_⟩
  rcases hu k m hm u hu' with ⟨h1, h2⟩ | ⟨h1, m', hm', h2⟩
  · exact .inl ⟨hsz ▸ h1, h2⟩
  · refine .inr ⟨hlo ▸ h1, ?_⟩
    obtain ⟨k', hk', he⟩ := List.getElem_of_mem hm'
    rw [List.length_take] at hk'
    refine ⟨k', m', by omega, ?_, h2⟩
    rw [← he, List.getElem_take]
    exact List.getElem?_eq_getElem _

/-- **`OutDef` from a clean result.** -/
theorem outDef_of {ctx ctx' : Ctx} {S : List Nat} {lo root : Nat} {s0 s : LState} {out : Option V}
    (hlo : lo = s0.nextVreg) (hsz : ctx'.valDef.size = ctx.valDef.size)
    (h : ∀ v, out = some v → ∃ env,
      γ (sc ctx S lo root) (.cl false false) (Dn ctx' (sc ctx S lo root) s0 s) env v) :
    OutDef ctx S s0 s out := by
  intro rss hout rs hrs r hr
  obtain ⟨env, hcl⟩ := h _ hout
  have hd := hcl.1 r (by simp only [regsU, List.mem_flatten]; exact ⟨rs, hrs, hr⟩)
  cases r
  case vreg n cl =>
    refine ⟨n, cl, rfl, ?_⟩
    rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨hsz ▸ h1, h2⟩
    · exact .inr ⟨hlo ▸ h1, h2⟩
  all_goals exact absurd hd.1 Bool.false_ne_true

theorem γ_root {c : SC} {D : Nat → Prop} {env : Isle.Interp.Env V} :
    γ c (.cl true false) D env (.inst c.root) :=
  ⟨by simp [regsU], by simp [V.valsIn], by simp [V.instsIn, IOk]⟩

theorem γ_labels {c : SC} {D : Nat → Prop} {env : Isle.Interp.Env V} {ls : List Label} :
    γ c (.cl false false) D env (.labels ls) :=
  ⟨by simp [regsU], by simp [V.valsIn], by simp [V.instsIn]⟩

theorem dataOk_mono {P P' : Nat → Prop} (hP : ∀ n, P n → P' n) {d : V} (h : DataOk P d) :
    DataOk P' d :=
  ⟨h.1, h.2.1, h.2.2.1, fun n hn => hP n (h.2.2.2 n hn)⟩

/-! ## The data of a terminator: its values are its operands -/

/-- `data_ok` with the terminator's operands. -/
macro "tdata_ok" : tactic => `(tactic| (
  unfold instDataV opcodeV
  repeat' first
    | with_reducible apply dataOk_mkVariant (by decide)
    | with_reducible exact dataOkL_nil
    | with_reducible apply dataOkL_cons
    | with_reducible exact dataOk_int
    | with_reducible exact dataOk_blockCalls
    | with_reducible exact dataOk_op rfl rfl
    | with_reducible apply dataOk_value
    | with_reducible apply dataOk_values
  all_goals first
    | trivial
    | (intro x hx; simp_all [Driver.termArgs]; done)
    | (intro x hx; simp [Driver.termArgs, hx]; done)
    | (intro x hx; simp only [List.mem_cons] at hx
       rcases hx with h | h <;> simp [Driver.termArgs, h]; done)
    | simp [Driver.termArgs]))

theorem termData_vals {t : Clif.Terminator} {d : V} (h : termData t = .ok d) :
    DataOk (· ∈ Driver.termArgs t) d := by
  cases t <;> simp only [termData] at h
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h)
    | (simp only [pure, Except.pure, Except.ok.injEq] at h
       subst h
       tdata_ok)

set_option maxRecDepth 20000 in
theorem tryCallData_vals {f : Clif.Function} {t : Clif.Terminator} {d : V}
    (h : tryCallData f t = .ok d) : DataOk (· ∈ Driver.termArgs t) d := by
  cases t <;> simp only [tryCallData] at h
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h; done)
    | skip
  all_goals
    rename_i et
    cases he : exnTableOpnd f et with
    | error e => rw [he] at h; cases h
    | ok q =>
      rw [he] at h
      obtain ⟨sig, items⟩ := q
      simp only [bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h; done)
        | (simp only [pure, Except.pure, Except.ok.injEq] at h
           subst h
           tdata_ok)

/-! ## The model's conditions in the driver's contexts -/

/-- **The model's conditions** for a run reaching from `S` in a context that is `ctx` up to its
placeholder slots and `try_call` registers (`ctx`, `termCtx`, `tryCtx`). -/
theorem dcond_of {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (hvr : ValRegK ctx)
    {insts' : Array IInfo} {trs' : List Reg × List Reg} {S : List Nat} {lo root : Nat}
    (hins : ∀ (j : Nat) (info : IInfo), ctx.insts[j]? = some info → info.clif.isSome = true →
      insts'[j]? = some info)
    (hroot : ∀ info, insts'[root]? = some info → DataOk (Reach ctx S) info.data)
    (htry : ∀ r ∈ trs'.1 ++ trs'.2, ∃ n cl, r = .vreg n cl) :
    DCond { ctx with insts := insts', tryRegs := trs' } (sc ctx S lo root) := by
  have hdef : ∀ n j, ctx.defInst? n = some j → ∃ info cl, ctx.insts[j]? = some info ∧
      info.clif = some cl ∧ insts'[j]? = some info := by
    intro n j hd
    obtain ⟨info, hi, -⟩ := hctx.defInst n j hd
    have hs := hctx.defClif n j info hd hi
    obtain ⟨cl, hcl⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨info, cl, hi, hcl, hins j info hi hs⟩
  refine ⟨hctx.valueReg, hvr, hroot, ?_, fun n j hn hd => ⟨n, hn, hd⟩, ?_, htry⟩
  · rintro j info ⟨n, hn, hd⟩ hj
    have hj : insts'[j]? = some info := hj
    obtain ⟨info0, cl, hi0, hcl, hj0⟩ := hdef n j hd
    rw [hj0] at hj
    cases hj
    exact ⟨dataOk_mono (fun y hy => Reach.dep hn hd hi0 hcl (.inl hy))
        (instData_ok (hctx.data j _ cl hi0 hcl)),
      fun y hy => Reach.dep hn hd hi0 hcl (.inr hy)⟩
  · intro n j info cl hn hd hj hcl y hy
    have hj : insts'[j]? = some info := hj
    have hd : ctx.defInst? n = some j := hd
    obtain ⟨info0, cl0, hi0, hcl0, hj0⟩ := hdef n j hd
    rw [hj0] at hj
    cases hj
    rw [hcl0] at hcl
    cases hcl
    exact Reach.dep hn hd hi0 hcl0 (.inl hy)

/-- A terminator context keeps the statements' slots. -/
theorem termCtx_keeps {ctx : Ctx} {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    (data : V) : ∀ (j : Nat) (info : IInfo), ctx.insts[j]? = some info → info.clif.isSome = true →
      (termCtx ctx ti data).insts[j]? = some info := by
  intro j info hj hs
  have hji : j ≠ ti := by
    rintro rfl
    rw [hph] at hj
    cases hj
    simp at hs
  rw [termCtx_insts_ne hji]
  exact hj

/-! ## The driver's calls -/

section Runs
variable (hroot : DRootHyp) (htab : TabHyp) (hmod : DModelHyp)
include hroot htab hmod

/-- **A statement's `lower` run.** -/
theorem stmt_def {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (hvr : ValRegK ctx)
    (htr : ctx.tryRegs = ([], [])) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst) {s : LState} {out : Option V}
    {s' : LState} {tr : List RuleId} (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) :
    RunDef ctx (instArgs inst) s s' ∧
      (info.results ≠ [] → OutDef ctx (instArgs inst) s s' out) := by
  have hC : DCond { ctx with insts := ctx.insts, tryRegs := ctx.tryRegs }
      (sc ctx (instArgs inst) s.nextVreg ii) :=
    dcond_of hctx hvr (fun _ _ h _ => h)
      (fun info' h' => by
        rw [hi] at h'
        cases h'
        exact dataOk_mono (fun y hy => Reach.seed hy) (instData_ok (hctx.data ii info inst hi hc)))
      (by rw [htr]; simp)
  have M : DModel program ctx (sc ctx (instArgs inst) s.nextVreg ii) s := hmod _ _ s hC
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  obtain ⟨hIs, -, hv⟩ := hroot (p := program) (T := (· ∈ defTab)) (cfg := {}) (vs := [.inst ii])
    M htab.1 rfl
    (fun _ _ => info.results = []) (fun rl => rl ∈ program.rulesOf TId.lower ∧ rl.id = 587)
    [.cl true false] (.cl false false) data_program.t686 term_686_kind rfl
    (fun rl hrl => by
      by_cases h587 : rl.id = 587
      · exact .inr (.inl ⟨hrl, h587⟩)
      by_cases h636 : rl.id = 636 ∨ rl.id = 637
      · exact .inr (.inr (lower_636_637_nomatch hctx hi hc hrl h636))
      · exact .inl (htab.2.1 rl hrl h587 (fun h => h636 (.inl h)) (fun h => h636 (.inr h))))
    (fun rl _ ⟨hrl, h587⟩ k m s1 tr1 env s2 tr2 r s3 tr3 _ _ _ _ hIs hm he => by
      obtain ⟨hs, -⟩ := Cov.matchRule_noIfLets (iflets_587 hrl h587) hm
      cases hs
      obtain ⟨rfl, -⟩ := nop_rhs Cov.totality hrl h587 _ rfl _ _ _ _ _ _ _ he
      exact ⟨hIs, RsD.refl _, fun _ _ => nop_match_results hctx hi hc hrl h587 hm⟩)
    (fun _ => ⟨γ_root, trivial⟩) (isD_start (Nat.le_refl _)) happ
  refine ⟨runDef_of rfl rfl hIs, fun hres => outDef_of (ctx' := ctx) (root := ii) rfl rfl
    fun v hv' => ?_⟩
  rcases hv v hv' with hp | hq
  · exact hp
  · exact absurd hq hres

/-- **A terminator's run** (in `termCtx`). -/
theorem term_def {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (hvr : ValRegK ctx)
    (htr : ctx.tryRegs = ([], [])) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator}
    (hty : t.isTry = false) {data : V} (hdat : termData (abiTerm f t) = .ok data)
    {targets : List Label} {s : LState} {out : Option V} {s' : LState} {tr : List RuleId}
    (h : termCallF ctx ti data t targets s = .ok (out, s', tr)) :
    RunDef ctx (termArgs (abiTerm f t)) s s' := by
  have hti : ti < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hph).1
  have hslot := termCtx_self hti data
  have hC : DCond { ctx with insts := (termCtx ctx ti data).insts, tryRegs := ctx.tryRegs }
      (sc ctx (termArgs (abiTerm f t)) s.nextVreg ti) :=
    dcond_of hctx hvr (termCtx_keeps hph data)
      (fun info h' => by
        rw [hslot] at h'
        cases h'
        exact dataOk_mono (fun y hy => Reach.seed hy) (termData_vals hdat))
      (by rw [htr]; simp)
  have M : DModel program (termCtx ctx ti data) (sc ctx (termArgs (abiTerm f t)) s.nextVreg ti) s :=
    hmod _ _ s hC
  have hIs0 : IsD (termCtx ctx ti data) (sc ctx (termArgs (abiTerm f t)) s.nextVreg ti) s s :=
    isD_start (Nat.le_refl _)
  unfold termCallF at h
  have hbranch : runTerm (termCtx ctx ti data) "lower_branch" [.inst ti, .labels targets] s =
      .ok (out, s', tr) → RunDef ctx (termArgs (abiTerm f t)) s s' := fun h => by
    obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
    rw [program_termByName_lower_branch] at ht
    cases ht
    exact runDef_of rfl rfl (hroot (p := program) (T := (· ∈ defTab)) (cfg := {})
      (vs := [.inst ti, .labels targets]) M htab.1 rfl
      (fun _ _ => False) (fun _ => False) [.cl true false, .cl false false] (.cl false false)
      data_program.t687 term_687_kind rfl (fun rl hrl => .inl (htab.2.2 rl hrl))
      (fun _ _ h => h.elim) (fun _ => ⟨γ_root, γ_labels, trivial⟩) hIs0 happ).1
  have hlower : retOrTrap (abiTerm f t) = true →
      runTerm (termCtx ctx ti data) "lower" [.inst ti] s = .ok (out, s', tr) →
      RunDef ctx (termArgs (abiTerm f t)) s s' := by
    intro hrt h
    obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
    rw [program_termByName_lower] at ht
    cases ht
    exact runDef_of rfl rfl (hroot (p := program) (T := (· ∈ defTab)) (cfg := {})
      (vs := [.inst ti]) M htab.1 rfl
      (fun _ _ => False) (fun _ => False) [.cl true false] (.cl false false)
      data_program.t686 term_686_kind rfl
      (fun rl hrl => by
        cases hr : termRootRule rl with
        | false => exact .inr (.inr (lower_term_nomatch hrt hdat hslot hrl hr))
        | true =>
          simp only [termRootRule, Bool.or_eq_true, beq_iff_eq] at hr
          exact .inl (htab.2.1 rl hrl (by rcases hr with h | h <;> simp [h])
            (by rcases hr with h | h <;> simp [h]) (by rcases hr with h | h <;> simp [h])))
      (fun _ _ h => h.elim) (fun _ => ⟨γ_root, trivial⟩) hIs0 happ).1
  cases t with
  | ret vs => exact hlower rfl h
  | trap c => exact hlower rfl h
  | jump bc => exact hbranch h
  | brif c a b => exact hbranch h
  | brTable x d tb => exact hbranch h
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hdat
  | tryCall fn args et => simp [Clif.Terminator.isTry] at hty
  | tryCallIndirect callee args et => simp [Clif.Terminator.isTry] at hty

/-- **A `try_call`'s `lower_branch` run** (in `tryCtx`: the `try_call` registers are vregs). -/
theorem try_def {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (hvr : ValRegK ctx)
    {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator}
    {et : Clif.ExnTable} {data : V} (hdat : tryCallData f t = .ok data) {sig : Clif.Signature}
    {items : List (Option Nat)} (he : exnTableOpnd f et = .ok (sig, items)) {lo st1 : LState}
    {trs : List Reg × List Reg} (htr : tryRegsOf sig lo = some (trs, st1)) {targets : List Label}
    {out : Option V} {s' : LState} {tr : List RuleId}
    (h : tryCallF ctx ti data trs targets { st1 with emitted := #[] } = .ok (out, s', tr)) :
    RunDef ctx (termArgs t) { st1 with emitted := #[] } s' := by
  have hti : ti < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hph).1
  have hslot := termCtx_self hti data
  have htrs : ∀ r ∈ trs.1 ++ trs.2, ∃ n cl, r = .vreg n cl := by
    obtain ⟨-, rfl, -⟩ := tryRegsOf_spec (exnTableOpnd_cc he) htr
    intro r hr
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with ⟨j, -, rfl⟩ | rfl | rfl
    all_goals exact ⟨_, _, rfl⟩
  have hC : DCond { ctx with insts := (termCtx ctx ti data).insts, tryRegs := trs }
      (sc ctx (termArgs t) st1.nextVreg ti) :=
    dcond_of hctx hvr (termCtx_keeps hph data)
      (fun info h' => by
        rw [hslot] at h'
        cases h'
        exact dataOk_mono (fun y hy => Reach.seed hy) (tryCallData_vals hdat))
      htrs
  have M : DModel program (tryCtx ctx ti data trs) (sc ctx (termArgs t) st1.nextVreg ti)
      { st1 with emitted := #[] } := hmod _ _ _ hC
  unfold tryCallF at h
  obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  exact runDef_of rfl rfl (hroot (p := program) (T := (· ∈ defTab)) (cfg := {})
    (vs := [.inst ti, .labels targets]) M htab.1 rfl
    (fun _ _ => False) (fun _ => False) [.cl true false, .cl false false] (.cl false false)
    data_program.t687 term_687_kind rfl (fun rl hrl => .inl (htab.2.2 rl hrl))
    (fun _ _ h => h.elim) (fun _ => ⟨γ_root, γ_labels, trivial⟩) (isD_start (Nat.le_refl _))
    happ).1

/-- **`DefRunsHyp`** from the generic soundness of a root term, the decided tables and the
model. -/
theorem defRunsHyp_of : DefRunsHyp := by
  intro f ctx ranges st0 _ hs _ hb
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
  have htr := (ctxFacts_of hb).tryRegs
  have hvr := valRegK_of_build hb
  exact ⟨fun ii info inst s out s' tr hi hc _ h => stmt_def hroot htab hmod hctx hvr htr hi hc h,
    fun ti t data targets s out s' tr _ hph hty _ hdat _ h =>
      term_def hroot htab hmod hctx hvr htr hph hty hdat h,
    fun ti t et data sig items lo trs st1 targets out s' tr _ hph _ _ hdat he _ htr h =>
      try_def hroot htab hmod hctx hvr hph hdat he htr h⟩

end Runs

/-! ## The deliverables -/

/-- The generic soundness of a root term (`DefGenSoundAt.lean`). -/
theorem dRootHyp : DRootHyp := @dRoot

/-- The decided tables (`DefGenTab.lean`). -/
theorem tabHyp : TabHyp := ⟨tabOK, rootLower, rootBranch⟩

/-- **`DefRunsHyp`** from the model. -/
theorem defRunsHyp_of_model (hmod : DModelHyp) : DefRunsHyp :=
  defRunsHyp_of dRootHyp tabHyp hmod

end Backend.Proof.DefRun
