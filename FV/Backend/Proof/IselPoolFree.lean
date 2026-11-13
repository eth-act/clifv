import FV.Backend.Proof.IselPool
import FV.Backend.Proof.PoolRoots
import FV.Backend.Proof.PoolTabData
import FV.Backend.Proof.KillGen
import FV.Backend.Proof.KillTermIds
import FV.Backend.Proof.IselFlowT
import FV.Backend.Proof.IselExclTF
import FV.Backend.Proof.IselFloatConst
import FV.Backend.Proof.IselCtlRuleIds
import FV.Backend.Proof.IselCovDriver
import FV.Backend.Proof.LowerContractT
import FV.Backend.Proof.IselPrgMono

/-!
# The lowering of the float scope emits no literal-pool load (#1002)

`constant_f64`'s last rule (`inst.isle:4275`, `emit_u64_le_const`, #565) is the only builder of
a constant-pool entry, and the `f64const` rule of `lower` (`lower.isle:68`, id 585) the only
closure-root rule that reaches `constant_f64`. An `f64const` of the float scope
(`Compile.instETF`) is `Compile.f64PoolFree`, so one of `constant_f64`'s earlier rules matches
it. Hence no ISLE run of the driver over a float-capable context emits a literal-pool load:

* `poolModel`: the uniform invariant of ISLE runs (`Isle.Interp.UModel`, `KillGen.lean`) with
  the value predicate "no constant-pool entry" (`V.poolIn`) and the run relation `NoPoolSince`,
  on the term set `poolTab` (generated, untrusted; closed under `Isle.ruleTerms`, without
  `emit_u64_le_const`: `poolTab_closedB`, `poolTab_const`, kernel-checked);
* `constant_f64_noPool`: `constant_f64` of a pattern without literal pool commits one of its
  first four rules (first-match selection, `internal_first`), whose terms are in `poolTab`;
* `f64const_rhs_noPool`: rule 585's right-hand side on an `f64const` of the scope;
* `stmt_noPool`, `termCall_noPool`, `tryCall_noPool`: the driver's ISLE runs.
-/

namespace Backend.Proof.Pool

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

/-! ## The term set -/

/-- The terms of a rule are in `poolTab`. -/
def poolRuleOkB (rl : Rule) : Bool := (ruleTerms rl).all (poolTab.contains ·)

theorem poolTab_closedB : poolTab.all (fun t => (program.rulesOf t).all poolRuleOkB) = true := by
  simp only [poolTab, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

theorem poolTab_const : poolTab.contains TId.emit_u64_le_const = false := by decide +kernel

theorem poolTab_outputReg : poolTab.contains TId.output_reg = true := by decide +kernel

/-- Every root rule of `lower` is outside the closure, the `f64const` rule (585), or applies
terms of `poolTab`. -/
theorem poolRootS_ok : (program.rulesOf TId.lower).all
    (fun rl => !closureRootIds.contains rl.id || rl.id == 585 || poolRuleOkB rl) = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

theorem poolRootB_ok : (program.rulesOf TId.lower_branch).all poolRuleOkB = true := by
  rw [show TId.lower_branch = 687 from rfl, data_program.r687]
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

/-- `constant_f64`'s rules but the literal-pool one (401) apply terms of `poolTab`. -/
theorem poolRootF_ok : (program.rulesOf TId.constant_f64).all
    (fun rl => rl.id == poolRule || poolRuleOkB rl) = true := by
  rw [show TId.constant_f64 = 587 from rfl, program_rulesOf_587]
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

theorem poolRuleOk_of {rl : Rule} (h : poolRuleOkB rl = true) : ∀ u ∈ ruleTerms rl, u ∈ poolTab := by
  intro u hu
  simpa using List.all_eq_true.mp h u hu

theorem poolTab_closed : ∀ t ∈ poolTab, ∀ rl ∈ program.rulesOf t, ∀ u ∈ ruleTerms rl, u ∈ poolTab :=
  fun t ht rl hrl =>
    poolRuleOk_of (List.all_eq_true.mp (List.all_eq_true.mp poolTab_closedB t ht) rl hrl)

theorem poolTab_ne {t : TermId} (h : t ∈ poolTab) : t ≠ TId.emit_u64_le_const := by
  rintro rfl
  have := poolTab_const
  simp [h] at this

/-! ## The model -/

/-- **The pool-free model** of the driver's semantics in a context whose instruction data holds
no constant-pool entry, on `poolTab`. -/
def poolModel (ctx : Ctx) (hd : DataP ctx) : UModel program (sem ctx) where
  P := fun _ v => v.poolIn = false
  Is := fun _ => True
  Rs := NoPoolSince
  T := (· ∈ poolTab)
  C := fun _ _ => True
  O := fun _ => False
  rs_refl := noPool_refl
  rs_trans := fun _ _ _ => noPool_trans
  mono := fun _ _ _ _ _ _ h => h
  int := fun _ _ _ _ => by simp [sem, V.poolIn]
  bool := fun _ _ _ => by simp [sem, V.poolIn]
  prim := fun _ _ _ _ _ h => by
    obtain ⟨t, rfl⟩ := sem_prim_eq ctx h
    simp [V.poolIn]
  mkd := fun _ ty _ _ k vs _ _ _ _ _ hvs => by
    show (V.data ty k vs).poolIn = false
    rw [poolIn_data]
    exact poolInL_eq_false.mpr hvs
  un := fun _ _ _ _ _ _ _ _ _ _ _ hv hu => by
    have := sem_unData_eq ctx hu
    subst this
    rw [poolIn_data] at hv
    exact poolInL_eq_false.mp hv
  ext := fun s _ term _ _ _ _ v fs _ _ _ _ hv h =>
    externExtract_pool hd term v s fs (h : externExtract ctx term v s = .ok fs) hv
  ctor := fun s _ term _ _ _ vs v s' hT ht _ _ hvs h => by
    have hvs' : poolInL vs = false := poolInL_eq_false.mpr hvs
    refine ⟨?_, trivial, ctor_noPool ctx hvs' h⟩
    cases hv : v.poolIn with
    | false => rfl
    | true =>
      rw [CovT.sem_ctor] at h
      have := externCtor_pool ctx term vs s v s' h
        (by rw [Kill.termOf_id_eq ht]; exact poolTab_ne hT) hv
      rw [hvs'] at this
      cases this
  oracle := fun _ h => h.elim
  closed := fun t ht _ rl hrl => ⟨poolTab_closed t ht rl hrl, fun _ _ => trivial⟩

/-! ## First-match selection, any result -/

/-- **One step of an internal constructor with first-match selection**: no rule matched (no
value, state unchanged), or a rule of the term matched from the start state after rules that all
failed to match, and its right-hand side ran to the result (`internal_cases` with
`selectRule_some_first`). -/
theorem internal_first {W σ : Type} {p : Program} {sem : Isle.Sem W σ} {cfg : Config}
    (hc : cfg.checkOverlap = false) {n : Nat} {ty : TypeId} {t : TermId}
    {vs : List W} {term : Term} {flags : TermFlags} {ex : Option Extractor}
    (ht : termOf p t = .ok term) (hk : term.kind = .decl flags (some .internal) ex)
    (hm : flags.isMulti = false) {s s' : σ} {tr tr' : Array RuleId} {r : Option W}
    (h : (applyTerm p sem cfg (n + 1) ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    (r = none ∧ s' = s) ∨
    ∃ rl pre post, p.rulesOf t = pre ++ rl :: post ∧
      (∀ r' ∈ pre, ∃ m', n ≤ m' + 2 + (p.rulesOf t).length ∧
        ∃ s1, (matchRule p sem cfg m' r' vs).run (s, tr) = .ok (none, s1)) ∧
      ∃ m env s1 tr1 tr2, m + 2 ≤ n ∧ n ≤ m + 2 + (p.rulesOf t).length ∧
        (matchRule p sem cfg m rl vs).run (s, tr) = .ok (some env, (s1, tr1)) ∧
        (evalExpr p sem cfg n rl.rhs env).run (s1, tr1) = .ok (r, (s', tr2)) := by
  rw [applyTerm_internal_run ht hk hm] at h
  obtain ⟨⟨sel, ⟨s1, tr1⟩⟩, h1, h2⟩ := except_bind_eq_ok h
  cases sel with
  | none =>
    have := selectRule_none h1
    cases this
    simp only at h2
    split at h2
    · cases pure_ok h2; exact .inl ⟨rfl, rfl⟩
    · exact (throw_ok h2).elim
  | some re =>
    obtain ⟨rl, env⟩ := re
    obtain ⟨-, m, hmn, hnm, hmatch⟩ := selectRule_some_fuel hc h1
    obtain ⟨pre, post, hrs, hpre⟩ := selectRule_some_first hc h1
    simp only at h2
    obtain ⟨ev, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
    refine .inr ⟨rl, pre, post, hrs, hpre, m, env, s1, tr1, tr2, hmn, hnm, hmatch, ?_⟩
    cases ev with
    | some v =>
      obtain ⟨u, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
      have hf := fire_ok h5
      cases pure_ok h6
      simp only at hf
      subst hf
      exact h3
    | none => cases pure_ok h4; exact h3

/-- A match that returned keeps its result with more fuel (`monoAt`). -/
theorem matchRule_mono_le {W σ : Type} {p : Program} {sem : Isle.Sem W σ} {cfg : Config}
    {m m' : Nat} (hm : m ≤ m') {r : Rule} {vs : List W} {s : σ × Array RuleId}
    {res : Option (Isle.Interp.Env W) × (σ × Array RuleId)}
    (h : (matchRule p sem cfg m r vs).run s = .ok res) :
    (matchRule p sem cfg m' r vs).run s = .ok res := by
  induction hm with
  | refl => exact h
  | step _ ih => exact (monoAt _).mrule _ _ _ _ ih

/-! ## `constant_f64` without literal pool -/

section Const
variable {ctx : Ctx} {cfg : Config}

theorem rulesOf_587_length : (program.rulesOf 587).length = 5 := by
  rw [program_rulesOf_587]; rfl

set_option maxHeartbeats 8000000 in
/-- **`constant_f64`** (`inst.isle:4264-4276`) of a pattern that needs no literal pool
(`Compile.f64PoolFree`) emits no literal-pool load and returns no constant-pool entry: one of
its first four rules matches, so the literal-pool rule is not selected. -/
theorem constant_f64_noPool (hd : DataP ctx) (hc : cfg.checkOverlap = false) {i : Int}
    (hi0 : 0 ≤ i) (hi : i < 2 ^ 64)
    (hpf : u64 i = 0 ∨ (fpModImm? (u64 i) .size64).isSome = true ∨ u64 i < 2 ^ 32 ∨
      u64 i % 2 ^ 32 = 0)
    {n : Nat} {ty : TypeId} {s s' : LState} {tr tr' : Array RuleId} {r : Option V}
    (h : (applyTerm program (sem ctx) cfg (n + 1) ty 587 [.int i]).run (s, tr) =
      .ok (r, (s', tr'))) :
    NoPoolSince s s' ∧ ∀ v, r = some v → v.poolIn = false := by
  have hp' := data_program
  have hu64 : u64 i = i.toNat := by unfold u64; omega
  have hfirst := internal_first hc hp'.t587 term_587_kind rfl h
  have hlen := rulesOf_587_length
  rw [hlen] at hfirst
  clear h
  revert hpf
  rcases hfirst with ⟨rfl, rfl⟩ | ⟨rl, pre, post, hL, hpre, m, env, s1, tr1, tr2, -, -, hmatch,
    hrhs⟩
  · intro _
    exact ⟨noPool_refl _, fun v hv => by cases hv⟩
  · intro hpf
    have hrl : rl ∈ program.rulesOf 587 := by rw [hL]; simp
    have hne : rl.id ≠ poolRule := by
      intro hid
      revert hpf
      rw [program_rulesOf_587] at hL
      isel_rule_cases hL
      all_goals first
        | (exact absurd hid (by decide))
        | skip
      intro hpf
      have key : ∀ (r' : Rule),
          r' ∈ [rule_inst_4264, rule_inst_4268, rule_inst_4271, rule_inst_4273] →
          (∀ (k : Nat) (w : LState × Array RuleId),
            ∃ env, (matchRule program (sem ctx) cfg (k + 20) r' [.int i]).run w =
              .ok (some env, w)) → False := by
        intro r' hr' hsome
        obtain ⟨m', -, s1', hn'⟩ := hpre r' hr'
        have hn'' := matchRule_mono_le (Nat.le_add_right m' 20) hn'
        obtain ⟨env', he⟩ := hsome m' _
        rw [he] at hn''
        cases hn''
      rcases hpf with h0 | hfm | hlt | hlow
      · refine key rule_inst_4264 (by simp) fun k ⟨st0, tr0⟩ => ?_
        have hi0' : i = 0 := by omega
        subst hi0'
        isel_eval [rule_inst_4264, sem_eq, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq,
          exists_eq', exists_eq_left', true_and, and_true]
      · obtain ⟨mm, hmm⟩ := Option.isSome_iff_exists.mp hfm
        refine key rule_inst_4268 (by simp) fun k ⟨st0, tr0⟩ => ?_
        have hctor : externCtor ctx T.asimd_fp_mod_imm_from_u64 [.int i, .data 95 3 []] st0 =
            .ok (.op (.fpModImm mm), st0) := by
          show (match (fpModImm? (u64 i) .size64).map (V.op ∘ Opnd.fpModImm) with
            | some v => ExtResult.ok (v, st0) | none => ExtResult.fail) = _
          rw [hmm]; rfl
        isel_eval [rule_inst_4268, hctor, hp'.t679, hp'.t2035, Except.ok.injEq, Prod.mk.injEq,
          Option.some.injEq, exists_eq', exists_eq_left', true_and, and_true]
      · refine key rule_inst_4271 (by simp) fun k ⟨st0, tr0⟩ => ?_
        have hx2 : externExtract ctx T.u32_from_u64 (.int i) st0 = .ok [.int i] :=
          (ext_u32_from_u64_iff ctx _ _ _).mpr ⟨⟨hi0, by omega⟩, rfl⟩
        isel_eval [rule_inst_4271, hx2, hp'.t1541, Except.ok.injEq, Prod.mk.injEq,
          Option.some.injEq, exists_eq', exists_eq_left', true_and, and_true]
      · refine key rule_inst_4273 (by simp) fun k ⟨st0, tr0⟩ => ?_
        have hx1 : externExtract ctx T.u64_low32_bits_unset (.int i) st0 = .ok [.int i] :=
          (ext_u64_low32_bits_unset_iff ctx _ _ _).mpr ⟨hlow, rfl⟩
        isel_eval [rule_inst_4273, hx1, hp'.t588, Except.ok.injEq, Prod.mk.injEq,
          Option.some.injEq, exists_eq', exists_eq_left', true_and, and_true]
    have hok := List.all_eq_true.mp poolRootF_ok rl hrl
    have hb : (rl.id == poolRule) = false := by simpa using hne
    rw [hb, Bool.false_or] at hok
    have hT := poolRuleOk_of hok
    obtain ⟨hIs1, r1, he1⟩ := (uSoundAt (poolModel ctx hd) hc m).mrule rl [.int i] s tr env s1 tr1
      hT (fun _ _ => trivial)
      (fun v hv => by
        simp only [List.mem_singleton] at hv
        subst hv
        exact (poolIn_int : (V.int i).poolIn = false)) trivial hmatch
    obtain ⟨-, r2, hv2⟩ := (uSoundAt (poolModel ctx hd) hc n).expr rl.rhs env s1 tr1 r s' tr2
      (ruleTerms_rhs hT) (ruleTys_rhs (C := fun _ _ => True) (fun _ _ => trivial)) he1 hIs1 hrhs
    exact ⟨noPool_trans r1 r2, hv2⟩

end Const

/-! ## The `f64const` rule -/

theorem mem_lower_68 : rule_lower_68 ∈ program.rulesOf TId.lower :=
  List.mem_iff_getElem?.mpr ⟨175, by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl⟩

set_option maxHeartbeats 8000000 in
/-- **Rule 585** (`lower.isle:68`, `f64const`) on an instruction of a float-capable context whose
instructions are in the float scope: its right-hand side `(output_reg (constant_f64 n))` emits no
literal-pool load, the literal's bits `n` being `Compile.f64PoolFree`. -/
theorem f64const_rhs_noPool {f : Clif.Function} {ctx : Ctx} {cfg : Config} (hctx : CtxInvT f ctx)
    (hsc : InstScopeTF ctx) (hd : DataP ctx) (hco : cfg.checkOverlap = false) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {m k : Nat} {s s1 s2 : LState} {tr tr1 tr2 : Array RuleId}
    {env : Interp.Env V} {r : Option V}
    (hm : (matchRule program (sem ctx) cfg m rule_lower_68 [.inst ii]).run (s, tr) =
      .ok (some env, (s1, tr1)))
    (he : (evalExpr program (sem ctx) cfg k rule_lower_68.rhs env).run (s1, tr1) =
      .ok (r, (s2, tr2))) : NoPoolSince s s2 := by
  have hp := data_program
  obtain ⟨hs, -⟩ := Cov.matchRule_noIfLets (ctx := ctx) (cfg := cfg)
    (r := rule_lower_68) rfl hm
  cases hs
  have hm' := matchRule_mono_le (m := m) (m' := (m + 20) + 1) (by omega) hm
  clear hm
  obtain ⟨info', fs, hi', hdat⟩ := root_match_data hp ctx (r := rule_lower_68) rfl hp.t2481
    term_2481_kind hp.t2344 term_2344_kind (m := m + 20) hm'
  rw [hi] at hi'
  cases hi'
  have hdd := hctx.data ii info inst hi hc
  rw [hdat] at hdd
  obtain ⟨imm, rfl, rfl⟩ := instData_f64const_inv hdd
  have hpf := f64PoolFreeInst_of_instETF (hsc ii info _ hi hc) .f64 imm rfl rfl
  have henv : env[0]? = some (some (.int (imm.toNat : Int))) := by
    isel_inv' hp [] at hm'
    obtain ⟨rfl, rfl⟩ := fconst_data_eq hi hdat ‹ctx.insts[ii]? = some _› ‹V.data 152 34 _ = _›
    have hfs := (ext_u64_from_ieee64_iff ctx _ _ _).mp ‹externExtract ctx T.u64_from_ieee64 _ _ = _›
    simp only [List.cons.injEq, and_true] at hfs
    subst hfs
    simp
  clear hm'
  have hlt := imm.isLt
  have h64 : imm.toNat < 2 ^ 64 := by simpa using hlt
  have hu : u64 (imm.toNat : Int) = imm.toNat := by unfold u64; omega
  have he1 : (evalExpr program (sem ctx) cfg k (.term 25 172 [.term 27 587 [.var 4 0]]) env).run
      (s, tr) = .ok (r, (s2, tr2)) := he
  clear he
  -- a run that returns has the fuel of every nested step
  cases k with
  | zero => rw [evalExpr.eq_1] at he1; exact (throw_ok he1).elim
  | succ k =>
  rw [evalExpr.eq_7] at he1
  obtain ⟨o, ⟨sa, tra⟩, h1, h2⟩ := bind_ok he1
  cases k with
  | zero => rw [evalArgs.eq_1] at h1; exact (throw_ok h1).elim
  | succ k =>
  rw [evalArgs.eq_3] at h1
  obtain ⟨o1, ⟨sb, trb⟩, h3, h4⟩ := bind_ok h1
  cases k with
  | zero => rw [evalExpr.eq_1] at h3; exact (throw_ok h3).elim
  | succ k =>
  rw [evalExpr.eq_7] at h3
  obtain ⟨o2, ⟨sc, trc⟩, h5, h6⟩ := bind_ok h3
  cases k with
  | zero => rw [evalArgs.eq_1] at h5; exact (throw_ok h5).elim
  | succ k =>
  cases k with
  | zero =>
    rw [evalArgs.eq_3] at h5
    obtain ⟨_, _, h5a, -⟩ := bind_ok h5
    rw [evalExpr.eq_1] at h5a
    exact (throw_ok h5a).elim
  | succ k =>
  have hargs : (evalArgs program (sem ctx) cfg ((k + 1) + 1) [.var 4 0] env).run (s, tr) =
      .ok (some [.int (imm.toNat : Int)], (s, tr)) :=
    evalArgs_cons_iff.mpr ⟨_, (s, tr), [], evalExpr_var_iff.mpr ⟨henv, rfl⟩,
      evalArgs_nil_iff.mpr ⟨rfl, rfl⟩, rfl⟩
  rw [hargs] at h5
  cases h5
  have h6' : (applyTerm program (sem ctx) cfg ((k + 1) + 1) 27 587 [.int (imm.toNat : Int)]).run
      (s, tr) = .ok (o1, (sb, trb)) := h6
  obtain ⟨hR1, hv1⟩ := constant_f64_noPool hd hco (i := (imm.toNat : Int)) (by omega) (by omega)
    (by rw [hu]; exact hpf) h6'
  cases o1 with
  | none =>
    cases pure_ok h4
    cases pure_ok h2
    exact hR1
  | some w =>
    obtain ⟨o3, ⟨sd, trd⟩, h7, h8⟩ := bind_ok h4
    rw [evalArgs.eq_2] at h7
    cases pure_ok h7
    cases pure_ok h8
    have hT172 : (172 : TermId) ∈ poolTab := by simpa using poolTab_outputReg
    obtain ⟨-, hR2, -⟩ := uSound (poolModel ctx hd) hco _ _ _ _ _ _ _ _ _
      hT172 trivial
      (fun v hv => by simp only [List.mem_singleton] at hv; subst hv; exact hv1 _ rfl) trivial h2
    exact noPool_trans hR1 hR2

/-! ## The driver's runs -/

section Runs
variable {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
include hctx

/-- **A statement's `lower` run** over a float-capable context whose instructions are in the
float scope emits no literal-pool load. -/
theorem stmt_noPool (hsc : InstScopeTF ctx) (hnm : LowerNoMatch ctx) (hd : DataP ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {s : LState} {out : Option V} {s' : LState} {tr : List RuleId}
    (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) : NoPoolSince s s' := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      ((∀ u ∈ ruleTerms rl, (poolModel ctx hd).T u) ∧
          ∀ q ∈ ruleTys rl, (poolModel ctx hd).C q.1 q.2) ∨
        (rl ∈ program.rulesOf TId.lower ∧ rl.id = 585) ∨
        ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠
          .ok (some env, s1) := by
    intro rl hrl
    have hok := List.all_eq_true.mp poolRootS_ok rl hrl
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hok
    rcases hok with (hcr | h585) | hok
    · exact .inr (.inr (hnm ii info inst hi hc rl hrl hcr {}))
    · exact .inr (.inl ⟨hrl, h585⟩)
    · exact .inl ⟨poolRuleOk_of hok, fun _ _ => trivial⟩
  exact (uRoot (poolModel ctx hd) rfl (fun _ _ => True)
    (fun rl => rl ∈ program.rulesOf TId.lower ∧ rl.id = 585) data_program.t686 term_686_kind rfl
    hrules
    (fun rl _ ⟨hrl, h585⟩ k m s0 tr0 env s1 tr1 r s2 tr2 _ _ _ _ _ hm he => by
      have hr : rl = rule_lower_68 :=
        eq_of_mem_of_id lower_ids_nodup hrl mem_lower_68 (by rw [h585]; rfl)
      subst hr
      exact ⟨trivial, f64const_rhs_noPool hctx hsc hd rfl hi hc hm he, fun _ _ => trivial⟩)
    (fun v hv => by
      simp only [List.mem_singleton] at hv
      subst hv
      exact (rfl : (V.inst ii).poolIn = false))
    trivial happ).2.1

omit hctx in
/-- **A `lower_branch` run** in a context whose instruction data holds no constant-pool entry
emits no literal-pool load. -/
theorem branch_noPool {ctx : Ctx} (hd : DataP ctx) {ti : Nat} {targets : List Label} {s : LState}
    {out : Option V} {s' : LState} {tr : List RuleId}
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr)) :
    NoPoolSince s s' := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  exact (uRoot (poolModel ctx hd) rfl (fun _ _ => False) (fun _ => False) data_program.t687
    term_687_kind rfl
    (fun rl hrl => .inl ⟨poolRuleOk_of (List.all_eq_true.mp poolRootB_ok rl hrl),
      fun _ _ => trivial⟩)
    (fun _ _ h => h.elim)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact (rfl : (V.inst ti).poolIn = false)
      · exact (rfl : (V.labels targets).poolIn = false))
    trivial happ).2.1

omit hctx in
/-- **A terminator's run** (at its placeholder slot) emits no literal-pool load. -/
theorem termCall_noPool {ctx : Ctx} (hd : DataP ctx) {ti : Nat} (hti : ti < ctx.insts.size)
    {t : Clif.Terminator} {data : V} (hdat : termData (abiTerm f t) = .ok data)
    {targets : List Label} {s : LState} {out : Option V} {s' : LState} {tr : List RuleId}
    (h : termCallF ctx ti data t targets s = .ok (out, s', tr)) : NoPoolSince s s' := by
  have hslot := termCtx_self hti data
  have hd' : DataP (termCtx ctx ti data) := dataP_termCtx hd (termData_poolIn hdat) ti
  unfold termCallF at h
  have hlower : retOrTrap (abiTerm f t) = true →
      runTerm (termCtx ctx ti data) "lower" [.inst ti] s = .ok (out, s', tr) →
      NoPoolSince s s' := by
    intro hrt h
    obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
    rw [program_termByName_lower] at ht
    cases ht
    have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
        ((∀ u ∈ ruleTerms rl, (poolModel _ hd').T u) ∧
            ∀ q ∈ ruleTys rl, (poolModel _ hd').C q.1 q.2) ∨ False ∨
          ∀ m s0 env s1, (matchRule program (sem (termCtx ctx ti data)) {} m rl [.inst ti]).run s0 ≠
            .ok (some env, s1) := by
      intro rl hrl
      cases hroot : termRootRule rl with
      | false => exact .inr (.inr (lower_term_nomatch hrt hdat hslot hrl hroot))
      | true =>
        have hok := List.all_eq_true.mp poolRootS_ok rl hrl
        simp only [termRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
        rcases hroot with h1 | h1 <;> rw [h1] at hok <;>
          exact .inl ⟨poolRuleOk_of (by simpa (config := { decide := true }) using hok),
            fun _ _ => trivial⟩
    exact (uRoot (poolModel _ hd') rfl (fun _ _ => False) (fun _ => False) data_program.t686
      term_686_kind rfl hrules (fun _ _ h => h.elim)
      (fun v hv => by
        simp only [List.mem_singleton] at hv
        subst hv
        exact (rfl : (V.inst ti).poolIn = false))
      trivial happ).2.1
  cases t with
  | ret vs => exact hlower rfl h
  | trap c => exact hlower rfl h
  | jump bc => exact branch_noPool hd' h
  | brif c a b => exact branch_noPool hd' h
  | brTable x d tb => exact branch_noPool hd' h
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hdat
  | tryCall fn args et => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hdat
  | tryCallIndirect callee args et =>
    simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hdat

omit hctx in
/-- **A `try_call`'s run** (`lower_branch` at its placeholder slot) emits no literal-pool load. -/
theorem tryCall_noPool {ctx : Ctx} (hd : DataP ctx) {ti : Nat} {t : Clif.Terminator} {data : V}
    (hdat : tryCallData f t = .ok data) {trs : List Reg × List Reg} {targets : List Label}
    {s : LState} {out : Option V} {s' : LState} {tr : List RuleId}
    (h : tryCallF ctx ti data trs targets s = .ok (out, s', tr)) : NoPoolSince s s' := by
  unfold tryCallF at h
  exact branch_noPool (dataP_tryCtx hd (tryCallData_poolIn hdat) ti trs) h

end Runs

end Backend.Proof.Pool
