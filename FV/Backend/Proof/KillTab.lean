import FV.Backend.Proof.KillGen
import FV.Backend.Proof.IselFlow
import FV.Backend.Proof.IselShpOracle

/-!
# Killed vregs of the ISLE lowering (V4, `SpillKillFree`): the rule-data facts

The terms the uniform invariant (`KillGen`) runs over: `killTabS` (reachable through
`Isle.ruleTerms` from the rules of `lower` other than `nop`'s 587 and the I128 rules 636, 637)
and `killTabB` (from the rules of `lower_branch`), not descending into the black-box oracle
terms `killOracles` (`atomic_rmw_loop`, `atomic_cas_loop`, `br_table_impl`, the only builders of
`AtomicRMWLoop`/`AtomicCASLoop`/`JTSequence` data). Decided over the exported rule data:

* closure under the rules of the non-oracle terms, and of the root rules;
* no call site builds `MInst` data of a variant with killed defs (`killCall`, for the call
  site's type, which is the type `applyTerm` gives the data);
* no variant term of those three variants and no `invalid_reg` in either set, no `gen_call_rets`
  in `killTabB`.

Plus the excluded root rules: 636, 637 never match a statement (`lower_636_637_nomatch`), and
`nop`'s right-hand side keeps the state and returns `[[Reg.invalid]]` (`nop_rhs`).
-/

namespace Backend.Proof.Kill

open Backend Backend.Proof Isle Isle.Interp Isle.Aarch64

/-! ## The term sets -/

set_option maxRecDepth 100000

/-- The black-box oracle terms: the only builders of data with killed defs. -/
def killOracles : List TermId := [TId.atomic_rmw_loop, TId.atomic_cas_loop, TId.br_table_impl]

/-- Worklist closure under `Isle.ruleTerms` of the non-oracle terms (`k`: fuel; the closure
property is decided afterwards, so running out of fuel is harmless). -/
def killClose : Nat → List TermId → Std.HashSet TermId → Std.HashSet TermId
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | k + 1, t :: ts, seen =>
    if seen.contains t then killClose k ts seen
    else if killOracles.contains t then killClose k ts (seen.insert t)
    else killClose k ((program.rulesOf t).flatMap ruleTerms ++ ts) (seen.insert t)

/-- The excluded root rules of `lower`: `nop` (587, hand-checked) and the I128 rules 636, 637
(never match). -/
def killExcl : List RuleId := [587, 636, 637]

/-- The terms the statement root rules apply. -/
def killRootsS : List TermId :=
  ((program.rulesOf TId.lower).filter fun r => !killExcl.contains r.id).flatMap ruleTerms

/-- The terms the branch root rules apply. -/
def killRootsB : List TermId := (program.rulesOf TId.lower_branch).flatMap ruleTerms

/-- **The terms of statement runs** (and the oracles). -/
def killTabS : List TermId := (killClose 10000000 (killOracles ++ killRootsS) {}).toList

/-- **The terms of branch runs** (and the oracles). -/
def killTabB : List TermId := (killClose 10000000 (killOracles ++ killRootsB) {}).toList

/-! ## The call-site condition -/

/-- A call site `(ty, t)` does not build `MInst` data of a variant with killed defs. -/
def killCall (ty : TypeId) (t : TermId) : Prop :=
  ∀ term k, termOf program t = .ok term → term.kind = .enumVariant k →
    ¬(ty = tyMInst ∧ isKVariant k = true)

/-- `killCall`, decided. -/
def killCallB (ty : TypeId) (t : TermId) : Bool :=
  match program.term? t with
  | some term =>
    match term.kind with
    | .enumVariant k => !(ty == tyMInst && isKVariant k)
    | _ => true
  | none => true

theorem termOf_program_eq {t : TermId} {term : Term} (h : termOf program t = .ok term) :
    program.term? t = some term := by
  unfold termOf at h
  split at h
  · rename_i term' h'
    cases h
    exact h'
  · cases h

theorem killCall_of {ty : TypeId} {t : TermId} (h : killCallB ty t = true) : killCall ty t := by
  intro term k ht hk ⟨hty, hkv⟩
  rw [killCallB, termOf_program_eq ht] at h
  simp [hk, hty, hkv] at h

/-- A rule's terms are in `L` and its call sites are allowed. -/
def ruleOkB (L : List TermId) (rl : Rule) : Bool :=
  (ruleTerms rl).all (L.contains ·) && (ruleTys rl).all fun q => killCallB q.1 q.2

theorem ruleOk_of {L : List TermId} {rl : Rule} (h : ruleOkB L rl = true) :
    (∀ u ∈ ruleTerms rl, u ∈ L) ∧ ∀ q ∈ ruleTys rl, killCall q.1 q.2 := by
  simp only [ruleOkB, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨fun u hu => by simpa using h.1 u hu, fun q hq => killCall_of (h.2 q hq)⟩

/-- Closure of `L` under the rules of its non-oracle terms. -/
def tabOkB (L : List TermId) : Bool :=
  L.all fun t => killOracles.contains t || (program.rulesOf t).all (ruleOkB L)

theorem closed_of {L : List TermId} (h : tabOkB L = true) :
    ∀ t ∈ L, t ∉ killOracles → ∀ rl ∈ program.rulesOf t,
      (∀ u ∈ ruleTerms rl, u ∈ L) ∧ ∀ q ∈ ruleTys rl, killCall q.1 q.2 := by
  intro t ht ho rl hrl
  have h1 := List.all_eq_true.mp h t ht
  have ho' : killOracles.contains t = false := by simpa using ho
  rw [ho', Bool.false_or] at h1
  exact ruleOk_of (List.all_eq_true.mp h1 rl hrl)

theorem tabOkB_S : tabOkB killTabS = true := by native_decide

theorem tabOkB_B : tabOkB killTabB = true := by native_decide

/-- **`killTabS` is closed** under the rules of its non-oracle terms, whose call sites are
allowed. -/
theorem killTabS_closed : ∀ t ∈ killTabS, t ∉ killOracles → ∀ rl ∈ program.rulesOf t,
    (∀ u ∈ ruleTerms rl, u ∈ killTabS) ∧ ∀ q ∈ ruleTys rl, killCall q.1 q.2 :=
  closed_of tabOkB_S

/-- **`killTabB` is closed** under the rules of its non-oracle terms, whose call sites are
allowed. -/
theorem killTabB_closed : ∀ t ∈ killTabB, t ∉ killOracles → ∀ rl ∈ program.rulesOf t,
    (∀ u ∈ ruleTerms rl, u ∈ killTabB) ∧ ∀ q ∈ ruleTys rl, killCall q.1 q.2 :=
  closed_of tabOkB_B

theorem rootS_ok : (program.rulesOf TId.lower).all
    (fun rl => killExcl.contains rl.id || ruleOkB killTabS rl) = true := by native_decide

theorem rootB_ok : (program.rulesOf TId.lower_branch).all (ruleOkB killTabB) = true := by
  native_decide

/-- **The statement root rules** (but 587, 636, 637) apply terms of `killTabS` at allowed call
sites. -/
theorem killRootS : ∀ rl ∈ program.rulesOf TId.lower, rl.id ≠ 587 → rl.id ≠ 636 → rl.id ≠ 637 →
    (∀ u ∈ ruleTerms rl, u ∈ killTabS) ∧ ∀ q ∈ ruleTys rl, killCall q.1 q.2 := by
  intro rl hrl h1 h2 h3
  have h := List.all_eq_true.mp rootS_ok rl hrl
  have hx : killExcl.contains rl.id = false := by simp [killExcl, h1, h2, h3]
  rw [hx, Bool.false_or] at h
  exact ruleOk_of h

/-- **The branch root rules** apply terms of `killTabB` at allowed call sites. -/
theorem killRootB : ∀ rl ∈ program.rulesOf TId.lower_branch,
    (∀ u ∈ ruleTerms rl, u ∈ killTabB) ∧ ∀ q ∈ ruleTys rl, killCall q.1 q.2 :=
  fun rl hrl => ruleOk_of (List.all_eq_true.mp rootB_ok rl hrl)

theorem oracles_ok : killOracles.all (fun t => killTabS.contains t && killTabB.contains t) = true := by
  native_decide

/-- The oracles are in both sets. -/
theorem killOracles_sub : ∀ t ∈ killOracles, t ∈ killTabS ∧ t ∈ killTabB := by
  intro t ht
  have h := List.all_eq_true.mp oracles_ok t ht
  simp only [Bool.and_eq_true, List.contains_iff_mem] at h
  exact h

theorem noX_ok : (killTabS ++ killTabB).all (fun t => t != TId.«MInst.AtomicRMWLoop» &&
    t != TId.«MInst.AtomicCASLoop» && t != TId.«MInst.JTSequence» && t != TId.invalid_reg) = true := by
  native_decide

/-- **No variant term of a variant with killed defs, and no `invalid_reg`**, in either set. -/
theorem killTab_noX : ∀ t ∈ killTabS ++ killTabB, t ≠ TId.«MInst.AtomicRMWLoop» ∧
    t ≠ TId.«MInst.AtomicCASLoop» ∧ t ≠ TId.«MInst.JTSequence» ∧ t ≠ TId.invalid_reg := by
  intro t ht
  have h := List.all_eq_true.mp noX_ok t ht
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem genCallRets_ok : killTabB.contains TId.gen_call_rets = false := by native_decide

/-- **No `gen_call_rets` in branch runs.** -/
theorem genCallRets_notB : TId.gen_call_rets ∉ killTabB := by
  have h := genCallRets_ok
  simpa using h

/-- The term-level form of the variant condition. -/
def varOkB (t : TermId) : Bool :=
  match program.term? t with
  | some term =>
    match term.kind with
    | .enumVariant k => !(term.ret == tyMInst && isKVariant k)
    | _ => true
  | none => true

theorem variants_ok : (killTabS ++ killTabB).all varOkB = true := by native_decide

/-- **No variant term of either set builds `MInst` data of a variant with killed defs** (for its
declared result type). -/
theorem killTab_variants : ∀ t ∈ killTabS ++ killTabB, ∀ term k, termOf program t = .ok term →
    term.kind = .enumVariant k → ¬(term.ret = tyMInst ∧ isKVariant k = true) := by
  intro t ht term k htm hk ⟨hty, hkv⟩
  have h := List.all_eq_true.mp variants_ok t ht
  rw [varOkB, termOf_program_eq htm] at h
  simp [hk, hty, hkv] at h

/-! ## The excluded root rules -/

/-- **Rules 636 and 637 (I128) never match a statement**: they are not closure roots. -/
theorem lower_636_637_nomatch {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {r : Rule} (hr : r ∈ program.rulesOf TId.lower) (hid : r.id = 636 ∨ r.id = 637) :
    ∀ m s0 env s1, (matchRule program (sem ctx) {} m r [.inst ii]).run s0 ≠ .ok (some env, s1) :=
  Driver.lower_nonroot_nomatch hctx hi hc hr (by rcases hid with h | h <;> rw [h] <;> decide)

/-- A run of an internal constructor that returned a value, of a term whose rules have no
if-lets: some rule's argument match and its right-hand side, at one fuel less. -/
theorem internal_rule {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false) {t : TermId}
    {term : Term} {flags : TermFlags} {ex : Option Extractor} (ht : termOf program t = .ok term)
    (hk : term.kind = .decl flags (some .internal) ex) (hm : flags.isMulti = false)
    (hil : ∀ r ∈ program.rulesOf t, r.iflets = []) {n : Nat} {ty : TypeId} {vs : List V}
    {s : LState} {tr : Array RuleId} {v : V} {s' : LState} {tr' : Array RuleId}
    (h : (applyTerm program (sem ctx) cfg (n + 1) ty t vs).run (s, tr) = .ok (some v, (s', tr'))) :
    ∃ r ∈ program.rulesOf t, ∃ env tr0,
      matchArgs program (sem ctx) s r.args vs (Array.replicate r.vars.length none) = .ok (some env) ∧
      (evalExpr program (sem ctx) cfg n r.rhs env).run (s, tr) = .ok (some v, (s', tr0)) := by
  obtain ⟨r, hr, m, env, s1, st, tr0, -, hmt, he, hs'⟩ := applyTerm_internal_some hc ht hk hm h
  obtain ⟨rfl, hma⟩ := Cov.matchRule_noIfLets (hil r hr) hmt
  simp only [Prod.mk.injEq] at hs'
  obtain ⟨rfl, -⟩ := hs'
  exact ⟨r, hr, env, tr0, hma, he⟩

theorem ctor_invalid_reg' (ctx : Ctx) (st : LState) :
    externCtor ctx T.invalid_reg [] st = .ok (.reg .invalid, st) := rfl

theorem term_178_kind_k : T.«invalid_reg».kind = (.decl ⟨false, false, false, false⟩
    (some (.external "invalid_reg")) (some (.internal (.list [(.atom "extractor"),
      (.list [(.atom "invalid_reg")]), (.list [(.atom "is_valid_reg"), (.atom "false")])])))) := rfl

set_option maxHeartbeats 1000000 in
theorem nop_rhs_some {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false) {n : Nat}
    {env : Isle.Interp.Env V} {s : LState} {tr : Array RuleId} {v : V} {s' : LState}
    {tr' : Array RuleId}
    (h : (evalExpr program (sem ctx) cfg n rule_lower_78.rhs env).run (s, tr) =
      .ok (some v, (s', tr'))) :
    s' = s ∧ v = .regsVec [[Reg.invalid]] := by
  oracle_inv [rule_lower_78, program_term_172, program_term_178, term_178_kind_k,
    ctor_invalid_reg'] at h
  have h172 := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rl, hrl, env, tr0, hma, he⟩ := internal_rule hc program_term_172 term_172_kind rfl
    (by rw [program_rulesOf_172]; simp [rule_prelude_lower_105]) h172
  rw [program_rulesOf_172, List.mem_singleton] at hrl
  subst hrl
  oracle_inv [rule_prelude_lower_105, program_term_170, program_term_164] at hma he

/-- `nop`'s right-hand side calls no `partial` term. -/
theorem totalE_nop : Cov.totalE program rule_lower_78.rhs = true := by decide +kernel

/-- **`nop`'s rule (587, `output_reg invalid_reg`)**: its right-hand side, from any environment
at any fuel, keeps the lowering state and returns only `[[Reg.invalid]]`. -/
theorem nop_rhs (htot : Cov.Totality) {ctx : Ctx} {r : Rule} (hr : r ∈ program.rulesOf TId.lower)
    (hid : r.id = 587) :
    ∀ (cfg : Config), cfg.checkOverlap = false → ∀ (n : Nat) (env : Isle.Interp.Env V)
      (s : LState) (tr : Array RuleId) (o : Option V) (s' : LState) (tr' : Array RuleId),
      (evalExpr program (sem ctx) cfg n r.rhs env).run (s, tr) = .ok (o, (s', tr')) →
      s' = s ∧ ∀ v, o = some v → v = .regsVec [[Reg.invalid]] := by
  have hmem : rule_lower_78 ∈ program.rulesOf TId.lower :=
    List.mem_iff_getElem?.mpr ⟨177, by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl⟩
  obtain rfl := eq_of_mem_of_id lower_ids_nodup hr hmem hid
  intro cfg hc n env s tr o s' tr' h
  obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.mp (htot.1 ctx cfg n _ env _ o _ totalE_nop h)
  obtain ⟨rfl, rfl⟩ := nop_rhs_some hc h
  exact ⟨rfl, fun _ hv => (Option.some.inj hv).symm⟩

theorem killImm_ok : (killTabS.contains TId.imm && killTabB.contains TId.imm) = true := by
  native_decide

/-- `imm` (a sub-run of `br_table_impl`) is in both sets. -/
theorem imm_mem : TId.imm ∈ killTabS ∧ TId.imm ∈ killTabB := by
  have h := killImm_ok
  simp only [Bool.and_eq_true, List.contains_iff_mem] at h
  exact h

end Backend.Proof.Kill
