import FV.E2E.LinkOwnRets
import FV.Backend.Proof.KillDriver
import FV.Backend.Proof.IselShpCtor

/-!
# The ISLE inversion for `Rets`: `iselNoRets : IselNoRetsHyp`

The uniform invariant of ISLE runs (`Isle.Interp.UModel`, `KillGen.lean`) with the run relation
`NoRetsSince` on the term set `retTab`: the closure under `Isle.ruleTerms` of the terms applied
by the rules of `lower` other than `rule_lower_2574` (the `return` rule, id 1037) and by the rules
of `lower_branch`. Decided over the exported rule data: `retTab` is closed and does not contain
`gen_return`, the only extern constructor emitting a `Rets` (`Cov.externCtor_shp`; `emit`'s
`MInst.ofV` decodes no `Rets`, `ofV_noRets`). Rule 1037 pins the `MultiAry` format, which no
statement's data has (`ret_nomatch`).
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 100000

/-! ## Constructors emit no `Rets` but `gen_return` -/

/-- Is the instruction a `Rets`? -/
def isRetsB : MInst → Bool
  | .rets _ => true
  | _ => false

/-- **`MInst.ofV`** never builds a `Rets`. -/
theorem ofV_noRets {v : V} {m : MInst} (h : MInst.ofV v = some m) : isRetsB m = false := by
  unfold MInst.ofV at h
  obtain ⟨⟨k, fs⟩, -, h2⟩ := Flow.bind_some_ex h
  clear h
  revert h2
  revert m
  apply _root_.ofV_split _ (fun _ _ (r : Option MInst) => ∀ m, r = some m → isRetsB m = false)
  all_goals
    intros
    rename_i m hm
    try simp only at hm
    repeat' (first | (obtain ⟨_, _, hm⟩ := Flow.bind_some_ex hm) | split at hm)
    all_goals first
      | (cases hm; done)
      | (simp only [pure, Option.some.injEq] at hm
         subst hm
         rfl)

theorem noRets_refl (s : LState) : NoRetsSince s s := ⟨[], by simp, by simp⟩

theorem noRets_trans {a b c : LState} (h1 : NoRetsSince a b) (h2 : NoRetsSince b c) :
    NoRetsSince a c := by
  obtain ⟨ms, g1, g2⟩ := h1
  obtain ⟨ms', g3, g4⟩ := h2
  refine ⟨ms ++ ms', by simp [g3, g1], fun m hm => ?_⟩
  rcases List.mem_append.mp hm with hm | hm
  · exact g2 m hm
  · exact g4 m hm

/-- An extern constructor other than `gen_return` emits no `Rets`. -/
theorem ctor_noRets (ctx : Ctx) {term : Term} {vs : List V} {s : LState} {v : V} {s' : LState}
    (hid : term.id ≠ TId.gen_return) (h : (sem ctx).ctor term vs s = .ok (v, s')) :
    NoRetsSince s s' := by
  rw [sem_ctor] at h
  obtain ⟨ms, h1, h2⟩ := Cov.externCtor_shp ctx term vs s v s' h
  refine ⟨ms, h1, fun m hm us hus => ?_⟩
  subst hus
  rcases h2 _ hm with hc | ⟨-, i, -, hi⟩ | ⟨hg, -⟩
  · simp [MInst.isCtl] at hc
  · have := ofV_noRets hi
    simp [isRetsB] at this
  · exact hid hg

/-! ## The term set -/

/-- Worklist closure under `Isle.ruleTerms` (`k`: fuel; the closure property is decided
afterwards, so running out of fuel is harmless). -/
def retClose : Nat → List TermId → Std.HashSet TermId → Std.HashSet TermId
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | k + 1, t :: ts, seen =>
    if seen.contains t then retClose k ts seen
    else retClose k ((program.rulesOf t).flatMap ruleTerms ++ ts) (seen.insert t)

/-- The terms the root rules apply: those of `lower` but the `return` rule (1037), and those of
`lower_branch`. -/
def retRoots : List TermId :=
  ((program.rulesOf TId.lower).filter fun r => r.id != 1037).flatMap ruleTerms ++
    (program.rulesOf TId.lower_branch).flatMap ruleTerms

/-- **The terms of statement and branch runs.** -/
def retTab : List TermId := (retClose 10000000 retRoots {}).toList

/-- The terms of a rule are in `retTab`. -/
def retRuleOkB (rl : Rule) : Bool := (ruleTerms rl).all (retTab.contains ·)

theorem retTab_closedB : retTab.all (fun t => (program.rulesOf t).all retRuleOkB) = true := by
  native_decide

theorem retTab_genReturn : retTab.contains TId.gen_return = false := by native_decide

theorem retRootS_ok : (program.rulesOf TId.lower).all (fun rl => rl.id == 1037 || retRuleOkB rl) = true := by
  native_decide

theorem retRootB_ok : (program.rulesOf TId.lower_branch).all retRuleOkB = true := by native_decide

theorem retRuleOk_of {rl : Rule} (h : retRuleOkB rl = true) : ∀ u ∈ ruleTerms rl, u ∈ retTab := by
  intro u hu
  simpa using List.all_eq_true.mp h u hu

theorem retTab_closed : ∀ t ∈ retTab, ∀ rl ∈ program.rulesOf t, ∀ u ∈ ruleTerms rl, u ∈ retTab :=
  fun t ht rl hrl => retRuleOk_of (List.all_eq_true.mp (List.all_eq_true.mp retTab_closedB t ht) rl hrl)

theorem retTab_ne {t : TermId} (h : t ∈ retTab) : t ≠ TId.gen_return := by
  rintro rfl
  have := retTab_genReturn
  simp [h] at this

/-! ## The model -/

/-- **The no-`Rets` model** of the driver's semantics in context `ctx`, on `retTab`. -/
def retsModel (ctx : Ctx) : UModel program (sem ctx) where
  P := fun _ _ => True
  Is := fun _ => True
  Rs := NoRetsSince
  T := (· ∈ retTab)
  C := fun _ _ => True
  O := fun _ => False
  rs_refl := noRets_refl
  rs_trans := fun _ _ _ => noRets_trans
  mono := by intros; trivial
  int := by intros; trivial
  bool := by intros; trivial
  prim := by intros; trivial
  mkd := by intros; trivial
  un := by intros; trivial
  ext := by intros; trivial
  ctor := fun _ t _ _ _ _ _ _ _ hT ht _ _ _ h =>
    ⟨trivial, trivial, ctor_noRets ctx (by rw [Kill.termOf_id_eq ht]; exact retTab_ne hT) h⟩
  oracle := fun _ h => h.elim
  closed := fun t ht _ rl hrl => ⟨retTab_closed t ht rl hrl, fun _ _ => trivial⟩

/-! ## The `return` rule never matches a statement -/

theorem variantNames_MultiAry :
    (variantNames 152)[VIdx.InstructionData.MultiAry]? = some "MultiAry" := rfl

/-- **`rule_lower_2574`** (id 1037) pins the `MultiAry` format, which no statement has. -/
theorem ret_nomatch {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {rl : Rule} (hrl : rl ∈ program.rulesOf TId.lower) (hid : rl.id = 1037) :
    ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1) := by
  intro m s0 env s1 hm
  rw [eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2574 (by rw [hid]; rfl)] at hm
  obtain ⟨tf, htf, hkf⟩ := kind_of (t := 2465) (k := VIdx.InstructionData.MultiAry) (by decide +kernel)
  obtain ⟨to, hto, hko⟩ := kind_of (t := 2291) (k := 7) (by decide +kernel)
  obtain ⟨info', fs, hi', hd⟩ := rootOp_match (r := rule_lower_2574) rfl htf hkf hto hko hm
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hc
  rw [hd] at hdat
  have h1 := (instData_inv_names hdat).1
  rw [variantNames_MultiAry] at h1
  have h2 := Option.some.inj h1
  cases inst <;> simp [instNames] at h2

/-! ## The driver's runs -/

/-- **A statement's `lower` run** emits no `Rets`. -/
theorem stmt_noRets {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {s : LState} {out : Option V} {s' : LState} {tr : List RuleId}
    (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) : NoRetsSince s s' := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      ((∀ u ∈ ruleTerms rl, (retsModel ctx).T u) ∧ ∀ q ∈ ruleTys rl, (retsModel ctx).C q.1 q.2) ∨
        False ∨ ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠
          .ok (some env, s1) := by
    intro rl hrl
    by_cases hid : rl.id = 1037
    · exact .inr (.inr (ret_nomatch hctx hi hc hrl hid))
    · have h := List.all_eq_true.mp retRootS_ok rl hrl
      have hb : (rl.id == 1037) = false := by simpa using hid
      rw [hb, Bool.false_or] at h
      exact .inl ⟨retRuleOk_of h, fun _ _ => trivial⟩
  exact (uRoot (retsModel ctx) rfl (fun _ _ => False) (fun _ => False) data_program.t686
    term_686_kind rfl hrules (fun _ _ h => h.elim) (fun _ _ => trivial) trivial happ).2.1

/-- **A `lower_branch` run** (in any context) emits no `Rets`. -/
theorem branch_noRets {ctx : Ctx} {ti : Nat} {targets : List Label} {s : LState} {out : Option V}
    {s' : LState} {tr : List RuleId}
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr)) :
    NoRetsSince s s' := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  exact (uRoot (retsModel ctx) rfl (fun _ _ => False) (fun _ => False) data_program.t687
    term_687_kind rfl
    (fun rl hrl => .inl ⟨retRuleOk_of (List.all_eq_true.mp retRootB_ok rl hrl), fun _ _ => trivial⟩)
    (fun _ _ h => h.elim) (fun _ _ => trivial) trivial happ).2.1

/-- **The ISLE inversion for `Rets`.** -/
theorem iselNoRets : IselNoRetsHyp := by
  refine ⟨fun f hs ctx ranges st0 hbc ii info inst s out s' tr hi hc h => ?_,
    fun ctx ti targets s out s' tr h => branch_noRets h⟩
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hbc)
  exact stmt_noRets hctx hi hc h

end E2E.LinkCheck
