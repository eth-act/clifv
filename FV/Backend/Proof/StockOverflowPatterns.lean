module

public import FV.Backend.Proof.StockSourceView
public import FV.Backend.Proof.StockPatternSource
public import FV.Backend.Proof.IselCmpCond

@[expose] public section

/-! Overflow flags patterns are excluded by the existing source subset.
This is a reachability prerequisite, not a proof that all whole-driver
opportunistic state stays empty. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
attribute [local irreducible] Isle.Aarch64.program
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def overflowFlagsRules : List Rule :=
  [rule_inst_4993, rule_inst_5013, rule_inst_5032, rule_inst_5049,
    rule_inst_5058, rule_inst_5077, rule_inst_5094]

private theorem legacy_overflow_flags_pattern_absurd {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) (st : LState) (x : Nat) (env env' : Isle.Interp.Env V)
    {r : Rule} (member : r ∈ overflowFlagsRules)
    (matched : matchArgs program (Backend.sem ctx) st r.args [.value x] env = .ok (some env')) :
    False := by
  simp only [overflowFlagsRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have hp : Data program := data_program
    isel_inv' hp [] at matched
    have lookup88 : (variantNames 151)[88]? = some "UaddOverflow" := by decide +kernel
    have lookup92 : (variantNames 151)[92]? = some "UmulOverflow" := by decide +kernel
    have lookup93 : (variantNames 151)[93]? = some "SmulOverflow" := by decide +kernel
    have absent88 : "UaddOverflow" ∉ eOpNames := by decide
    have absent92 : "UmulOverflow" ∉ eOpNames := by decide
    have absent93 : "SmulOverflow" ∉ eOpNames := by decide
    grind only [opcode_absurd]

/-- All seven generated overflow-flags source patterns fail on the existing
mapped subset-E context, independently of scheduler state and register IDs.
Five of these are the AArch64 creators of opportunistic flag producers. -/
theorem stock_overflow_flags_patterns_unreachable {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (st : State) (x : Nat)
    (env env' : Isle.Interp.Env V) {r : Rule}
    (member : r ∈ overflowFlagsRules) :
    matchArgs program (Stock.sem ctx) st r.args [.value x] env ≠ .ok (some env') := by
  intro matched
  have view : DFGViewEq ctx (sourceIdentityCtx ctx) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  rw [stock_matchArgs_source view] at matched
  exact legacy_overflow_flags_pattern_absurd mapped.identityView st.base x env env' member matched

/-- An actual successful rule match cannot select any overflow-flags rule in
the existing subset, including when matching uses the Stock scheduler state. -/
theorem stock_overflow_flags_rule_unreachable {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (st : State × Array RuleId) (x : Nat)
    {r : Rule} (member : r ∈ overflowFlagsRules) (cfg : Config) (fuel : Nat)
    (env : Isle.Interp.Env V) (next : State × Array RuleId) :
    (matchRule program (Stock.sem ctx) cfg fuel r [.value x]).run st ≠
      .ok (some env, next) := by
  intro matched
  cases fuel with
  | zero => rw [matchRule.eq_1] at matched; cases matched
  | succ fuel =>
    obtain ⟨env0, args, _⟩ := matchRule_some_inv matched
    exact stock_overflow_flags_patterns_unreachable mapped st.1 x _ env0 member args

/-- The premises come from an actual nonempty context build with an allocated
source register different from its source ID; the excluded rule list is nonempty. -/
theorem stock_overflow_flags_unreachable_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (initial : State),
      LowerScope f ∧ Stock.buildCtx f = .ok (ctx, ranges, initial) ∧
      MappedCtxInv f ctx ∧ ctx.valueReg? 2 = some (.vreg 193 .int) ∧
      rule_inst_4993 ∈ overflowFlagsRules ∧
      (∀ r ∈ overflowFlagsRules, ∀ env env',
        matchArgs program (Stock.sem ctx) initial r.args [.value 2] env ≠ .ok (some env')) ∧
      (∀ r ∈ overflowFlagsRules, ∀ cfg fuel env next,
        (matchRule program (Stock.sem ctx) cfg fuel r [.value 2]).run (initial, #[]) ≠
          .ok (some env, next)) := by
  obtain ⟨scope, build, mapped, reg⟩ := buildCtx_mappedInv_witness
  refine ⟨_, _, _, _, scope, build, mapped, reg, by simp [overflowFlagsRules], ?_, ?_⟩
  · intro r member env env'
    exact stock_overflow_flags_patterns_unreachable mapped _ 2 env env' member
  · intro r member cfg fuel env next
    exact stock_overflow_flags_rule_unreachable mapped _ 2 member cfg fuel env next

end Backend.Stock.Proof
