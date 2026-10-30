import FV.Backend.Proof.IselCmpRoot
import FV.Backend.Proof.StockSourceView
import FV.Backend.Proof.StockPatternSource
import FV.Backend.Proof.StockExtendRequests
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
private theorem defClif_of {ctx : Ctx} {x i : Nat} {info : IInfo} {cl : Clif.Inst}
    (defined : ctx.defInst? x = some i) (found : ctx.insts[i]? = some info) (source : info.clif = some cl) :
    ctx.defClif? x = some cl := by simp [Ctx.defClif?,defined,found,source]
section Names
attribute [local semireducible] Isle.Aarch64.program
private theorem fcmp_name : (variantNames 151)[112]? = some "Fcmp" := by decide +kernel
end Names
private theorem legacy_fcmp_absurd {f : Clif.Function} {ctx : Ctx} (inv : CtxInv f ctx)
    {c : Nat} {st : LState} {env next : Isle.Interp.Env V}
    (matched : matchArgs program (Backend.sem ctx) st rule_inst_4965.args [.value c] env = .ok (some next)) : False := by
  have hp := data_program
  isel_inv' hp [] at matched
  rcases ‹(∃ _ _, _) ∨ _› with ⟨uty,z,definition,rfl⟩ | ⟨_,rfl⟩
  all_goals repeat (isel_inv_simp [] at * <;> isel_destruct <;> subst_vars)
  all_goals
    obtain ⟨defined⟩ : Nonempty (ctx.defInst? _ = some _) := ⟨‹_›⟩
    obtain ⟨found⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹_›⟩
    obtain ⟨data⟩ : Nonempty (V.data 152 11 _ = _) := ⟨‹_›⟩
    exact opcode_absurd inv defined found data fcmp_name (by decide +kernel)
private theorem fcmp_absurd {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {c fuel : Nat} {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {next : State × Array RuleId}
    (matched : (matchRule program (Stock.sem ctx) {} fuel rule_inst_4965 [.value c]).run (st,tr) = .ok (some env,next)) : False := by
  cases fuel with
  | zero => rw [matchRule.eq_1] at matched; cases matched
  | succ fuel =>
    obtain ⟨before,args,_⟩ := matchRule_some_inv matched
    have view : DFGViewEq ctx (sourceIdentityCtx ctx) := ⟨rfl,rfl,rfl,rfl,rfl⟩
    rw [stock_matchArgs_source view] at args
    exact legacy_fcmp_absurd inv.identityView args
/-- A source condition directly defined by an integer comparison, optionally
through the original single zero extension looked through by actual650. -/
def SelectComparisonOrigin (ctx : Ctx) (c : Nat) (cc : Clif.IntCC) (ty : Clif.Ty) (a b : Nat) : Prop :=
  ctx.defClif? c = some (.icmp cc ty a b) ∨
    ∃ target z,ctx.defClif? c = some (.extend .uextend target z) ∧ ctx.defClif? z = some (.icmp cc ty a b)
private def ConditionOutcome (ctx : Ctx) (c : Nat) (st middle : State) (tr : Array RuleId) (condition : V) : Prop :=
    (∃ helperFuel helperTrace,300 ≤ helperFuel ∧
      ApplyInternal program (Stock.sem ctx) {} helperFuel 123 651 [.value c]
        (st,tr) condition (middle,helperTrace)) ∨
    (∃ cc ty a b,SelectComparisonOrigin ctx c cc ty a b ∧
      ∃ helperFuel helperTrace,300 ≤ helperFuel ∧
        ApplyInternal program (Stock.sem ctx) {} helperFuel 123 652
          [.data 145 (ccIdx cc) [],.value a,.value b] (st,tr) condition (middle,helperTrace))
attribute [local irreducible] ConditionOutcome
/-- Actual original650 either calls the scalar nonzero emitter or compares
original integer source operands. Float look-through is excluded by original
scope, and comparison provenance is derived from actual DFG matching. -/
theorem stock_original_select_condition_calls {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {c fuel : Nat} (enough : 400 ≤ fuel)
    {st middle : State} {tr trace : Array RuleId} {condition : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 123 650 [.value c] (st,tr) condition (middle,trace)) :
    (∃ helperFuel helperTrace,300 ≤ helperFuel ∧
      ApplyInternal program (Stock.sem ctx) {} helperFuel 123 651 [.value c]
        (st,tr) condition (middle,helperTrace)) ∨
    (∃ cc ty a b,SelectComparisonOrigin ctx c cc ty a b ∧
      ∃ helperFuel helperTrace,300 ≤ helperFuel ∧
        ApplyInternal program (Stock.sem ctx) {} helperFuel 123 652
          [.data 145 (ccIdx cc) [],.value a,.value b] (st,tr) condition (middle,helperTrace)) := by
  suffices outcome : ConditionOutcome ctx c st middle tr condition by
    simpa only [ConditionOutcome] using outcome
  have hp := data_program
  have hc : ({} : Config).checkOverlap = false := rfl
  stock_split hp hc run 650
  · exact False.elim (fcmp_absurd inv hm)
  · isel_inv [*,rule_inst_4966,sem_extract,sem_unData,stock_matchArgs] at hm
    rcases ‹(∃ _ _, _) ∨ _› with ⟨uty,z,definition,rfl⟩ | ⟨_,rfl⟩
    all_goals repeat (isel_inv_simp [] at * <;> isel_destruct <;> subst_vars)
    all_goals
      obtain ⟨defined⟩ : Nonempty (ctx.defInst? _ = some _) := ⟨‹_›⟩
      obtain ⟨found⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹_›⟩
      obtain ⟨data⟩ : Nonempty (V.data 152 14 _ = _) := ⟨‹_›⟩
      obtain ⟨cl,clif,raw⟩ := ctxInv_clif inv.identityView defined found
      rw [← data] at raw
      obtain ⟨cc,ty,a,b,rfl,rfl,rfl⟩ := instData_icmp_inv raw
      isel_inv_simp [] at *
      isel_destruct
      subst_vars
      isel_inv [*,rule_inst_4966,sem_extract,sem_unData,stock_matchArgs] at he
      obtain ⟨call⟩ : Nonempty (ApplyInternal program (Stock.sem ctx) {} _ 123 652 _ _ _ _) := ⟨‹_›⟩
      have origin := defClif_of defined found clif
      have provenance : SelectComparisonOrigin ctx c cc ty a b := by
        unfold SelectComparisonOrigin
        first
          | exact Or.inl origin
          | exact Or.inr ⟨_,_,by assumption,origin⟩
      unfold ConditionOutcome
      exact Or.inr ⟨cc,ty,a,b,provenance,_,_,by omega,call⟩
  · isel_inv [*,rule_inst_4967,sem_extract,sem_unData,stock_matchArgs] at hm he
    all_goals isel_destruct <;> subst_vars
    all_goals
      obtain ⟨call⟩ : Nonempty (ApplyInternal program (Stock.sem ctx) {} _ 123 651 _ _ _ _) := ⟨‹_›⟩
      unfold ConditionOutcome
      exact Or.inl ⟨_,_,by omega,call⟩
end Backend.Stock.Proof.ScalarSelect
