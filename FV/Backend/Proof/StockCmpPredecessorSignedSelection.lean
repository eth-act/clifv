import FV.Backend.Proof.StockExtendRequests
import FV.Backend.Proof.StockCmpPredecessorSignedMatch
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private def Canonical (p : Program) (ctx : Ctx) (r : Rule) (args : List V) (env : Isle.Interp.Env V) : Prop :=
  ∀ st tr n,(matchRule p (Stock.sem ctx) {} (n+20) r args).run (st,tr) = .ok (some env,st,tr)
private def SavedMatch (p : Program) (ctx : Ctx) (fuel : Nat) (r : Rule) (args : List V)
    (start : State × Array RuleId) (env : Isle.Interp.Env V) (finish : State × Array RuleId) : Prop :=
  (matchRule p (Stock.sem ctx) {} fuel r args).run start = .ok (some env,finish)
private def SavedRhs (p : Program) (ctx : Ctx) (fuel : Nat) (r : Rule) (env : Isle.Interp.Env V)
    (start : State × Array RuleId) (out : V) (finish : State × Array RuleId) : Prop :=
  (evalExpr p (Stock.sem ctx) {} fuel r.rhs env).run start = .ok (some out,finish)
private def Outcome (p : Program) (ctx : Ctx) (r : Rule) (env : Isle.Interp.Env V) (fuel : Nat)
    (st next : State) (tr trace : Array RuleId) (out : V) : Prop :=
  ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel r.rhs env).run (st,tr) = .ok (some out,next,rhsTrace) ∧
    trace = rhsTrace.push r.id
attribute [local irreducible] Canonical SavedMatch SavedRhs Outcome
private theorem outcome_elim {p : Program} {ctx : Ctx} {r : Rule} {env : Isle.Interp.Env V}
    {fuel : Nat} {st next : State} {tr trace : Array RuleId} {out : V}
    (h : Outcome p ctx r env fuel st next tr trace out) :
    ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel r.rhs env).run (st,tr) = .ok (some out,next,rhsTrace) ∧
      trace = rhsTrace.push r.id := by
  unfold Outcome at h
  exact h
private theorem save_match {p : Program} {ctx : Ctx} {fuel : Nat} {r : Rule} {args : List V}
    {start finish : State × Array RuleId} {env : Isle.Interp.Env V}
    (h : (matchRule p (Stock.sem ctx) {} fuel r args).run start = .ok (some env,finish)) :
    SavedMatch p ctx fuel r args start env finish := by unfold SavedMatch; exact h
private theorem save_rhs {p : Program} {ctx : Ctx} {fuel : Nat} {r : Rule} {env : Isle.Interp.Env V}
    {start finish : State × Array RuleId} {out : V}
    (h : (evalExpr p (Stock.sem ctx) {} fuel r.rhs env).run start = .ok (some out,finish)) :
    SavedRhs p ctx fuel r env start out finish := by unfold SavedRhs; exact h
private theorem selected {p : Program} {ctx : Ctx} {r : Rule} {args : List V}
    {canonical env : Isle.Interp.Env V} {m fuel : Nat} {st next : State} {tr trace : Array RuleId}
    {after : State × Array RuleId} {out : V} (matchProof : Canonical p ctx r args canonical)
    (matched : SavedMatch p ctx (m+20) r args (st,tr) env after)
    (rhs : SavedRhs p ctx fuel r env after out (next,trace)) :
    Outcome p ctx r canonical fuel st next tr (trace.push r.id) out := by
  unfold Canonical at matchProof
  unfold SavedMatch at matched
  unfold SavedRhs at rhs
  rw [matchProof st tr m] at matched
  have parts := Prod.mk.inj (Except.ok.inj matched)
  have eq := Option.some.inj parts.1
  rw [← eq,← parts.2] at rhs
  unfold Outcome
  exact ⟨trace,rhs,rfl⟩
private theorem rejected_prefix {p : Program} {ctx : Ctx} {r : Rule} {args : List V}
    {env : Isle.Interp.Env V} {st : State} {tr : Array RuleId} {pre : List Rule}
    (matchProof : Canonical p ctx r args env)
    (failed : ∀ r' ∈ pre,∃ n after,(matchRule p (Stock.sem ctx) {} (n+20) r' args).run (st,tr) = .ok (none,after))
    (member : r ∈ pre) : False := by
  obtain ⟨n,after,run⟩ := failed r member
  unfold Canonical at matchProof
  rw [matchProof st tr n] at run
  cases run
private theorem ordinary_failure {p : Program} (hp : Data p) (ctx : Ctx) (sz : OperandSize)
    {x y j : Nat} {info : IInfo} {i : Int}
    (typed : ctx.valueType? x = some (.int sz.bits))
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i])
    (nonencodable : Imm12.ofNat? (u64 i) = none) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) rule_inst_5165
      [.data 145 (ccIdx .sge) [],.value x,.value y]).run (st,tr) = .ok (none,st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  have definition := ext_def_inst_some ctx st.base defined
  have instruction := ext_inst_data_value ctx st.base found
  rw [data] at instruction
  have normalized := ext_u64_from_imm64 ctx st.base i
  have normalizedNonencodable : Imm12.ofNat? (u64 (u64 i)) = none := by
    rw [u64_ofNat (u64_lt' i)]; exact nonencodable
  have absent : externExtract ctx T.imm12_from_u64 (.int (u64 i)) st.base = .fail := by
    rw [ext_imm12_from_u64,normalizedNonencodable]
  cases hp
  cases sz
  all_goals isel_eval [*,rule_inst_5165,sem_extract,sem_unData,sem_eq,stock_matchArgs,
    ext_ty_32_or_64_32,ext_ty_32_or_64_64,OperandSize.bits]
/-- A real emitter success with an original nonencodable odd constant selects
the actual predecessor RHS, excluding ordinary immediates and later fallbacks. -/
theorem stock_cmp_predecessor_signed_emitter_selected {p : Program} (hp : Data p) (ctx : Ctx) (sz : OperandSize)
    {x y j fuel : Nat} {info : IInfo} {i : Int} {imm : Imm12}
    (enough : 200 ≤ fuel) (typed : ctx.valueType? x = some (.int sz.bits))
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i])
    (odd : u64 i % 2 = 1) (encoded : Imm12.ofNat? (u64 (i-1)) = some imm)
    (nonencodable : Imm12.ofNat? (u64 i) = none)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) {} fuel 123 652
      [.data 145 (ccIdx .sge) [],.value x,.value y] (st,tr) out (next,trace)) :
    ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel rule_inst_5160.rhs
      #[some (.ty (.int sz.bits)),some (.value x),some (.int (u64 i)),some (.op (.imm12 imm))]).run
      (st,tr) = .ok (some out,next,rhsTrace) ∧ trace = rhsTrace.push rule_inst_5160.id := by
  suffices result : Outcome p ctx rule_inst_5160
      #[some (.ty (.int sz.bits)),some (.value x),some (.int (u64 i)),some (.op (.imm12 imm))] fuel st next tr trace out by
    exact outcome_elim result
  have hp' := hp
  have hc : ({} : Config).checkOverlap = false := rfl
  have matchProof : Canonical p ctx rule_inst_5160 [.data 145 (ccIdx .sge) [],.value x,.value y]
      #[some (.ty (.int sz.bits)),some (.value x),some (.int (u64 i)),some (.op (.imm12 imm))] := by
    unfold Canonical
    exact fun q t n => stock_cmp_predecessor_signed_match hp' ctx sz typed defined found data odd encoded q t n
  stock_split hp hc run 652
  all_goals simp only [Prod.mk.injEq] at *
  all_goals isel_destruct <;> subst_vars
  all_goals try (
    exfalso
    apply rejected_prefix (p := p) (ctx := ctx) (st := st) (tr := tr) matchProof hpre
    decide +kernel)
  all_goals have savedMatch := save_match hm
  all_goals have savedRhs := save_rhs he
  all_goals try (exact selected (p := p) (ctx := ctx) (st := st) (tr := tr) matchProof savedMatch savedRhs)
  all_goals try (
    rw [ordinary_failure hp' ctx sz typed defined found data nonencodable] at hm
    cases hm)
  all_goals clear he run
  all_goals isel_inv_simp [hp'.t1,hp'.t2,hp'.t144,hp'.t209,hp'.t2341,hp'.t2482,hp'.t2269,hp'.t2270,hp'.t2272,hp'.t2276,
    rule_inst_5170,rule_inst_5171,rule_inst_5172,rule_inst_5173,rule_inst_5155,rule_inst_5160,
    sem_extract,sem_unData,sem_eq,ccIdx] at hm
  all_goals isel_destruct <;> subst_vars
  all_goals simp at *
end Backend.Stock.Proof.ScalarCmp
