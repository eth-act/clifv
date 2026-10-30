import FV.Backend.Proof.IselCovForm
import FV.Backend.Proof.StockExtendRequests
import FV.Backend.Proof.StockCmpZeroMatch
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
section Integers
attribute [local semireducible] Isle.Aarch64.program
private theorem zero (ctx : Ctx) : (Stock.sem ctx).int 4 0 = .int 0 := rfl
end Integers
private def Matches (p : Program) (ctx : Ctx) (r : Rule) (args : List V) (env : Isle.Interp.Env V) : Prop :=
  ∀ st tr n,(matchRule p (Stock.sem ctx) {} (n+20) r args).run (st,tr) = .ok (some env,st,tr)
private def SavedMatch (p : Program) (ctx : Ctx) (fuel : Nat) (r : Rule) (args : List V)
    (start : State × Array RuleId) (env : Isle.Interp.Env V) (finish : State × Array RuleId) : Prop :=
  (matchRule p (Stock.sem ctx) {} fuel r args).run start = .ok (some env,finish)
private def SavedRhs (p : Program) (ctx : Ctx) (fuel : Nat) (r : Rule) (env : Isle.Interp.Env V)
    (start : State × Array RuleId) (out : V) (finish : State × Array RuleId) : Prop :=
  (evalExpr p (Stock.sem ctx) {} fuel r.rhs env).run start = .ok (some out,finish)
private def Outcome (p : Program) (ctx : Ctx) (r : Rule) (fuel : Nat) (x : Nat)
    (st next : State) (tr trace : Array RuleId) (out : V) : Prop :=
  ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel r.rhs #[some (.value x)]).run
    (st,tr) = .ok (some out,next,rhsTrace) ∧ trace = rhsTrace.push r.id
attribute [local irreducible] Matches SavedMatch SavedRhs Outcome
private theorem save_match {p : Program} {ctx : Ctx} {fuel : Nat} {r : Rule} {args : List V}
    {start finish : State × Array RuleId} {env : Isle.Interp.Env V}
    (h : (matchRule p (Stock.sem ctx) {} fuel r args).run start = .ok (some env,finish)) :
    SavedMatch p ctx fuel r args start env finish := by unfold SavedMatch; exact h
private theorem save_rhs {p : Program} {ctx : Ctx} {fuel : Nat} {r : Rule}
    {env : Isle.Interp.Env V} {start finish : State × Array RuleId} {out : V}
    (h : (evalExpr p (Stock.sem ctx) {} fuel r.rhs env).run start = .ok (some out,finish)) :
    SavedRhs p ctx fuel r env start out finish := by unfold SavedRhs; exact h
private theorem outcome_elim {p : Program} {ctx : Ctx} {r : Rule} {fuel x : Nat}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (h : Outcome p ctx r fuel x st next tr trace out) :
    ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel r.rhs #[some (.value x)]).run
      (st,tr) = .ok (some out,next,rhsTrace) ∧ trace = rhsTrace.push r.id := by
  unfold Outcome at h
  exact h
private theorem rejected_prefix {p : Program} {ctx : Ctx} {r : Rule} {args : List V}
    {env : Isle.Interp.Env V} {st : State} {tr : Array RuleId} {pre : List Rule}
    (matchProof : Matches p ctx r args env)
    (failed : ∀ r' ∈ pre,∃ n after,(matchRule p (Stock.sem ctx) {} (n+20) r' args).run
      (st,tr) = .ok (none,after)) (mem : r ∈ pre) : False := by
  obtain ⟨n,after,run⟩ := failed r mem
  unfold Matches at matchProof
  rw [matchProof st tr n] at run
  cases run
private theorem selected_outcome {p : Program} {ctx : Ctx} {r : Rule} {args : List V}
    {x m fuel : Nat} {st next : State} {tr trace : Array RuleId} {out : V}
    {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (matchProof : Matches p ctx r args #[some (.value x)])
    (matched : SavedMatch p ctx (m+20) r args (st,tr) env after)
    (rhs : SavedRhs p ctx fuel r env after out (next,trace)) :
    Outcome p ctx r fuel x st next tr (trace.push r.id) out := by
  unfold Matches at matchProof
  unfold SavedMatch at matched
  unfold SavedRhs at rhs
  rw [matchProof st tr m] at matched
  have parts := Prod.mk.inj (Except.ok.inj matched)
  have envEq := Option.some.inj parts.1
  rw [←envEq,←parts.2] at rhs
  unfold Outcome
  exact ⟨trace,rhs,rfl⟩
private theorem parameter_extract_absent {ctx : Ctx} {x : Nat} (parameter : ctx.defInst? x = none)
    {st : LState} {node : V} (h : externExtract ctx T.def_inst (.value x) st = .ok [node]) : False := by
  obtain ⟨j,defined,fields⟩ := (ext_def_inst_iff ctx st x [node]).mp h
  rw [parameter] at defined
  cases defined
/-- Successful real emit_icmp on a parameter and original defining zero selects
its actual zero rule, excluding higher mirrored rules and all later fallbacks. -/
theorem stock_cmp_zero_right_emitter_selected {p : Program} (hp : Data p) (ctx : Ctx)
    (nonzero : Bool) {x y j fuel : Nat} {info : IInfo} {i : Int}
    (enough : 220 ≤ fuel) (parameter : ctx.defInst? x = none)
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i]) (normalized : u64 i = 0)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) {} fuel 123 652
      [.data 145 (if nonzero then ccIdx .ne else ccIdx .eq) [],.value x,.value y]
      (st,tr) out (next,trace)) :
    ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel
      (if nonzero then rule_inst_5172 else rule_inst_5170).rhs #[some (.value x)]).run
      (st,tr) = .ok (some out,next,rhsTrace) ∧
      trace = rhsTrace.push (if nonzero then rule_inst_5172 else rule_inst_5170).id := by
  suffices h : Outcome p ctx (if nonzero then rule_inst_5172 else rule_inst_5170)
      fuel x st next tr trace out by exact outcome_elim h
  have hp' := hp
  have hc : ({} : Config).checkOverlap = false := rfl
  have matchProof : Matches p ctx (if nonzero then rule_inst_5172 else rule_inst_5170)
      [.data 145 (if nonzero then ccIdx .ne else ccIdx .eq) [],.value x,.value y]
      #[some (.value x)] := by
    unfold Matches
    exact fun q t n => stock_cmp_zero_right_match hp ctx nonzero defined found data normalized q t n
  cases nonzero
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true] at *
  all_goals clear hc
  all_goals have hc : ({} : Config).checkOverlap = false := rfl
  all_goals stock_split hp hc run 652
  all_goals try (
    exfalso
    apply rejected_prefix (p := p) (ctx := ctx) (st := st) (tr := tr) matchProof hpre
    simp only [List.mem_cons,List.mem_singleton]
    decide +kernel)
  all_goals have savedMatch := save_match hm
  all_goals have savedRhs := save_rhs he
  all_goals try (exact selected_outcome (p := p) (ctx := ctx) (x := x) (st := st) (tr := tr) matchProof savedMatch savedRhs)
  all_goals clear he run
  all_goals isel_inv_simp [hp'.t1,hp'.t2,hp'.t144,hp'.t209,hp'.t2341,hp'.t2482,hp'.t2269,hp'.t2270,
    rule_inst_5170,rule_inst_5171,rule_inst_5172,rule_inst_5173,sem_extract,sem_unData,sem_eq,zero,ccIdx] at hm
  all_goals isel_destruct <;> subst_vars
  all_goals isel_inv_simp [hp'.t1,hp'.t2,hp'.t144,hp'.t209,hp'.t2341,hp'.t2482,hp'.t2269,hp'.t2270,
    rule_inst_5170,rule_inst_5171,rule_inst_5172,rule_inst_5173,sem_extract,sem_unData,sem_eq,zero,ccIdx] at *
  all_goals isel_destruct <;> subst_vars
  all_goals first
    | exact selected_outcome (p := p) (ctx := ctx) (x := x) (st := st) (tr := tr) matchProof savedMatch savedRhs
    | exact False.elim (parameter_extract_absent parameter (by assumption))
end Backend.Stock.Proof.ScalarCmp
