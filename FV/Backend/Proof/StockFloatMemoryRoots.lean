import FV.Backend.Proof.StockScopeRoots
import FV.Backend.Proof.StockRootOpcode
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- The float `load`/`store` closure roots (`load.f32`/`load.f64` 1047/1048, float `store`
1073/1074). Their opcodes are in `eOps`, but their patterns test `ty_float_or_vec`. -/
def floatMemoryRootIds : List RuleId := [1047,1048,1073,1074]

/-- Checked syntactic inventory: each listed root has one argument pattern that the abstract
exclusion checker rejects on every subset-E instruction. -/
theorem stock_float_memory_root_shapes :
    (program.rulesOf TId.lower).all (fun r => !floatMemoryRootIds.contains r.id ||
      match r.args with
      | [q] => fails program .inst q
      | _ => false) = true := by
  rw [show TId.lower = 686 from rfl,data_program.r686]
  decide +kernel

/-- The checked rejection applies to actual Stock source patterns through the mapped source
view, as for the roots outside the closure (`stock_excluded_root_args`). -/
theorem stock_float_memory_root_args {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {r : Rule} (member : r ∈ program.rulesOf TId.lower) (listed : r.id ∈ floatMemoryRootIds)
    {i : Nat} {info : IInfo} {inst : Clif.Inst} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some inst) (st : State) (env bound : Isle.Interp.Env V) :
    matchArgs program (Stock.sem ctx) st r.args [.inst i] env ≠ .ok (some bound) := by
  intro matched
  have checked := List.all_eq_true.mp stock_float_memory_root_shapes r member
  simp only [List.contains_iff_mem.mpr listed,Bool.not_true,Bool.false_or] at checked
  have view : DFGViewEq ctx (sourceIdentityCtx ctx) := ⟨rfl,rfl,rfl,rfl,rfl⟩
  rw [stock_matchArgs_source view] at matched
  split at checked
  · rename_i q argsEq
    rw [argsEq] at matched
    obtain ⟨middle,head,tail⟩ := matchArgs_cons_inv matched
    exact fails_sound mapped.identityView q .inst _ _ _ _ checked
      ⟨i,info,inst,rfl,source,clif,mapped.data i info inst source clif⟩ head
  · cases checked

theorem stock_float_memory_root_match {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {r : Rule} (member : r ∈ program.rulesOf TId.lower) (listed : r.id ∈ floatMemoryRootIds)
    {i : Nat} {info : IInfo} {inst : Clif.Inst} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some inst) (cfg : Config) (fuel : Nat) (st next : State × Array RuleId)
    (env : Isle.Interp.Env V) :
    (matchRule program (Stock.sem ctx) cfg fuel r [.inst i]).run st ≠ .ok (some env,next) := by
  intro matched
  cases fuel with
  | zero => rw [matchRule.eq_1] at matched; cases matched
  | succ fuel =>
    obtain ⟨bound,args,rest⟩ := matchRule_some_inv matched
    exact stock_float_memory_root_args mapped member listed source clif st.1 _ bound args

/-- Real first-match selection never picks a float memory root under the original mapped
context; no rule-id certificate is supplied by the caller. -/
theorem stock_selected_source_not_float_memory {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {i : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some inst)
    {before after : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i before out after trace) : selected.rule.id ∉ floatMemoryRootIds :=
  fun listed => stock_float_memory_root_match mapped selected.rule_mem listed source clif {}
    selected.matchFuel (before,#[]) (selected.matched,selected.matchTrace) selected.env selected.matchedRun
end Backend.Stock.Proof
