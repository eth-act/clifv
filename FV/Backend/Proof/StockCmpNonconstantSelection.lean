import FV.Backend.Proof.StockSourceView
import FV.Backend.Proof.IselCovForm
import FV.Backend.Proof.StockCmpRegisterSelection
import FV.Backend.Proof.StockExtendRequests
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
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
section Integers
attribute [local semireducible] Isle.Aarch64.program
private theorem zero (ctx : Ctx) : (Stock.sem ctx).int 4 0 = .int 0 := rfl
end Integers
private def registerEnv (cc : Clif.IntCC) (sz : OperandSize) (x y : Nat) : Isle.Interp.Env V :=
  ((((Array.replicate 4 none).setIfInBounds 0 (some (.data 145 (ccIdx cc) []))).setIfInBounds 1 (some (.value x))).setIfInBounds 3 (some (.value y))).setIfInBounds 2 (some (.ty (.int sz.bits)))
private def RegisterMatches (p : Program) (ctx : Ctx) (cc : Clif.IntCC) (sz : OperandSize) (x y : Nat) : Prop :=
  ∀ q trace n,(matchRule p (Stock.sem ctx) {} (n+2) rule_inst_5128 [.data 145 (ccIdx cc) [],.value x,.value y]).run (q,trace) =
    .ok (some (registerEnv cc sz x y),q,trace)
attribute [local irreducible] RegisterMatches
private theorem registerEnv_eq (cc : Clif.IntCC) (sz : OperandSize) (x y : Nat) :
    registerEnv cc sz x y = #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)] := by
  apply Array.toList_inj.mp
  simp [registerEnv,Array.toList_setIfInBounds,List.set,List.replicate]
private theorem register_match {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (sz : OperandSize)
    {x y : Nat} (typed : ctx.valueType? y = some (.int sz.bits)) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) rule_inst_5128 [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) =
      .ok (some (registerEnv cc sz x y),st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  cases hp
  cases sz
  all_goals isel_eval [*,rule_inst_5128,registerEnv,sem_extract,sem_unData,ext_ty_32_or_64_32,ext_ty_32_or_64_64,OperandSize.bits]
/-- Original source classification, allowing parameters and defined nonconstant operands. -/
def NonConstantSource (ctx : Ctx) (x : Nat) : Prop :=
  ∀ j info,ctx.defInst? x = some j → ctx.insts[j]? = some info →
    ∀ ty (c : BitVec ty.width),info.clif ≠ some (.iconst ty c)
private theorem nonconstant_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {x j : Nat} {info : IInfo} (notConstant : NonConstantSource ctx x)
    (defined : ctx.defInst? x = some j) (found : ctx.insts[j]? = some info)
    {value : V} (data : info.data = .data 152 35 [.data 151 57 [],value]) : False := by
  obtain ⟨original,clif,raw⟩ := ctxInv_clif inv.identityView defined found
  rw [data] at raw
  obtain ⟨ty,c,rfl,fields⟩ := instData_iconst_inv raw
  exact notConstant j info defined found ty c clif
/-- A successful actual emitter call on original nonconstant operands at32/64
must select its real register path. The source requests and RHS execution are
derived internally, rather than supplied as an emitter-selection certificate. -/
theorem stock_cmp_nonconstant_emitter_selected {p : Program} (hp : Data p) (ctx : Ctx) {f : Clif.Function} (inv : MappedCtxInv f ctx)
    (cc : Clif.IntCC) (sz : OperandSize) {x y fuel : Nat}
    (enough : 200 ≤ fuel) (typeX : ctx.valueType? x = some (.int sz.bits))
    (typeY : ctx.valueType? y = some (.int sz.bits))
    (notConstantX : NonConstantSource ctx x) (notConstantY : NonConstantSource ctx y)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) {} fuel 123 652 [.data 145 (ccIdx cc) [],.value x,.value y]
      (st,tr) out (next,trace)) :
    ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel rule_inst_5128.rhs
      #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)]).run
      (st,tr) = .ok (some out,next,rhsTrace) ∧ trace = rhsTrace.push rule_inst_5128.id := by
  have hp' := hp
  have hc : ({} : Config).checkOverlap = false := rfl
  have typedX := fun q => ext_value_type ctx q typeX
  have typedY := fun q => ext_value_type ctx q typeY
  have matchRR : RegisterMatches p ctx cc sz x y := by
    unfold RegisterMatches
    exact fun q trace n => register_match hp' ctx cc sz (x := x) typeY q trace n
  have envEq := registerEnv_eq cc sz x y
  stock_split hp hc run 652
  all_goals isel_inv [*,rule_inst_5171,rule_inst_5173,rule_inst_5170,rule_inst_5172,
    rule_inst_5165,rule_inst_5155,rule_inst_5160,rule_inst_5142,rule_inst_5134,
    rule_inst_5128,rule_inst_5117,rule_inst_5108,sem_extract,sem_unData,sem_eq,sem_prim,zero] at hm
  all_goals try (cases sz <;> simp [OperandSize.bits,ext_ty_32_or_64_32,ext_ty_32_or_64_64] at hm)
  all_goals isel_destruct <;> subst_vars
  all_goals simp only [typeX,typeY,Option.some.injEq,reduceCtorEq] at *
  all_goals isel_destruct <;> subst_vars
  all_goals try (
    exfalso
    apply nonconstant_data inv notConstantX
    · assumption
    · assumption
    · symm; assumption)
  all_goals try (
    exfalso
    apply nonconstant_data inv notConstantY
    · assumption
    · assumption
    · symm; assumption)
  all_goals try (cases sz <;> simp [OperandSize.bits,CTy.ofName?,CTy.int.injEq] at *)
  all_goals try (refine ⟨_,?_,rfl⟩; rw [← envEq]; exact he)
  all_goals have rejected := hpre
  all_goals isel_destruct
  all_goals obtain ⟨m,after,failed⟩ : (∃ m after,
    (matchRule p (Stock.sem ctx) {} (m+20) rule_inst_5128 [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) =
      .ok (none,after)) := ⟨_,_,by assumption⟩
  all_goals unfold RegisterMatches at matchRR
  all_goals have forward := matchRR st tr (m+18)
  all_goals rw [show (m+18)+2=m+20 from by omega] at forward
  all_goals rw [forward] at failed
  all_goals cases failed
end Backend.Stock.Proof.ScalarCmp
