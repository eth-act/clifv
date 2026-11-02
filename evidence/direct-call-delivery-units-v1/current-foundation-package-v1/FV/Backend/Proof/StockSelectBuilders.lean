import FV.Backend.Proof.StockValues
import FV.Backend.Proof.StockCmpWithFlags
import FV.Backend.Proof.IselCmpSelect
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem sem_unData (ctx : Ctx) (ty k j : Nat) (vs : List V) :
    (Stock.sem ctx).unData ty (.data k j vs) = if k = ty then some (j,vs) else none :=
  Backend.Proof.sem_unData ctx ty k j vs
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem base_eq (ctx : Ctx) (a b : V) : (Backend.sem ctx).eq a b = (a == b) := rfl
private theorem base_prim (ctx : Ctx) (name : String) :
    (Backend.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem int_scalar (ctx : Ctx) {w : Nat} (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (st : State) :
    Stock.externCtor ctx T.ty_int_ref_scalar_64 [.ty (.int w)] st = .ok (.ty (.int w),st) := by
  rw [stock_ctor_baseOnly ctx T.ty_int_ref_scalar_64 _ st (by decide)]
  rcases width with rfl | rfl | rfl | rfl <;> rfl
private theorem not_float (ctx : Ctx) (w : Nat) (st : LState) :
    Backend.externExtract ctx T.ty_scalar_float (.ty (.int w)) st = .fail := rfl
private theorem not_vector (ctx : Ctx) (w : Nat) (st : LState) :
    Backend.externExtract ctx T.ty_vec128 (.ty (.int w)) st = .fail := rfl
private theorem fresh (ctx : Ctx) (st : State) :
    Stock.externCtor ctx T.temp_writable_reg [.ty (.int 64)] st =
      .ok (.reg (st.base.fresh .int).1,{st with base := (st.base.fresh .int).2}) := by
  rw [stock_ctor_baseOnly ctx T.temp_writable_reg _ st (by decide)]
  rfl
private theorem writable (ctx : Ctx) (st : State) (v : V) :
    Stock.externCtor ctx T.writable_reg_to_reg [v] st = .ok (v,st) := by
  rw [stock_ctor_baseOnly ctx T.writable_reg_to_reg _ st (by decide)]
  rfl
/-- Actual conditional-select construction allocates one result and preserves
all Stock scheduling fields outside the allocation frontier. -/
theorem stock_csel_builder {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (st : State) (tr : Array RuleId) (n : Nat) (condition x y : V) :
    (applyTerm p (Stock.sem ctx) cfg (n+40) 49 425 [condition,x,y]).run (st,tr) =
      .ok (some (.data 49 3 [.data 58 31 [.reg (st.base.fresh .int).1,condition,x,y],
        .reg (st.base.fresh .int).1]),{st with base := (st.base.fresh .int).2},tr.push rule_inst_3059.id) := by
  have temporary := fun q => fresh ctx q
  have register := fun q v => writable ctx q v
  cases hp
  isel_eval [*,rule_inst_3059,sem_ctor,sem_mkData,sem_prim,CTy.ofName?]
/-- Scalar lower_select_cond performs both original guarded requests, allocates
one destination, emits the decoded flag producer and actual csel, and retains
all remaining scheduling state. -/
theorem stock_select_cond_run {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {w x y : Nat} (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (st : State) (tr : Array RuleId) (n : Nat) (condition : Cond)
    {mi : V} {m : MInst} (decoded : MInst.ofV mi = some m) {rx ry : Reg}
    (mapX : ctx.valueReg? x = some rx) (mapY : ctx.valueReg? y = some ry)
    (safeX : DemandAllowed ctx st x) (safeY : DemandAllowed ctx (st.mark x) y) :
    (applyTerm p (Stock.sem ctx) cfg (n+160) 22 660
      [.ty (.int w),.data 47 1 [mi],.data 96 condition.idx [],.value x,.value y]).run (st,tr) =
      .ok (some (.regs [(st.base.fresh .int).1]),
        {(st.mark x).mark y with base := (((st.base.fresh .int).2.emit m).emit
          (.csel (st.base.fresh .int).1 rx ry condition))},
        ((tr.push rule_inst_3059.id).push rule_prelude_lower_818.id).push rule_inst_5364.id) := by
  have requestX := stock_put_in_reg ctx st x rx mapX safeX
  have requestY := stock_put_in_reg ctx (st.mark x) y ry mapY safeY
  have builder := fun q trace fuel => stock_csel_builder hp ctx hc q trace fuel
    (.data 96 condition.idx []) (.reg rx) (.reg ry)
  have decodedSelect : MInst.ofV (.data 58 31 [.reg (st.base.fresh .int).1,
      .data 96 condition.idx [],.reg rx,.reg ry]) =
      some (.csel (st.base.fresh .int).1 rx ry condition) := by
    rw [ofV_csel',V.cond?_data,cond_ofIdx_idx]
    rfl
  have flags := fun q trace fuel => ScalarCmp.stock_cmp_with_flags_reg hp ctx hc q trace fuel
    decoded decodedSelect (st.base.fresh .int).1
  have scalar := fun q => int_scalar ctx width q
  have noFloat : (V.ty (.int w) == V.ty (.float 128)) = false := by
    rcases width with rfl | rfl | rfl | rfl <;> decide
  have no128 : (V.ty (.int w) == V.ty (.int 128)) = false := by
    rcases width with rfl | rfl | rfl | rfl <;> decide
  simp only [State.mark] at requestX requestY builder flags ⊢
  rcases width with rfl | rfl | rfl | rfl
  all_goals cases hp
  all_goals isel_eval [*,rule_inst_5343,rule_inst_5350,rule_inst_5345,rule_inst_5341,rule_inst_5364,rule_inst_5347,
      sem_ctor,sem_mkData,sem_unData,sem_prim,sem_eq,sem_extract,base_eq,base_prim,State.mark,stock_matchArgs,not_float,not_vector,CTy.ofName?]
  all_goals rfl
end Backend.Stock.Proof.ScalarSelect
