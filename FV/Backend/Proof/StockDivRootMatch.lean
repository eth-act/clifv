module

public import FV.Backend.Proof.IselTermsALUAMulN
public import FV.Backend.Proof.StockDivMatch
public import FV.Backend.Proof.StockRootOpcodeMatch

@[expose] public section

namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_prim (ctx : Ctx) : (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
def baseWideRule : Clif.DivOp → Rule
  | .udiv => rule_lower_1116 | .sdiv => rule_lower_1145
  | .urem => rule_lower_1190 | .srem => rule_lower_1204
def baseNarrowRule : Clif.DivOp → Rule
  | .udiv => rule_lower_1119 | .sdiv => rule_lower_1153
  | .urem => rule_lower_1197 | .srem => rule_lower_1211
def baseWideEnv (op : Clif.DivOp) (x y : Nat) : Isle.Interp.Env V :=
  ((Array.replicate (baseWideRule op).vars.length none).setIfInBounds 0 (some (.value x))).setIfInBounds 1 (some (.value y))
def baseNarrowEnv (op : Clif.DivOp) (w x y : Nat) : Isle.Interp.Env V :=
  (((Array.replicate (baseNarrowRule op).vars.length none).setIfInBounds 0 (some (.ty (.int w)))).setIfInBounds 1 (some (.value x))).setIfInBounds 2 (some (.value y))
theorem stock_div_base_wide_match {p : Program} (hp : Data p) (ctx : Ctx) (op : Clif.DivOp)
    {i x y : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int 64))
    (data : info.data = .data 152 2 [.data 151 (opcodeId op) [],.values [x,y]])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) (baseWideRule op) [.inst i]).run (st,tr) =
      .ok (some (baseWideEnv op x y),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  cases hp
  cases op
  all_goals simp only [baseWideRule,baseWideEnv,opcodeId] at *
  all_goals isel_eval [*,rule_lower_1116,rule_lower_1145,rule_lower_1190,rule_lower_1204,sem_extract,sem_unData,sem_eq,sem_prim,ext_value_array_2]
theorem stock_div_base_narrow_match {p : Program} (hp : Data p) (ctx : Ctx) (op : Clif.DivOp)
    {i x y w : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w)) (width : w ≤ 32)
    (data : info.data = .data 152 2 [.data 151 (opcodeId op) [],.values [x,y]])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) (baseNarrowRule op) [.inst i]).run (st,tr) =
      .ok (some (baseNarrowEnv op w x y),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have fits := ext_fits_in_32_ty_fa ctx st.base (.int w)
  simp only [CTy.bits,width,ite_true] at fits
  cases hp
  cases op
  all_goals simp only [baseNarrowRule,baseNarrowEnv,opcodeId] at *
  all_goals isel_eval [*,rule_lower_1119,rule_lower_1153,rule_lower_1197,rule_lower_1211,sem_extract,sem_unData,sem_eq,sem_prim,ext_value_array_2]
end Backend.Stock.Proof.ScalarDiv
