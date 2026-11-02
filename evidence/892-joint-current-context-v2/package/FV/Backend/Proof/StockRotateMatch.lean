import FV.Backend.Proof.StockRotateNarrowRoots
namespace Backend.Stock.Proof.ScalarRotate
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
def rotateOp (left : Bool) : Clif.BinaryOp := if left then .rotl else .rotr
def rotateOpcode (left : Bool) : Nat := if left then 101 else 102
def rotateRule (left immediate : Bool) (w : Nat) : Rule :=
  if w = 8 ∨ w = 16 then rotateNarrowRule left immediate
  else if immediate then rotateWideImmRule left (w = 64) else rotateWideRule left (w = 64)
def rotateEnv (left : Bool) (w x y : Nat) : Isle.Interp.Env V :=
  if w = 8 ∨ w = 16 then rotateNarrowEnv left w x y else rotateWideEnv left x y
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (t : Nat) (v : V) :
    (Stock.sem ctx).unData t v = (Backend.sem ctx).unData t v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
section Data
attribute [local semireducible] Isle.Aarch64.program
/-- Original mapped source facts supply the supported type, binary opcode and
result type for rotations; no caller encoding certificate is needed. -/
theorem stock_rotate_source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (left : Bool) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.binary (rotateOp left) ty x y)) :
    IW ty.width ∧ info.data = .data 152 2 [.data 151 (rotateOpcode left) [],.values [x,y]] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by
    cases left <;> simpa [rotateOp,Compile.instE,Compile.binaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  · cases ty <;> simp [eTy,Clif.Ty.width,IW] at supported ⊢
  · have expected : instData f (.binary (rotateOp left) ty x y) =
        .ok (.data 152 2 [.data 151 (rotateOpcode left) [],.values [x,y]]) := by
      cases left <;> simp [rotateOp,rotateOpcode,instData,binaryOpcode,supported] <;> rfl
    exact Except.ok.inj (raw.symm.trans expected)
end Data
/-- All six register-count matches bind canonical original operands, with
unchanged complete Stock state and trace. -/
theorem stock_rotate_register_match {p : Program} (hp : Data p) (ctx : Ctx) (left : Bool)
    {i x y w : Nat} {info : IInfo} (width : IW w) (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 2 [.data 151 (rotateOpcode left) [],.values [x,y]])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+10) (rotateRule left false w) [.inst i]).run (st,tr) =
      .ok (some (rotateEnv left w x y),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have values := ext_value_array_2 ctx st.base x y
  have fits := ext_fits_in_16 ctx st.base w
  cases hp
  cases left <;> rcases width with rfl | rfl | rfl | rfl
  all_goals simp only [rotateRule,rotateOpcode,rotateEnv,rotateNarrowRule,rotateNarrowEnv,
    rotateWideRule,rotateWideEnv,Bool.false_eq_true,Nat.reduceEqDiff,ite_true,ite_false,
    false_or,or_true,or_false] at extraction ⊢
  all_goals isel_eval [*,rule_lower_1772,rule_lower_1840,rule_lower_1791,rule_lower_1797,
    rule_lower_1844,rule_lower_1848,sem_extract,sem_unData,sem_eq,sem_prim]
end Backend.Stock.Proof.ScalarRotate
