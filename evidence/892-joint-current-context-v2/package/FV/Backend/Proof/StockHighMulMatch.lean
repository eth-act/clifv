import FV.Backend.Proof.StockDFG
import FV.Backend.Proof.StockHighMulNarrowRhs
namespace Backend.Stock.Proof.ScalarHighMul
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
section SourceData
attribute [local semireducible] Isle.Aarch64.program
/-- Original accepted high-multiply instructions determine their exact scalar
opcode, width and operand data; source IDs retain the original numbering. -/
theorem stock_highmul_source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (signed : Bool) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (if signed then .smulhi else .umulhi) ty x y)) :
    (ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) ∧
      info.data = .data 152 2 [.data 151 (if signed then 79 else 78) [],.values [x,y]] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by cases signed <;> simpa [Compile.instE,Compile.binaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,_⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  · cases ty <;> simp [eTy,Clif.Ty.width] at supported ⊢
  · have expected : instData f (.binary (if signed then .smulhi else .umulhi) ty x y) =
        .ok (.data 152 2 [.data 151 (if signed then 79 else 78) [],.values [x,y]]) := by
      cases signed <;> simp [instData,binaryOpcode,supported] <;> rfl
    exact Except.ok.inj (raw.symm.trans expected)
end SourceData
theorem stock_highmul_wide_match {p : Program} (hp : Data p) (ctx : Ctx) (signed : Bool)
    {i x y : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int 64))
    (data : info.data = .data 152 2 [.data 151 (if signed then 79 else 78) [],.values [x,y]])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) (wideRule signed) [.inst i]).run (st,tr) =
      .ok (some (wideEnv x y),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  cases hp
  cases signed
  all_goals simp only [wideRule,wideEnv,Bool.false_eq_true,ite_false,ite_true] at *
  all_goals isel_eval [*,rule_lower_1056,rule_lower_1068,sem_extract,sem_unData,sem_eq,sem_prim,ext_value_array_2]
theorem stock_highmul_narrow_match {p : Program} (hp : Data p) (ctx : Ctx) (signed : Bool)
    {i x y w : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w)) (width : w ≤ 32)
    (data : info.data = .data 152 2 [.data 151 (if signed then 79 else 78) [],.values [x,y]])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) (narrowRule signed) [.inst i]).run (st,tr) =
      .ok (some (narrowEnv w x y),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have fits := ext_fits_in_32_ty_fa ctx st.base (.int w)
  simp only [CTy.bits,width,ite_true] at fits
  cases hp
  cases signed
  all_goals simp only [narrowRule,narrowEnv,Bool.false_eq_true,ite_false,ite_true] at *
  all_goals isel_eval [*,rule_lower_1059,rule_lower_1071,sem_extract,sem_unData,sem_eq,sem_prim,ext_value_array_2]
end Backend.Stock.Proof.ScalarHighMul
