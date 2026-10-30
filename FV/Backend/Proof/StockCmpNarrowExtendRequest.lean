import FV.Backend.Proof.StockValues
import FV.Backend.Proof.IselCtlTry
import FV.Backend.Proof.StockShiftHelper
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_bool (ctx : Ctx) (b : Bool) : (Stock.sem ctx).bool b = .bool b := rfl
private theorem sem_int (ctx : Ctx) (ty : Nat) (i : Int) : (Stock.sem ctx).int ty i = .int (normInt ty i) := rfl
/-- The actual narrow widening helpers demand the original operand and retain
all scheduling fields while allocating their32-bit temporary. -/
theorem stock_cmp_narrow_extend_request {p : Program} (hp : Data p) (ctx : Ctx) (signed : Bool)
    {x w : Nat} (width : w ≤ 16) (type : ctx.valueType? x = some (.int w))
    {rx : Reg} (mapped : ctx.valueReg? x = some rx) (st : State) (safe : DemandAllowed ctx st x)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace,(applyTerm p (Stock.sem ctx) {} (n+60) 27 (if signed then 555 else 556) [.value x]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st.mark x with base := (st.base.fresh .int).2.emit (.extend (st.base.fresh .int).1 rx signed w 32)},trace) := by
  have helper := fun q trace fuel => ScalarShift.stock_extend_helper hp ctx (cfg := {}) rfl q trace fuel rx signed w 32
  have helperExact := ScalarShift.stock_extend_helper hp ctx (cfg := {}) rfl (st.mark x) tr (n+38) rx signed w 32
  have cast32 : ((32:Nat):Int) = (32:Int) := rfl
  simp only [cast32] at helper helperExact
  have valueType := ext_value_type ctx st.base type
  have fits := ext_fits_in_32 ctx st.base w
  simp only [show w ≤ 32 by omega,ite_true] at fits
  have bits : ∀ q,Stock.externCtor ctx T.ty_bits [.ty (.int w)] q = .ok (.int w,q) := by
    intro q
    rw [stock_ctor_baseOnly ctx T.ty_bits _ q (by decide)]
    rfl
  have primitive32 : (Stock.sem ctx).prim 14 "I32" = some (.ty (.int 32)) := rfl
  have primitive64 : (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
  have eq : ∀ a b,(Stock.sem ctx).eq a b = (a == b) := fun _ _ => rfl
  have ne32 : (V.ty (.int w) == V.ty (.int 32)) = false := by simp; omega
  have ne64 : (V.ty (.int w) == V.ty (.int 64)) = false := by simp; omega
  have request := stock_put_in_reg ctx st x rx mapped safe
  have norm32 : normInt 1 32 = 32 := normInt_1_32
  have hp' := hp
  cases signed
  · refine Exists.intro ?traceU ?proofU
    case proofU =>
      simp only [Bool.false_eq_true,ite_false] at *
      rw [applyTerm.eq_2]
      rw [hp.t556]
      isel_eval [*, isel_monad,hp'.t555,hp'.r555,hp'.t556,hp'.r556,hp'.t2,hp'.t111,hp'.t182,hp'.t87,rule_inst_3809,rule_inst_3813,rule_inst_3814,sem_ctor,sem_extract,sem_bool,sem_int,norm32,ctor_ty_bits_ty_fa]
      all_goals simp only [isel_data,isel_monad]
      all_goals isel_eval [*, isel_monad,hp'.t555,hp'.r555,hp'.t556,hp'.r556,hp'.t2,hp'.t111,hp'.t182,hp'.t87,rule_inst_3799,rule_inst_3803,rule_inst_3804,rule_inst_3809,rule_inst_3813,rule_inst_3814,sem_ctor,sem_extract,sem_bool,sem_int,norm32,reduceCtorEq]
      all_goals rfl
  · refine Exists.intro ?traceS ?proofS
    case proofS =>
      simp only [ite_true] at *
      rw [applyTerm.eq_2]
      rw [hp.t555]
      isel_eval [*, isel_monad,hp'.t555,hp'.r555,hp'.t556,hp'.r556,hp'.t2,hp'.t111,hp'.t182,hp'.t87,rule_inst_3799,rule_inst_3803,rule_inst_3804,sem_ctor,sem_extract,sem_bool,sem_int,norm32,ctor_ty_bits_ty_fa]
      all_goals simp only [isel_data,isel_monad]
      all_goals isel_eval [*, isel_monad,hp'.t555,hp'.r555,hp'.t556,hp'.r556,hp'.t2,hp'.t111,hp'.t182,hp'.t87,rule_inst_3799,rule_inst_3803,rule_inst_3804,rule_inst_3809,rule_inst_3813,rule_inst_3814,sem_ctor,sem_extract,sem_bool,sem_int,norm32,reduceCtorEq]
      all_goals rfl
end Backend.Stock.Proof.ScalarCmp
