import FV.Backend.Proof.IselCmpEmit
import FV.Backend.Proof.StockProjection
import FV.Backend.Proof.IselCtlTry
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
private theorem base_eq (ctx : Ctx) (a b : V) : (Backend.sem ctx).eq a b = (a == b) := rfl
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_bool (ctx : Ctx) (b : Bool) : (Stock.sem ctx).bool b = .bool b := rfl
section Integers
attribute [local semireducible] Isle.Aarch64.program
private theorem one (ctx : Ctx) : (Stock.sem ctx).int 4 1 = .int 1 := rfl
private theorem zero (ctx : Ctx) : (Stock.sem ctx).int 4 0 = .int 0 := rfl
end Integers
theorem stock_cmp_constant_left_zero_failure {p : Program} (hp : Data p) (ctx : Ctx)
    (nonzeroRule : Bool) (cc : Clif.IntCC) {x y j : Nat} {info : IInfo} {i : Int}
    (defined : ctx.defInst? x = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i]) (nonzero : u64 i ≠ 0)
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) (if nonzeroRule then rule_inst_5173 else rule_inst_5171)
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (none,st,tr) := by
  have definition := ext_def_inst_some ctx st.base defined
  have instruction := ext_inst_data_value ctx st.base found
  rw [data] at instruction
  have normalized := ext_u64_from_imm64 ctx st.base i
  have distinct : (V.int (u64 i) == V.int 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro same
    have equal := V.int.inj (beq_iff_eq.mp same)
    omega
  cases hp
  cases nonzeroRule <;> cases cc
  all_goals isel_eval [*,rule_inst_5171,rule_inst_5173,sem_extract,sem_unData,sem_eq,base_eq,zero,stock_matchArgs,ccIdx]
end Backend.Stock.Proof.ScalarCmp
