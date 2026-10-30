import FV.Backend.Proof.IselCmpEmit
import FV.Backend.Lowering.Stock
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
section Integers
attribute [local semireducible] Isle.Aarch64.program
private theorem zero (ctx : Ctx) : (Stock.sem ctx).int 4 0 = .int 0 := rfl
end Integers
/-- Original zero constant data matches the actual equality/inequality rule,
with the exact one-variable environment and unchanged complete state and trace. -/
theorem stock_cmp_zero_right_match {p : Program} (hp : Data p) (ctx : Ctx)
    (nonzero : Bool) {x y j : Nat} {info : IInfo} {i : Int}
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i]) (normalized : u64 i = 0)
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) (if nonzero then rule_inst_5172 else rule_inst_5170)
      [.data 145 (if nonzero then ccIdx .ne else ccIdx .eq) [],.value x,.value y]).run (st,tr) =
      .ok (some (#[some (.value x)]),st,tr) := by
  have definition := ext_def_inst_some ctx st.base defined
  have instruction := ext_inst_data_value ctx st.base found
  rw [data] at instruction
  have literal := ext_u64_from_imm64 ctx st.base i
  rw [normalized] at literal
  cases hp
  cases nonzero
  all_goals isel_eval [*,rule_inst_5170,rule_inst_5172,sem_extract,sem_unData,sem_eq,zero,ccIdx,show (V.int (0 : Nat) == V.int (0 : Int)) = true from rfl]
  all_goals apply congrArg (fun env : Isle.Interp.Env V => Except.ok (some env,st,tr))
  all_goals apply Array.toList_inj.mp
  all_goals simp [Array.toList_setIfInBounds,List.set,List.replicate]
end Backend.Stock.Proof.ScalarCmp
