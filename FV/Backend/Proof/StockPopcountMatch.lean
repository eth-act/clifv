import FV.Backend.Proof.StockScopedPopcountRhs
namespace Backend.Stock.Proof.Popcount
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (t : Nat) (v : V) :
    (Stock.sem ctx).unData t v = (Backend.sem ctx).unData t v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_prim (ctx : Ctx) (ty : Nat) (name : String) :
    (Stock.sem ctx).prim ty name = (Backend.sem ctx).prim ty name := rfl

theorem popcount_match {p : Program} (hp : Data p) (ctx : Ctx) {w i x : Nat} {info : IInfo}
    (width : IW w) (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w)) (data : info.data = .data 152 29 [.data 151 111 [],.value x])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) (popcountRule w) [.inst i]).run (st,tr) =
      .ok (some (popcountEnv w x),st,tr) := by
  have found := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at found
  rcases width with rfl | rfl | rfl | rfl
  all_goals
    cases hp
    isel_eval [*,popcountRule,popcountEnv,popcountAlloc,rule_lower_2074,rule_lower_2080,
      rule_lower_2086,rule_lower_2092,sem_extract,sem_unData,sem_eq,sem_prim]
end Backend.Stock.Proof.Popcount
