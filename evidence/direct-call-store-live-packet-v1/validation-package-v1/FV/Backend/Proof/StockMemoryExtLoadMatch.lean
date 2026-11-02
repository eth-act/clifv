import FV.Backend.Proof.StockMemoryExtLoadSelection

namespace Backend.Stock.Memory.ExtendedRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty t k : Nat) (fs : List V) :
    (Stock.sem ctx).unData ty (.data t k fs) = if t = ty then some (k,fs) else none :=
  Backend.Proof.sem_unData ctx ty t k fs
private theorem sem_i32 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I32" = some (.ty (.int 32)) := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl

/-- The actual memory root matches the original load data, retaining the entire
Stock state and binding the source pointer and flags in its typed environment. -/
theorem stock_match_extending_load {p : Program} (hp : Data p) (kind : Kind) (ctx : Ctx) {cfg : Config}
    {i x : Nat} {info : IInfo} {flags : Clif.MemFlags}
    (source : ctx.insts[i]? = some info)
    (data : info.data = .data 152 16 [.data 151 kind.sourceTag [],.value x,.op (.memFlags flags),.int 0])
    (little : flags.endianness ≠ some .big) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) cfg (n+2) kind.root [.inst i]).run (st,tr) =
      .ok (some (env3 (.value x) (.op (.memFlags flags)) (.int 0)),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data] at extraction
  have endian := (ext_little_or_native_endian_iff ctx st.base flags [.op (.memFlags flags)]).mpr ⟨little,rfl⟩
  cases kind <;> simp only [Kind.sourceTag,Kind.root] at * <;> cases hp <;>
    isel_eval [*,rule_lower_2647,rule_lower_2650,rule_lower_2653,rule_lower_2656,rule_lower_2659,rule_lower_2662,
      sem_extract,sem_unData,sem_i32,sem_eq]

end Backend.Stock.Memory.ExtendedRoots
