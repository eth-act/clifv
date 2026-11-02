import FV.Backend.Lowering.Stock
import FV.Backend.Proof.DriverCheck

/-! The actual revised Stock return constructor. Return pins follow the source
signature, including the implicit struct pointer in x8. Legacy contracts remain
unchanged. Source request arity is a separate derived semantic obligation. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

def returnPins (f : Clif.Function) (count : Nat) : Option (List Reg) :=
  if (sigRets f.sig).any (·.purpose == .sret) then some [.x 8] else retRegs count

def unpackReturnRegs (rss : List (List Reg)) : Option (List Reg) :=
  rss.mapM (fun | [r] => some r | _ => none)

/-- Successful actual return construction derives its complete register list,
pin selection, exact code and complete Stock state. No legacy constructor
projection is assumed for this revised helper. -/
theorem stock_gen_return_shape {ctx : Ctx} {rss : List (List Reg)} {st next : State} {value : V}
    (run : Stock.externCtor ctx T.gen_return [.regsVec rss] st = .ok (value,next)) :
    ∃ rs ps,returnPins ctx.func rss.length = some ps ∧ unpackReturnRegs rss = some rs ∧
      next = {st with base := st.base.emit (.rets (rs.zip ps))} ∧ value = .op .unit := by
  change (match returnPins ctx.func rss.length,unpackReturnRegs rss with
    | some ps,some rs => (ExtResult.ok (.op .unit,{st with base := st.base.emit (.rets (rs.zip ps))}) : ExtResult (V × State))
    | _,_ => ExtResult.unmodeled "gen_return register count") = ExtResult.ok (value,next) at run
  cases p : returnPins ctx.func rss.length with
  | none => rw [p] at run; cases r : unpackReturnRegs rss <;> rw [r] at run <;> cases run
  | some ps =>
    rw [p] at run
    cases r : unpackReturnRegs rss with
    | none => rw [r] at run; cases run
    | some rs => rw [r] at run; cases run; exact ⟨rs,ps,rfl,rfl,rfl,rfl⟩
end Backend.Stock.Proof
