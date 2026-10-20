import FV.Backend.Proof.StockSretReturnContractWitness

/-! Ungated continuation draft, outside PR203: invert the actual revised
Stock gen_return constructor. Source-arity and full root/driver semantics still
need derivation under the original inputs. -/
namespace Backend.Stock.Proof.ReturnABIDraft
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def pins (ctx : Ctx) (count : Nat) : Option (List Reg) :=
  if (sigRets ctx.func.sig).any (·.purpose == .sret) then some [.x 8] else retRegs count
private def unpack (rss : List (List Reg)) : Option (List Reg) :=
  rss.mapM (fun | [r] => some r | _ => none)
private theorem gen_return_shape {ctx : Ctx} {rss : List (List Reg)} {st next : State} {value : V}
    (run : Stock.externCtor ctx T.gen_return [.regsVec rss] st = .ok (value,next)) :
    ∃ rs ps, pins ctx rss.length = some ps ∧ unpack rss = some rs ∧
      next = {st with base := st.base.emit (.rets (rs.zip ps))} ∧ value = .op .unit := by
  change (match pins ctx rss.length, unpack rss with
    | some ps,some rs => (ExtResult.ok (.op .unit,{st with base := st.base.emit (.rets (rs.zip ps))}) : ExtResult (V × State))
    | _,_ => ExtResult.unmodeled "gen_return register count") = ExtResult.ok (value,next) at run
  cases p : pins ctx rss.length with
  | none => rw [p] at run; cases r : unpack rss <;> rw [r] at run <;> cases run
  | some ps =>
    rw [p] at run
    cases r : unpack rss with
    | none => rw [r] at run; cases run
    | some rs => rw [r] at run; cases run; exact ⟨rs,ps,rfl,rfl,rfl,rfl⟩
#print axioms gen_return_shape
private def witnessCtx (sret : Bool) : Ctx := {sinkCtx with func := {sinkCtx.func with
  sig := {params := if sret then [⟨.i64,.none,.sret⟩] else [],returns := []}}}
private theorem gen_return_shape_witness (sret : Bool) :
    ∃ (ctx : Ctx) (next : State),
      Stock.externCtor ctx T.gen_return [.regsVec [[.vreg 192 .int]]] sinkState = .ok (.op .unit,next) ∧
      ∃ rs ps,pins ctx 1 = some ps ∧ unpack [[.vreg 192 .int]] = some rs ∧
        next = {sinkState with base := sinkState.base.emit (.rets (rs.zip ps))} := by
  let ctx := witnessCtx sret
  let ps : List Reg := [if sret then .x 8 else .x 0]
  let next : State := {sinkState with base := sinkState.base.emit (.rets ([.vreg 192 .int].zip ps))}
  have call : Stock.externCtor ctx T.gen_return [.regsVec [[.vreg 192 .int]]] sinkState = .ok (.op .unit,next) := by
    cases sret <;> rfl
  obtain ⟨rs,ps,selected,unpacked,state,_⟩ := gen_return_shape call
  exact ⟨ctx,next,call,rs,ps,selected,unpacked,state⟩
/-- Helper success alone does not imply return arity. The caller must derive
request arity from original source/signature facts; no accepted-input guard. -/
private theorem sret_request_arity_boundary :
    Stock.externCtor (witnessCtx true) T.gen_return
      [.regsVec [[.vreg 192 .int],[.vreg 193 .int]]] sinkState =
      .ok (.op .unit,{sinkState with base := sinkState.base.emit (.rets [(.vreg 192 .int,.x 8)])}) ∧
    unpack [[.vreg 192 .int],[.vreg 193 .int]] = some [.vreg 192 .int,.vreg 193 .int] ∧
    pins (witnessCtx true) 2 = some [.x 8] ∧ (2 : Nat) ≠ 1 := ⟨rfl,rfl,rfl,by decide⟩
#print axioms gen_return_shape_witness
#print axioms sret_request_arity_boundary
end Backend.Stock.Proof.ReturnABIDraft
