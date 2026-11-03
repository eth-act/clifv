import FV.Backend.Proof.StockMemoryStoreMatch
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def flags : Clif.MemFlags := {trapCode := none}
private def fixture (kind : Kind) : Clif.Function := {
  name := "stock_store_source_match"
  sig := {
    params := [⟨.i64,.none,.normal⟩,⟨kind.sourceTy,.none,.normal⟩]
    returns := []
    callConv := some .systemV }
  blocks := [{
    id := 0
    params := [(0,.i64),(1,kind.sourceTy)]
    body := [⟨[],.store kind.sourceOp kind.sourceTy flags 1 0 0⟩]
    term := .ret [] }] }

private def built (kind : Kind) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (fixture kind)).toOption.getD (sinkCtx,#[],sinkState)
private def info (kind : Kind) : IInfo := (built kind).1.insts[0]!
private theorem build_ok (kind : Kind) : Stock.buildCtx (fixture kind) = .ok (built kind) := by
  cases kind <;> rfl
private theorem scope (kind : Kind) : LowerScope (fixture kind) := by
  cases kind <;> exact lowerScope_of rfl
private theorem source (kind : Kind) : (built kind).1.insts[0]? = some (info kind) := by
  cases kind <;> rfl
private theorem clif (kind : Kind) :
    (info kind).clif = some (.store kind.sourceOp kind.sourceTy flags 1 0 0) := by
  cases kind <;> rfl
private theorem typed (kind : Kind) : kind.sourceOp = .store →
    (built kind).1.valueType? 1 = some (.int kind.width.bits) := by
  cases kind <;> intro same <;> first | rfl | cases same

/-- Original build contexts inhabit all seven matching contracts without a selected-root certificate. -/
theorem integer_store_source_match_witness (kind : Kind) :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st : State) (info : IInfo),
      Stock.buildCtx f = .ok (ctx,ranges,st) ∧ LowerScope f ∧ ctx.insts[0]? = some info ∧
      info.clif = some (.store kind.sourceOp kind.sourceTy flags 1 0 0) ∧
      (matchRule program (Stock.sem ctx) {} 20 kind.root [.inst 0]).run (st,#[]) =
        .ok (some (env4 (.value 1) (.value 0) (.op (.memFlags flags)) (.int 0)),st,#[]) := by
  obtain ⟨little,data⟩ := integer_store_source_data kind
    (buildCtx_mappedInv (scope kind) (build_ok kind)) (source kind) (clif kind)
  have matched := stock_match_integer_store data_program kind (built kind).1
    (cfg := {}) (source kind) (typed kind) data little (built kind).2.2 #[] 0
  exact ⟨fixture kind,(built kind).1,(built kind).2.1,(built kind).2.2,info kind,
    build_ok kind,scope kind,source kind,clif kind,matched⟩

end Backend.Stock.Memory.StoreRoots
