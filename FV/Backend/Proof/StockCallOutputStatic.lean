import FV.Backend.Proof.StockReturnStatic
import FV.Backend.Proof.IselShpCall
namespace Backend.Stock.Proof.CallOutputStaticDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem output_fold {α : Type} (xs : List α) : ∀ (acc : List (List Reg)) (st : LState),
    xs.foldl (fun (p : List (List Reg) × LState) (_ : α) =>
      (p.1 ++ [[(p.2.fresh .int).1]],(p.2.fresh .int).2)) (acc,st) =
      (acc ++ outRegs st xs.length,freshN st xs.length) := by
  induction xs with
  | nil => intro acc st; simp [outRegs,freshN]
  | cons x xs ih =>
    intro acc st
    rw [List.foldl_cons,ih]
    simp only [List.length_cons,freshN,Prod.mk.injEq,and_true]
    simp [outRegs,LState.fresh,List.range_succ_eq_map,Function.comp_def,Nat.add_assoc,
      Nat.add_comm 1,List.append_assoc]

/-- Actual Stock call outputs allocate exactly one fresh integer virtual per
EXPLICIT return, preserving all scheduling fields and the emitted buffer.
Implicit sret results are intentionally absent from this caller-side vector. -/
theorem stock_gen_call_output_exact (ctx : Ctx) (sig : Clif.Signature) (st : State) :
    Stock.externCtor ctx T.gen_call_output [.op (.sig sig)] st =
      .ok (.regsVec (outRegs st.base sig.returns.length),
        {st with base := freshN st.base sig.returns.length}) := by
  change (let result := sig.returns.foldl (fun (p : List (List Reg) × LState) (_ : Clif.AbiParam) =>
      (p.1 ++ [[(p.2.fresh .int).1]],(p.2.fresh .int).2)) ([],st.base)
    ExtResult.ok (V.regsVec result.1,{st with base := result.2})) = _
  rw [output_fold]
  rfl

private theorem delegated {ctx : Ctx} {term : Term} {args : List V} {st next : State} {out : V}
    (ordinary : term.id ∉ revisedCtors)
    (run : Stock.externCtor ctx term args st = .ok (out,next)) :
    ∃ base,Backend.externCtor ctx term args st.base = .ok (out,base) ∧ next = {st with base} := by
  rw [stock_ctor_baseOnly _ _ _ _ ordinary] at run
  cases call : Backend.externCtor ctx term args st.base with
  | fail => rw [call] at run; cases run
  | unmodeled e => rw [call] at run; cases run
  | ok pair =>
    rcases pair with ⟨value,base⟩
    rw [call] at run
    cases run
    exact ⟨base,rfl,rfl⟩

/-- Actual output allocation followed by the actual return-pin helper derives
fresh, pairwise distinct ABI definitions. Its successful helper itself supplies
the at-most-eight bound; no new accepted-source or output certificate is used. -/
theorem stock_gen_call_rets_fresh_defs {ctx : Ctx} {sig : Clif.Signature}
    {before after final : State} {outs rets : V}
    (output : Stock.externCtor ctx T.gen_call_output [.op (.sig sig)] before = .ok (outs,after))
    (pinned : Stock.externCtor ctx T.gen_call_rets [.op (.sig sig),outs] after = .ok (rets,final)) :
    outs = .regsVec (outRegs before.base sig.returns.length) ∧
      after = {before with base := freshN before.base sig.returns.length} ∧
      final = after ∧ sig.returns.length ≤ 8 ∧
      rets = .op (.callRets (callDefs (outDefs before.base.nextVreg sig.returns.length))) ∧
      CallOk before.base.nextVreg [] (outDefs before.base.nextVreg sig.returns.length) ∧
      (∀ q ∈ outDefs before.base.nextVreg sig.returns.length,
        before.base.nextVreg ≤ q.2 ∧ q.2 < after.base.nextVreg) ∧
      after.base.emitted = before.base.emitted := by
  rw [stock_gen_call_output_exact] at output
  cases output
  obtain ⟨base,legacy,state⟩ := delegated (by decide) pinned
  obtain ⟨ps,rs,pins,unpacked,value,baseEq⟩ := (ctor_gen_call_rets_iff _ _ _ _ _).mp legacy
  rw [outRegs_length] at pins
  rw [outRegs_single] at unpacked
  cases unpacked
  obtain ⟨bound,pinShape⟩ := retRegs_eq pins
  rw [pinShape,callDefs_outDefs] at value
  have full : final = {before with base := freshN before.base sig.returns.length} := by
    rw [state,baseEq]
  have defs : CallOk before.base.nextVreg [] (outDefs before.base.nextVreg sig.returns.length) :=
    callOk_of (N := before.base.nextVreg) (b := before.base.nextVreg) (k := sig.returns.length)
      (Nat.le_refl _) bound (s := {callConv := some .systemV}) (by decide)
      (locs := []) (S := 0) rfl [] []
  refine ⟨rfl,rfl,full,bound,value,defs,?_,freshN_emitted _ _⟩
  intro q member
  obtain ⟨j,below,rfl⟩ := mem_outDefs member
  simp only [freshN_nextVreg]
  omega
end Backend.Stock.Proof.CallOutputStaticDraft
