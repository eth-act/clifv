import FV.Backend.Proof.StockOutgoingShape
import FV.Backend.Proof.PerEdgeSpillEntryFixture

namespace Backend.Stock.Proof.OutgoingShapeWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill
open Backend.Stock.Proof.SpillEntryFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private def built (indirect : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function indirect)).toOption.getD (sinkCtx,#[],default)
private theorem built_run (indirect : Bool) : Stock.buildCtx (function indirect) = .ok (built indirect) := by
  cases indirect <;> rfl
private def beforeArgs (indirect handler : Bool) : Array Reg :=
  if handler then #[.vreg (retV indirect+1) .int,.vreg (retV indirect+2) .int,.vreg 192 .int]
  else #[.vreg (retV indirect) .int,.vreg 192 .int]
private def Observed (indirect handler : Bool) : Prop :=
  (branchArgs (built indirect).1 (built indirect).2.2 0 (index handler)).toOption.map
    (fun pair => decide (pair.1 = beforeArgs indirect handler)) = some true
private theorem observed (indirect handler : Bool) : Observed indirect handler := by
  cases indirect <;> cases handler <;> unfold Observed <;> decide +kernel

/-- Complete direct/indirect TryCall sources inhabit whole-driver outgoing
class preservation and actual selected argument collection on normal/exception
routes. The real build's return/payload/ordinary registers form a nonempty
vector of exactly the original destination arity; checked allocation and
physical lowering succeed for these complete programs. -/
theorem stock_outgoing_shape_witness (indirect handler : Bool) :
    ∃ (result : Result) (prepared : EdgeVCode) (rf : RFunc) (af : AFunc)
      (ranges : Array (Nat × Nat)) (args : Array Reg) (next : State),
      Stock.lower (function indirect) = .ok result ∧ LowerScope (function indirect) ∧
      Dominated (function indirect) ∧ ArityOk (function indirect) ∧
      Stock.buildCtx (function indirect) = .ok (result.ctx,ranges,result.initial) ∧
      (∀ (b j : Nat) (row : Array (Array Reg)) (args : Array Reg),
        result.edgeArgs[b]? = some row → row[j]? = some args → ArgumentShape args) ∧
      branchArgs result.ctx result.initial 0 (index handler) = .ok (args,next) ∧
      args = beforeArgs indirect handler ∧ ArgumentShape args ∧
      (∃ (id : Nat) (sourceArgs : List Clif.TryArg) (target : Clif.Block),
        (destinations result.ctx.func.blocks[0]!.term)[index handler]? = some (id,sourceArgs) ∧
        result.ctx.func.block? id = some target ∧ args.size = target.params.length) ∧
      next.tryRegs = result.initial.tryRegs ∧
      prepareAt result.code result.edgeArgs = .ok prepared ∧
      rf = spillAllocAt prepared.code prepared.edges ∧
      checkAllocAt prepared.code prepared.edges rf = .ok () ∧ lowerRFunc prepared.code rf = .ok af := by
  obtain ⟨fixture⟩ := try_fixture indirect
  rcases fixture with ⟨result,prepared,rf,af,lowered,scope,dominated,arity,prepare,fallback,accepted,physical,metadata⟩
  have sourceBuild : ∃ ranges,Stock.buildCtx (function indirect) = .ok (result.ctx,ranges,result.initial) := by
    unfold Stock.lower at lowered
    dsimp only at lowered
    repeat' first
      | (solve | cases lowered)
      | simp only [bind,Except.bind,pure,Except.pure] at lowered
      | split at lowered
    cases lowered
    exact ⟨_,by assumption⟩
  obtain ⟨ranges,build⟩ := sourceBuild
  have same := Except.ok.inj (build.symm.trans (built_run indirect))
  have context := congrArg Prod.fst same
  have state := congrArg (fun q : Ctx × Array (Nat × Nat) × State => q.2.2) same
  have actual := observed indirect handler
  unfold Observed at actual
  rw [← context,← state] at actual
  cases called : branchArgs result.ctx result.initial 0 (index handler) with
  | error err => simp only [called,Except.toOption,Option.map_none] at actual; cases actual
  | ok pair =>
    obtain ⟨args,next⟩ := pair
    rw [called] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    obtain ⟨target,shape,frame⟩ := stock_branchArgs_shape build rfl called
    exact ⟨result,prepared,rf,af,ranges,args,next,lowered,scope,dominated,arity,build,
      stock_lower_outgoing_shape lowered,called,actual,shape,target,frame,prepare,fallback,accepted,physical⟩

end Backend.Stock.Proof.OutgoingShapeWitness
