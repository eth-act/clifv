import FV.Backend.Proof.StockDriverAliasClasses
import FV.Backend.Proof.StockTryAliasWitness
import FV.Backend.Proof.StockCriticalSplitWitness

namespace Backend.Stock.Proof.DriverAliasWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Flow Backend.Proof.Cov Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.BindingClassDraft Backend.Stock.Proof.ClassGrowthDraft Backend.Stock.Proof.DriverAliasClassDraft
open Backend.Stock.Proof.TryAliasFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower Stock.externCtor

/-- A complete original try-call source has a genuinely installed final alias,
whole-driver class consistency and a classed resolved payload. Actual raw,
global-checked fallback and physical stages all succeed; no alias premise is
supplied to the whole-driver theorem. -/
theorem stock_complete_driver_alias_classes_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧ ArityOk function ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      result.initial.tryRegs[1]? = some ([.vreg 193 .int],[.vreg 194 .int,.vreg 195 .int]) ∧
      (result.final.alias[194]?).join = some 193 ∧ AliasClasses result.final ∧
      ClassGrowth result.initial result.final ∧ result.final.tryRegs = result.initial.tryRegs ∧ Coverage.NoOpportunity result.final ∧
      (∀ r,RegCls result.code.classes r → RegCls result.code.classes
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) r)) ∧
      RegCls result.code.classes (.vreg 194 .int) ∧
      RegCls result.code.classes (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg 194 .int)) ∧
      result.code.blocks.any (fun b => b.insts.any isTryCall) = true ∧
      p.code.blocks.any (fun b => b.insts.any isTryCall) = true := by
  rcases HelperAliasWitnessDraft.stock_complete_try_alias_classes_witness with
    ⟨result,p,rf,af,ranges,value,after,lowered,scope,dominated,arity,prepared,fallback,checked,physical,
      build,slot,old,reserved,ctor,applied,named,afterAlias,finalAlias,afterClasses,reservedAfter,lateReserved,rawTry,preparedTry⟩
  have whole := stock_lower_alias_classes scope lowered
  have table := (WholeClassGrowthDraft.stock_lower_class_growth lowered).2.2.1
  have payload : RegCls result.code.classes (.vreg 194 .int) := by
    rw [regCls_vreg,table]
    exact (whole.1 194 193 finalAlias).1
  exact ⟨result,p,rf,af,lowered,scope,dominated,arity,prepared,fallback,checked,physical,slot,finalAlias,
    whole.1,whole.2.1,whole.2.2.1,whole.2.2.2.1,whole.2.2.2.2,payload,whole.2.2.2.2 _ payload,rawTry,preparedTry⟩

/-- Complete direct and indirect try-call sources exercise an actual critical
node in the same whole-driver class theorem. The unreachable source predecessor
is retained in the original input and contributes to forced splitting. -/
theorem stock_complete_critical_driver_alias_classes_witness (indirect : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc),
      Stock.lower (CriticalSplitFixture.function indirect) = .ok result ∧
      LowerScope (CriticalSplitFixture.function indirect) ∧ Dominated (CriticalSplitFixture.function indirect) ∧
      ArityOk (CriticalSplitFixture.function indirect) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      (CriticalSplitFixture.function indirect).blocks.length = 3 ∧
      Node.original 2 ∉ result.order.nodes.toList ∧ result.order.nodes[1]? = some (.edge 0 0 1) ∧
      AliasClasses result.final ∧ ClassGrowth result.initial result.final ∧
      result.final.tryRegs = result.initial.tryRegs ∧ Coverage.NoOpportunity result.final ∧
      (∀ r,RegCls result.code.classes r → RegCls result.code.classes
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) r)) := by
  rcases CriticalSplitWitness.stock_single_try_forced_split_witness indirect with
    ⟨result,p,rf,af,source,degree,lowered,scope,dominated,arity,prepared,fallback,checked,physical,
      sourceRun,sourceEq,counted,degreeEq,complete,single,shared,unreachable,edgeMember,edge,more⟩
  have whole := stock_lower_alias_classes scope lowered
  exact ⟨result,p,rf,af,lowered,scope,dominated,arity,prepared,fallback,checked,physical,
    rfl,unreachable,edge,whole.1,whole.2.1,whole.2.2.1,whole.2.2.2.1,whole.2.2.2.2⟩

end Backend.Stock.Proof.DriverAliasWitnessDraft
