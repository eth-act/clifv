import FV.Backend.Proof.StockMemoryAccessSourceTrap
import FV.Backend.Proof.StockFenceSourceRefines
import FV.Backend.Proof.LowerSim

/-! Draft: preserve actual source reachability inside the proof relation.
This relation is internal and adds no compiler acceptance condition. -/
namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

def pointState (initial : Clif.State) (point : SourcePoint) : Clif.State :=
  {initial with frame := point.2.1,mem := point.2.2}

private theorem ordinary_outcome {env : Clif.Env} {cp : Clif.Program}
    {fr : Clif.Frame} {cm : Clif.Mem} {inst : Clif.Inst}
    (family : OrdinaryBody.OrdinaryInst inst) :
    instOutcome env cp fr cm inst = Clif.evalInst fr cm inst := by
  cases inst <;> try rfl
  all_goals first
    | exact False.elim (family.1 _ _ rfl)
    | exact False.elim (family.2 _ _ _ rfl)

/-- An indexed original ordinary step is the actual next Clif step. -/
theorem ordinary_result_next {ctx : Ctx} {i : Nat} {env : Clif.Env} {cp : Clif.Program}
    (initial : Clif.State) {before after : SourcePoint}
    (ordinary : ∀ info inst,ctx.insts[i]? = some info → info.clif = some inst →
      OrdinaryBody.OrdinaryInst inst)
    (source : SourceInstResult env cp ctx i before.2 after.2) :
    Clif.step env cp (pointState initial before) = .next (pointState initial after) := by
  obtain ⟨info,inst,values,regs,rest,found,original,remaining,outcome,written,frame⟩ := source
  have family := ordinary info inst found original
  rw [ordinary_outcome family] at outcome
  rw [Clif.step_inst env cp (pointState initial before) ⟨info.results,inst⟩ rest remaining
    family.1 family.2]
  simp only [pointState] at *
  rw [outcome]
  simp only [Clif.StepResult.ofRes,Clif.continueWith,written]
  rw [frame]
  rfl

/-- An indexed original ordinary trap is the actual trapped Clif step. -/
theorem ordinary_trap_step {f : Clif.Function} {ctx : Ctx} {bi i : Nat}
    {env : Clif.Env} {cp : Clif.Program} (initial : Clif.State) {point : SourcePoint}
    {code : Clif.TrapCode}
    (ordinary : ∀ info inst,ctx.insts[i]? = some info → info.clif = some inst →
      OrdinaryBody.OrdinaryInst inst)
    (source : LocalBody.IndexedSourceTrap env cp f ctx bi i point code) :
    Clif.step env cp (pointState initial point) = .trapped code := by
  obtain ⟨index,info,inst,rest,found,original,remaining,outcome⟩ := source
  have family := ordinary info inst found original
  rw [ordinary_outcome family] at outcome
  rw [Clif.step_inst env cp (pointState initial point) ⟨info.results,inst⟩ rest remaining
    family.1 family.2]
  simp only [pointState] at *
  rw [outcome]
  rfl

/-- Keep the original guarded relation and actual source reachability together. -/
def ReachedGuardedRel (f : Clif.Function) (result : Result) (ctx : Ctx) (bi : Nat)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (initial : Clif.State)
    (state : State) (point : SourcePoint) (ρ : Nat → CV) (world : Arm.ArmState) : Prop :=
  GuardedScanRel f result ctx bi MR state point ρ world ∧
    Reach env cp initial (pointState initial point)

/-- Existing local success proofs preserve the added reachability invariant. -/
theorem guarded_with_reach {f : Clif.Function} {result : Result} {ctx : Ctx} {bi : Nat}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (initial : Clif.State)
    {isem : Backend.Proof.Sem} {record : ScanRecord}
    (ordinary : ∀ info inst,ctx.insts[record.inst]? = some info → info.clif = some inst →
      OrdinaryBody.OrdinaryInst inst)
    (normal : ScanFallRefines (IndexedSourceInst env cp f ctx bi) isem result.final.alias
      (GuardedScanRel f result ctx bi MR) record) :
    ScanFallRefines (IndexedSourceInst env cp f ctx bi) isem result.final.alias
      (ReachedGuardedRel f result ctx bi MR env cp initial) record := by
  intro before after source ρ world related
  obtain ⟨regs,next,executed,guarded⟩ := normal before after source ρ world related.1
  exact ⟨regs,next,executed,guarded,
    related.2.snoc (ordinary_result_next initial ordinary source.2.2)⟩

/-- A real source load fault gives the exact memory-trap event used by MapFaults. -/
theorem indexed_load_memtrap_at {f : Clif.Function} {ctx : Ctx} {bi i : Nat} {info : IInfo}
    {env : Clif.Env} {cp : Clif.Program} (initial : Clif.State) {point : SourcePoint}
    {code : Clif.TrapCode} {op : Clif.LoadOp} {ty : Clif.Ty} {flags : Clif.MemFlags}
    {pointer : Nat} {offset : Int} (found : ctx.insts[i]? = some info)
    (original : info.clif = some (.load op ty flags pointer offset))
    (failed : LocalBody.IndexedSourceTrap env cp f ctx bi i point code) :
    ∃ value,point.2.1.get pointer = .ok value ∧
      Clif.MemTrapAt env cp (pointState initial point) code (Clif.effAddr value offset) (op.size ty) ∧
      flags.trapCode = some code := by
  obtain ⟨value,pointerValue,access,invalid,flag⟩ := indexed_source_load_trap found original failed
  have ordinary : ∀ actual inst,ctx.insts[i]? = some actual → actual.clif = some inst →
      OrdinaryBody.OrdinaryInst inst := by
    intro actual inst present source
    cases Option.some.inj (present.symm.trans found)
    cases Option.some.inj (source.symm.trans original)
    constructor
    · intro fn args impossible
      cases impossible
    · intro sig callee args impossible
      cases impossible
  have trapped := ordinary_trap_step initial ordinary failed
  obtain ⟨index,actual,inst,rest,present,source,remaining,outcome⟩ := failed
  cases Option.some.inj (present.symm.trans found)
  cases Option.some.inj (source.symm.trans original)
  exact ⟨value,pointerValue,⟨trapped,invalid,⟨⟨info.results,.load op ty flags pointer offset⟩,
    rest,remaining,access⟩⟩,flag⟩

/-- MapFaults supplies the load's world property from actual source reachability. -/
theorem indexed_load_property {f : Clif.Function} {ctx : Ctx} {bi i : Nat} {info : IInfo}
    {env : Clif.Env} {cp : Clif.Program} (initial : Clif.State) {point : SourcePoint}
    {code : Clif.TrapCode} {op : Clif.LoadOp} {ty : Clif.Ty} {flags : Clif.MemFlags}
    {pointer : Nat} {offset : Int} (Q : Nat → Nat → Prop)
    (allFaults : ∀ state a n,Reach env cp initial state → Clif.MemTrapAt env cp state code a n → Q a n)
    (reached : Reach env cp initial (pointState initial point))
    (found : ctx.insts[i]? = some info) (original : info.clif = some (.load op ty flags pointer offset))
    (failed : LocalBody.IndexedSourceTrap env cp f ctx bi i point code) :
    ∃ value,point.2.1.get pointer = .ok value ∧
      Q (Clif.effAddr value offset) (op.size ty) ∧ flags.trapCode = some code := by
  obtain ⟨value,pointerValue,access,flag⟩ := indexed_load_memtrap_at initial found original failed
  exact ⟨value,pointerValue,allFaults _ _ _ reached access,flag⟩

/-- A real source store fault gives the exact memory-trap event used by MapFaults. -/
theorem indexed_store_memtrap_at {f : Clif.Function} {ctx : Ctx} {bi i : Nat} {info : IInfo}
    {env : Clif.Env} {cp : Clif.Program} (initial : Clif.State) {point : SourcePoint}
    {code : Clif.TrapCode} {op : Clif.StoreOp} {ty : Clif.Ty} {flags : Clif.MemFlags}
    {stored pointer : Nat} {offset : Int} (found : ctx.insts[i]? = some info)
    (original : info.clif = some (.store op ty flags stored pointer offset))
    (failed : LocalBody.IndexedSourceTrap env cp f ctx bi i point code) :
    ∃ value,point.2.1.get pointer = .ok value ∧
      Clif.MemTrapAt env cp (pointState initial point) code (Clif.effAddr value offset) (op.size ty) ∧
      flags.trapCode = some code := by
  obtain ⟨value,pointerValue,access,invalid,flag⟩ := indexed_source_store_trap found original failed
  have ordinary : ∀ actual inst,ctx.insts[i]? = some actual → actual.clif = some inst →
      OrdinaryBody.OrdinaryInst inst := by
    intro actual inst present source
    cases Option.some.inj (present.symm.trans found)
    cases Option.some.inj (source.symm.trans original)
    constructor
    · intro fn args impossible
      cases impossible
    · intro sig callee args impossible
      cases impossible
  have trapped := ordinary_trap_step initial ordinary failed
  obtain ⟨index,actual,inst,rest,present,source,remaining,outcome⟩ := failed
  cases Option.some.inj (present.symm.trans found)
  cases Option.some.inj (source.symm.trans original)
  exact ⟨value,pointerValue,⟨trapped,invalid,⟨⟨info.results,.store op ty flags stored pointer offset⟩,
    rest,remaining,access⟩⟩,flag⟩

/-- MapFaults supplies the store's world property from actual source reachability. -/
theorem indexed_store_property {f : Clif.Function} {ctx : Ctx} {bi i : Nat} {info : IInfo}
    {env : Clif.Env} {cp : Clif.Program} (initial : Clif.State) {point : SourcePoint}
    {code : Clif.TrapCode} {op : Clif.StoreOp} {ty : Clif.Ty} {flags : Clif.MemFlags}
    {stored pointer : Nat} {offset : Int} (Q : Nat → Nat → Prop)
    (allFaults : ∀ state a n,Reach env cp initial state → Clif.MemTrapAt env cp state code a n → Q a n)
    (reached : Reach env cp initial (pointState initial point))
    (found : ctx.insts[i]? = some info) (original : info.clif = some (.store op ty flags stored pointer offset))
    (failed : LocalBody.IndexedSourceTrap env cp f ctx bi i point code) :
    ∃ value,point.2.1.get pointer = .ok value ∧
      Q (Clif.effAddr value offset) (op.size ty) ∧ flags.trapCode = some code := by
  obtain ⟨value,pointerValue,access,flag⟩ := indexed_store_memtrap_at initial found original failed
  exact ⟨value,pointerValue,allFaults _ _ _ reached access,flag⟩

end Backend.Stock.Proof.MemoryFaults
