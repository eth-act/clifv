import FV.Backend.Proof.StockArithmeticBodyRefines
import FV.Backend.Proof.StockLogicalScanRefines

/-! Source-syntax coverage for complete select/arithmetic/logical bodies. -/
namespace Backend.Stock.Proof.LogicalBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Input syntax only; actual matching, binding and record decisions are derived. -/
def Family (inst : Clif.Inst) : Prop :=
  (∃ subtract : Bool, ∃ ty x y,
    inst = .binary (if subtract then .isub else .iadd) ty x y) ∨
  (∃ ty c x y, inst = .select ty c x y) ∨
  (∃ kind : LogicalSelected.Kind, ∃ ty x y, inst = .binary kind.cop ty x y)

private theorem family_result {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some inst)
    (family : Family inst) : ∃ z, info.results = [z] := by
  obtain ⟨tys,result,typed,arity⟩ := inv.resTys i info _ source clif
  have one : info.results.length = 1 := by
    rcases family with ⟨subtract,ty,x,y,shape⟩ | ⟨ty,c,x,y,shape⟩ | ⟨kind,ty,x,y,shape⟩
    all_goals
      rw [shape] at result
      have equal := Option.some.inj result
      rw [← equal] at arity
      simpa only [List.length_singleton] using arity
  cases values : info.results with
  | nil => simp [values] at one
  | cons z rest =>
    cases rest with
    | nil => exact ⟨z,rfl⟩
    | cons a tail => simp [values] at one

private theorem scans_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) :
    ∀ record ∈ output.records, exec record.inst record.input = .ok record.output := by
  induction cert with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

/-- Original syntax and successful lowering supply every body record's family,
source result, actual mapped register and emission/omission decision internally. -/
theorem actual_logical_families {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ term body, SourceBodySplit f event b term body ∧
      ∀ record ∈ body.records, MixedLogicalOrOmittedRecord f event.ctx event.block record := by
  have quiet : ∀ stm ∈ b.body, colored stm.inst = false := by
    intro stm member
    rcases family stm member with ⟨subtract,ty,x,y,shape⟩ | ⟨ty,c,x,y,shape⟩ | ⟨kind,ty,x,y,shape⟩
    all_goals rw [shape]
    · cases subtract <;> rfl
    · rfl
    · cases kind <;> rfl
  obtain ⟨term,body,split,decisions⟩ := stock_lower_pure_body_decisions run scope blocks quiet events
  refine ⟨term,body,split,?_⟩
  intro record member
  obtain ⟨j,stm,statement,current⟩ := split.positions record member
  obtain ⟨step,recorded,decision⟩ := decisions record member
  rcases decision with omitted | emitted
  · exact Or.inl (Or.inl ⟨j,b,stm,split.block,statement,current,step,recorded,Or.inl omitted⟩)
  · obtain ⟨info,source,clif,results⟩ :=
      ArithmeticBody.body_source_info run events split statement current
    have inv := (stock_lower_record_context run scope events).1
    have sourceFamily := family stm (List.mem_of_getElem? statement)
    obtain ⟨z,one⟩ := family_result inv source clif sourceFamily
    obtain ⟨emission,emissionRun,scan⟩ := stock_emitted_scan
      (scans_execute split.scanned record member) recorded emitted
    have atInst : event.ctx.insts[record.inst]! = info := by
      simp only [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,source,Option.getD_some]
    obtain ⟨r,mapped⟩ := ArithmeticBody.emission_result_mapped emissionRun
      (by rw [atInst]; exact one)
    obtain ⟨a,rfl⟩ := inv.valueReg z r mapped
    rcases sourceFamily with ⟨subtract,ty,x,y,shape⟩ | ⟨ty,c,x,y,shape⟩ | ⟨kind,ty,x,y,shape⟩
    · have original : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y) := by
        rw [clif,shape]
      exact Or.inl (Or.inr ⟨j,b,stm,split.block,statement,current,step,recorded,emitted,
        subtract,info,ty,x,y,z,a,source,original,one,results.symm.trans one,mapped⟩)
    · have original : info.clif = some (.select ty c x y) := by rw [clif,shape]
      exact Or.inl (Or.inl ⟨j,b,stm,split.block,statement,current,step,recorded,Or.inr
        ⟨emitted,info,ty,c,x,y,z,a,source,original,one,results.symm.trans one,mapped⟩⟩)
    · have original : info.clif = some (.binary kind.cop ty x y) := by rw [clif,shape]
      exact Or.inr ⟨j,b,stm,split.block,statement,current,step,recorded,emitted,
        kind,info,ty,x,y,z,a,source,original,one,results.symm.trans one,mapped⟩

/-- Whole ordinary-body refinement derives its record coverage and maps from
source syntax. The original indexed availability/DFG and memory/world boundary
is retained, including unused/dead statements and all prior body families. -/
theorem actual_logical_body_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ∃ term body, SourceBodySplit f event b term body ∧
      ∀ s s', SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block + ·)) s s' →
        ∀ ρ w, GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w → ∃ ρ' w',
          seqRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w =
            some (.fall ρ' w') ∧
          GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w' := by
  obtain ⟨term,body,split,families⟩ := actual_logical_families run scope blocks family events
  refine ⟨term,body,split,?_⟩
  intro s s' source ρ w held
  apply stock_lower_mixed_logical_body_fall_refines run scope dominated events
    split.scanned split.retained families refines stable s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using source
  · simpa only [split.state] using held

end Backend.Stock.Proof.LogicalBody
