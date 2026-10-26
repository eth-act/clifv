import FV.Backend.Proof.StockConditionalResolved
import FV.Backend.Proof.StockOriginalConditionPrefix
import FV.Backend.Proof.StockResolvedDefs
import FV.Backend.Proof.StockSequenceFrame
import FV.Backend.Proof.StockSelectCompanionFragment

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- The actual branch takes the original true/false edge and preserves every
register outside its real compiler allocation interval, including a removed
proof companion's number when an available source value resolves there. -/
def BranchExecution (F : BitVec 64 → Prop) (isem : Backend.Proof.Sem) (yes no : Label)
    (code : List MInst) (truth : Bool) (before next : LState) (ρ : Nat → CV) (world : Arm.ArmState) : Prop :=
  ∃ index inst ops regs prefixWorld endWorld,
    seqRun isem code ρ world = some (.stop index inst ops regs prefixWorld [] endWorld
      (.goto (if truth then 0 else 1))) ∧
    SameWorldNF F endWorld world ∧
    (∀ key,key < before.nextVreg ∨ next.nextVreg ≤ key → regs key = ρ key) ∧
    inst.targets = [yes,no] ∧ inst.isTerminator = true

private theorem framed_stop {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    {yes no : Label} {code : List MInst} {truth : Bool} {before next : LState}
    (fragment : Frag before next code) (aliases : Array (Option Nat)) (bounded : aliases.size ≤ before.nextVreg)
    {ρ regs : Nat → CV} {world prefixWorld endWorld : Arm.ArmState}
    {index : Nat} {inst : MInst} {ops : Array Operand}
    (run : seqRun isem (code.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world =
      some (.stop index inst ops regs prefixWorld [] endWorld (.goto (if truth then 0 else 1))))
    (nf : SameWorldNF F endWorld world) (targets : inst.targets = [yes,no]) (terminal : inst.isTerminator = true) :
    BranchExecution F isem yes no (code.map (·.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)))) truth before next ρ world := by
  refine ⟨index,inst,ops,regs,prefixWorld,endWorld,run,nf,?_,targets,terminal⟩
  intro key outside
  apply Sequence.stop_frame isem run key
  intro selected member defined
  have interval := Resolved.fragment_defs fragment aliases bounded selected member key defined
  rcases outside with lower | upper <;> omega

private theorem code_runs {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {yes no : Label} {raw : V} {suffix leading : List MInst}
    (compiled : BranchCode yes no raw suffix) {producer : MInst} {condition : Cond}
    (flags : CondFlag cmpImm0 raw producer condition) {before next : LState}
    (fragment : Frag before next (leading++suffix)) {aliases : Array (Option Nat)}
    (bounded : aliases.size ≤ before.nextVreg) {d : Nat} (fresh : aliases.size ≤ d)
    {truth : Bool} {ρ : Nat → CV} {world : Arm.ArmState}
    (run : Runs F isem ((leading++[producer,MInst.cset (.vreg d .int) condition]).map
      (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world
      (fun final _ => VHolds ⟨.i8,Clif.Sem.bool8 truth⟩ (final d))) :
    BranchExecution F isem yes no ((leading++suffix).map
      (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) truth before next ρ world := by
  have framed : Runs F isem ((leading++[producer,MInst.cset (.vreg d .int) condition]).map
      (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world
      (fun final _ => VHolds ⟨.i8,Clif.Sem.bool8 truth⟩ (final d) ∧ ∀ key,False → final key = ρ key) :=
    run.imp (fun final world _ value => ⟨value,fun key impossible => impossible.elim⟩)
  cases compiled with
  | zero key index size decoded =>
    rcases flags with ⟨key',index',size',equal,decoded',rfl,rfl⟩ |
      ⟨key',index',size',equal,decoded',rfl,rfl⟩ | ⟨mi,equal,parsed⟩
    all_goals simp at equal
    obtain ⟨rfl,rfl⟩ := equal
    rw [decoded] at decoded'
    cases decoded'
    obtain ⟨regs,prefixWorld,endWorld,actual,nf,_⟩ := zero_branch_resolved refines false size key fresh
      (P := fun _ => False) (fun _ h => h.elim) framed yes no
    exact framed_stop fragment aliases bounded actual nf rfl rfl
  | nonzero key index size decoded =>
    rcases flags with ⟨key',index',size',equal,decoded',rfl,rfl⟩ |
      ⟨key',index',size',equal,decoded',rfl,rfl⟩ | ⟨mi,equal,parsed⟩
    all_goals simp at equal
    obtain ⟨rfl,rfl⟩ := equal
    rw [decoded] at decoded'
    cases decoded'
    obtain ⟨regs,prefixWorld,endWorld,actual,nf,_⟩ := zero_branch_resolved refines true size key fresh
      (P := fun _ => False) (fun _ h => h.elim) framed yes no
    exact framed_stop fragment aliases bounded actual nf rfl rfl
  | flags rawInst actualProducer actualCondition decoded notAl notNv noDefs =>
    rcases flags with ⟨key',index',size',equal,decoded',rfl,rfl⟩ |
      ⟨key',index',size',equal,decoded',rfl,rfl⟩ | ⟨mi,equal,parsed⟩
    all_goals simp at equal
    obtain ⟨rfl,sameIndex⟩ := equal
    have same := cond_idx_inj sameIndex
    subst actualCondition
    rw [decoded] at parsed
    have sameProducer : actualProducer = producer := Option.some.inj parsed
    subst actualProducer
    have companion : Runs F isem (((leading++[producer])++[MInst.cset (.vreg d .int) condition]).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world
        (fun final _ => VHolds ⟨.i8,Clif.Sem.bool8 truth⟩ (final d) ∧ ∀ key,False → final key = ρ key) := by
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using framed
    obtain ⟨regs,prefixWorld,endWorld,actual,nf,_⟩ := flag_branch_resolved refines ⟨notAl,notNv⟩ fresh
      (P := fun _ => False) (fun _ h => h.elim) companion yes no
    simp only [List.append_assoc,List.cons_append,List.nil_append] at actual
    exact framed_stop fragment aliases bounded actual nf rfl rfl


/-- Original condition execution, actual descriptor construction and actual
emission derive complete source branch execution and its real register frame.
The boolean companion is constructed and removed internally; neither an
emitted-code certificate nor an inequality against its destination is assumed. -/
theorem original_source_branch_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cty : Clif.Ty} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {c : Nat} {test : BitVec cty.width} (getC : fr.getAs c cty = .ok test)
    (typedReads : ∀ {value : Nat} {ty : Clif.Ty} {bits : BitVec ty.width},
      fr.getAs value ty = .ok bits → ctx.valueType? value = some (.int ty.width))
    {conditionFuel constructFuel emitFuel : Nat}
    (enoughCondition : 400 ≤ conditionFuel) (enoughConstruct : 100 ≤ constructFuel) (enoughEmit : 30 ≤ emitFuel)
    {before middle constructed next : State} {trace conditionTrace constructTrace final : Array RuleId}
    {raw descriptor out : V} {yes no : Label}
    (conditionRun : ApplyInternal program (Stock.sem ctx) {} conditionFuel 123 650 [.value c]
      (before,trace) raw (middle,conditionTrace))
    (constructRun : ApplyInternal program (Stock.sem ctx) {} constructFuel 46 722
      [raw,.label yes,.label no] (middle,conditionTrace) descriptor (constructed,constructTrace))
    (emitRun : ApplyInternal program (Stock.sem ctx) {} emitFuel 13 242
      [descriptor] (constructed,constructTrace) out (next,final))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ before.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < before.demand.size)
    (held : ValuesHeld (Demanded middle) ctx fr (fun key => ρ (aliasNum aliases key)))
    (separatedReads : ∀ {value : Nat} {ty : Clif.Ty} {bits : BitVec ty.width},
      fr.getAs value ty = .ok bits → ∀ key,ctx.valueReg? value = some (.vreg key .int) →
        aliasNum aliases key ≠ before.base.nextVreg) :
    ∃ code,Frag before.base next.base code ∧
      ∀ world,BranchExecution F isem yes no (code.map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))))
        (test != 0) before.base next.base ρ world := by
  obtain ⟨leading,prefixFragment⟩ := original_prefix inv dfg getC typedReads enoughCondition conditionRun
  obtain ⟨producer,condition,booleanTrace,shape,flags,noDefs,notAl,notNv,companion,execution⟩ :=
    original_boolean_companion inv dfg getC typedReads enoughCondition conditionRun
      refines bounded extent held separatedReads
  obtain ⟨suffix,compiled,suffixFragment⟩ := descriptor_emits rfl enoughConstruct enoughEmit shape constructRun emitRun
  obtain ⟨d,booleanCode,output,lower,upper,booleanFragment,booleanRuns⟩ := execution
  change V.reg (.vreg middle.base.nextVreg .int) = V.reg (.vreg d .int) at output
  have destination : middle.base.nextVreg = d := (Reg.vreg.inj (V.reg.inj output)).1
  subst d
  have prefixBuffer : middle.base.emitted.toList = before.base.emitted.toList ++ leading := by
    simpa only [Array.toList_append,List.toList_toArray] using congrArg Array.toList prefixFragment.emitted
  have booleanCodeEq : booleanCode = leading ++ [producer,MInst.cset (.vreg middle.base.nextVreg .int) condition] := by
    have buffer := congrArg Array.toList booleanFragment.emitted
    simp only [LState.emit,LState.fresh,Array.toList_push,Array.toList_append,List.toList_toArray] at buffer
    rw [prefixBuffer] at buffer
    simp only [List.append_assoc,List.cons_append,List.nil_append] at buffer
    exact (List.append_cancel_left buffer).symm
  have fragment := prefixFragment.append suffixFragment
  refine ⟨leading++suffix,fragment,fun world => ?_⟩
  have value := (booleanRuns world).imp (fun final _ _ pair => pair.1)
  rw [booleanCodeEq] at value
  exact code_runs refines compiled flags fragment bounded (Nat.le_trans bounded prefixFragment.mono) value

end Backend.Stock.Proof.ConditionalValues
