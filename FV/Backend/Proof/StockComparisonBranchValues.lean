import FV.Backend.Proof.StockConditionalGuardedValues
import FV.Backend.Proof.StockConditionalCallValues
import FV.Backend.Proof.StockComparisonBranchFacts
import FV.Backend.Proof.StockComparisonBranchSelection

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open ScalarCmp ScalarSelect
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `BranchExecution` whose stop is at the last instruction of the code. -/
def LastBranchExecution (F : BitVec 64 → Prop) (isem : Backend.Proof.Sem) (yes no : Label)
    (code : List MInst) (truth : Bool) (before next : LState) (ρ : Nat → CV) (world : Arm.ArmState) : Prop :=
  ∃ index inst ops regs prefixWorld endWorld,
    seqRun isem code ρ world = some (.stop index inst ops regs prefixWorld [] endWorld
      (.goto (if truth then 0 else 1))) ∧
    index+1 = code.length ∧ SameWorldNF F endWorld world ∧
    (∀ key,key < before.nextVreg ∨ next.nextVreg ≤ key → regs key = ρ key) ∧
    inst.targets = [yes,no] ∧ inst.isTerminator = true

private theorem framed_stop {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    {yes no : Label} {code : List MInst} {truth : Bool} {before next : LState}
    (fragment : Frag before next code) (aliases : Array (Option Nat)) (bounded : aliases.size ≤ before.nextVreg)
    {ρ regs : Nat → CV} {world prefixWorld endWorld : Arm.ArmState}
    {index : Nat} {inst : MInst} {ops : Array Operand}
    (run : seqRun isem (code.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world =
      some (.stop index inst ops regs prefixWorld [] endWorld (.goto (if truth then 0 else 1))))
    (nf : SameWorldNF F endWorld world) (targets : inst.targets = [yes,no]) (terminal : inst.isTerminator = true)
    (last : index+1 = code.length) :
    LastBranchExecution F isem yes no (code.map (·.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)))) truth before next ρ world := by
  refine ⟨index,inst,ops,regs,prefixWorld,endWorld,run,by simpa only [List.length_map] using last,nf,?_,targets,terminal⟩
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
    LastBranchExecution F isem yes no ((leading++suffix).map
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
    exact framed_stop fragment aliases bounded actual nf rfl rfl (by simp)
  | nonzero key index size decoded =>
    rcases flags with ⟨key',index',size',equal,decoded',rfl,rfl⟩ |
      ⟨key',index',size',equal,decoded',rfl,rfl⟩ | ⟨mi,equal,parsed⟩
    all_goals simp at equal
    obtain ⟨rfl,rfl⟩ := equal
    rw [decoded] at decoded'
    cases decoded'
    obtain ⟨regs,prefixWorld,endWorld,actual,nf,_⟩ := zero_branch_resolved refines true size key fresh
      (P := fun _ => False) (fun _ h => h.elim) framed yes no
    exact framed_stop fragment aliases bounded actual nf rfl rfl (by simp)
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
    exact framed_stop fragment aliases bounded actual nf rfl rfl (by simp)


private theorem compose_branch_values {ctx : Ctx}
    {constructFuel emitFuel : Nat} (enoughConstruct : 100 ≤ constructFuel) (enoughEmit : 30 ≤ emitFuel)
    {before middle constructed next : State} {conditionTrace constructTrace final : Array RuleId}
    {raw descriptor out : V} {yes no : Label}
    (constructRun : ApplyInternal program (Stock.sem ctx) {} constructFuel 46 722
      [raw,.label yes,.label no] (middle,conditionTrace) descriptor (constructed,constructTrace))
    (emitRun : ApplyInternal program (Stock.sem ctx) {} emitFuel 13 242
      [descriptor] (constructed,constructTrace) out (next,final))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ before.base.nextVreg)
    {leading : List MInst} (prefixFragment : Frag before.base middle.base leading)
    (shape : CondShape raw (fun _ => True)) {producer : MInst} {condition : Cond}
    (flags : CondFlag cmpImm0 raw producer condition) {truth : Bool}
    (execution : BooleanExecution F isem aliases truth before
      {middle with base := (((middle.base.fresh .int).2.emit producer).emit
        (.cset (middle.base.fresh .int).1 condition))}
      (.reg (middle.base.fresh .int).1) ρ) :
    ∃ code,Frag before.base next.base code ∧
      ∀ world,LastBranchExecution F isem yes no (code.map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))))
        truth before.base next.base ρ world := by
  obtain ⟨suffix,compiled,suffixFragment⟩ := descriptor_emits rfl enoughConstruct enoughEmit shape constructRun emitRun
  obtain ⟨d,booleanCode,output,lower,upper,booleanFragment,booleanRuns⟩ := execution
  change V.reg (.vreg middle.base.nextVreg .int) = V.reg (.vreg d .int) at output
  have destination : middle.base.nextVreg = d := (Reg.vreg.inj (V.reg.inj output)).1
  subst d
  have prefixBuffer : middle.base.emitted.toList = before.base.emitted.toList ++ leading := by
    simpa only [Array.toList_append,List.toList_toArray] using congrArg Array.toList prefixFragment.emitted
  have booleanCodeEq : booleanCode = leading ++ [producer,MInst.cset (.vreg middle.base.nextVreg .int) condition] := by
    have buffer := congrArg Array.toList booleanFragment.emitted
    simp only [LState.emit,LState.fresh,Array.toList_push,Array.toList_append] at buffer
    rw [prefixBuffer] at buffer
    simp only [List.append_assoc,List.cons_append,List.nil_append] at buffer
    exact (List.append_cancel_left buffer).symm
  have fragment := prefixFragment.append suffixFragment
  refine ⟨leading++suffix,fragment,fun world => ?_⟩
  have value := (booleanRuns world).imp (fun final _ _ pair => pair.1)
  rw [booleanCodeEq] at value
  exact code_runs refines compiled flags fragment bounded (Nat.le_trans bounded prefixFragment.mono) value

/-- `original_boolean_companion` for a direct wide comparison: the narrow
comparison cases are excluded by the operand type, so no scratch separation
is needed. -/
private theorem comparison_boolean_companion {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cty : Clif.Ty} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {c : Nat} {test : BitVec cty.width} (getC : fr.getAs c cty = .ok test)
    (typedReads : ∀ {value : Nat} {ty : Clif.Ty} {bits : BitVec ty.width},
      fr.getAs value ty = .ok bits → ctx.valueType? value = some (.int ty.width))
    {fuel : Nat} (enough : 400 ≤ fuel) {before middle : State}
    {trace emitTrace : Array RuleId} {raw : V}
    (emitter : ApplyInternal program (Stock.sem ctx) {} fuel 123 650 [.value c]
      (before,trace) raw (middle,emitTrace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ before.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < before.demand.size)
    (held : ValuesHeld (Demanded middle) ctx fr (fun key => ρ (aliasNum aliases key)))
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat} (origin : ctx.defClif? c = some (.icmp cc ty x y))
    (wide : Bool) (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32))) :
    ∃ producer condition booleanTrace,
      CondShape raw (fun _ => True) ∧ CondFlag cmpImm0 raw producer condition ∧
      vdefs producer = [] ∧ condition ≠ .al ∧ condition ≠ .nv ∧
      ApplyInternal program (Stock.sem ctx) {} 119 27 715 [raw] (middle,emitTrace)
        (.reg (middle.base.fresh .int).1)
        ({middle with base := (((middle.base.fresh .int).2.emit producer).emit
          (.cset (middle.base.fresh .int).1 condition))},booleanTrace) ∧
      BooleanExecution F isem aliases (test != 0) before
        {middle with base := (((middle.base.fresh .int).2.emit producer).emit
          (.cset (middle.base.fresh .int).1 condition))}
        (.reg (middle.base.fresh .int).1) ρ := by
  have supported : ∀ {value : Nat} {ty : Clif.Ty} {bits : BitVec ty.width},
      fr.getAs value ty = .ok bits →
      ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := by
    intro value ty bits read
    have type := typedReads read
    have valid := inv.valTyE value (.int ty.width) type
    cases ty <;> simp [eCTys,Clif.Ty.width] at valid ⊢
  rcases stock_original_select_condition_calls inv enough emitter with
    ⟨helperFuel,helperTrace,enoughHelper,nonzero⟩ |
    ⟨cc',ty',a,b,origin',helperFuel,helperTrace,enoughHelper,comparison⟩
  · have shape := stock_select_nonzero_actual_condition_shape inv (supported getC) (by omega) (typedReads getC) nonzero
    obtain ⟨producer,condition,booleanTrace,flags,noDefs,notAl,notNv,companion⟩ :=
      stock_select_condition_boolean_companion ctx shape middle emitTrace
    have execution := nonzero_boolean_values inv (supported getC) dfg getC (typedReads getC)
      (by omega) (by decide) nonzero companion refines bounded extent held
    exact ⟨producer,condition,booleanTrace,shape,flags,noDefs,notAl,notNv,companion,execution⟩
  · obtain ⟨av,bv,getA,getB,truth⟩ := stock_select_comparison_origin_values dfg origin' (getAs_ok getC)
    have shape := stock_select_comparison_condition_shape inv (supported getA) cc'
      (typedReads getA) (typedReads getB) enoughHelper comparison
    obtain ⟨producer,condition,booleanTrace,flags,noDefs,notAl,notNv,companion⟩ :=
      stock_select_condition_boolean_companion ctx shape middle emitTrace
    have sameOperand : a = x := by
      rcases origin' with direct | ⟨target,z,extension,_⟩
      · rw [origin] at direct
        simp only [Option.some.injEq,Clif.Inst.icmp.injEq] at direct
        exact direct.2.2.1.symm
      · rw [origin] at extension
        simp at extension
    subst sameOperand
    have execution : ScalarCmp.CmpExecution F isem aliases cc' ty' av bv before
        {middle with base := (((middle.base.fresh .int).2.emit producer).emit
          (.cset (middle.base.fresh .int).1 condition))}
        (.reg (middle.base.fresh .int).1) ρ := by
      cases ty'
      · have narrow := typedReads getA
        rw [typeX] at narrow
        cases wide <;> simp [Clif.Ty.width] at narrow
      · have narrow := typedReads getA
        rw [typeX] at narrow
        cases wide <;> simp [Clif.Ty.width] at narrow
      · exact stock_cmp_wide_actual_emitter_values inv false cc' rfl dfg getA getB
          (typedReads getA) (typedReads getB) enoughHelper (by decide) comparison companion
          refines bounded extent held
      · exact stock_cmp_wide_actual_emitter_values inv true cc' rfl dfg getA getB
          (typedReads getA) (typedReads getB) enoughHelper (by decide) comparison companion
          refines bounded extent held
      · have impossible := supported getA
        simp [Clif.Ty.width] at impossible
      all_goals cases getAs_typed dfg (typedReads getA) getA
    refine ⟨producer,condition,booleanTrace,shape,flags,noDefs,notAl,notNv,companion,?_⟩
    change (test != 0) = Clif.Sem.intcc cc' av bv at truth
    rw [truth]
    exact execution

/-- Original condition execution, actual descriptor construction and actual
emission of a direct wide comparison condition derive complete source branch
execution. The wide operand type excludes the narrow comparison emitters, so
no scratch separation premise is needed. -/
theorem comparison_source_branch_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cty : Clif.Ty} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {c : Nat} {test : BitVec cty.width} (getC : fr.getAs c cty = .ok test)
    (typedReads : ∀ {value : Nat} {ty : Clif.Ty} {bits : BitVec ty.width},
      fr.getAs value ty = .ok bits → ctx.valueType? value = some (.int ty.width))
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat} (origin : ctx.defClif? c = some (.icmp cc ty x y))
    (wide : Bool) (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32)))
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
    (held : ValuesHeld (Demanded middle) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ code,Frag before.base next.base code ∧
      ∀ world,LastBranchExecution F isem yes no (code.map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))))
        (test != 0) before.base next.base ρ world := by
  obtain ⟨leading,prefixFragment⟩ := original_prefix inv dfg getC typedReads enoughCondition conditionRun
  obtain ⟨producer,condition,booleanTrace,shape,flags,noDefs,notAl,notNv,companion,execution⟩ :=
    comparison_boolean_companion inv dfg getC typedReads enoughCondition conditionRun
      refines bounded extent held origin wide typeX
  exact compose_branch_values enoughConstruct enoughEmit constructRun emitRun refines bounded
    prefixFragment shape flags execution

end Backend.Stock.Proof.ConditionalValues

namespace Backend.Stock.Proof.ConditionalCalls
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open ConditionalValues
set_option autoImplicit false
set_option Elab.async false

/-- The actual selected call packet of a direct wide comparison establishes
source branch execution from values held at its output state, with no scratch
separation premise. -/
theorem Calls.comparison_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    {cty : Clif.Ty} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {test : BitVec cty.width} (getC : fr.getAs c cty = .ok test)
    (typedReads : ∀ {value : Nat} {ty : Clif.Ty} {bits : BitVec ty.width},
      fr.getAs value ty = .ok bits → ctx.valueType? value = some (.int ty.width))
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat} (origin : ctx.defClif? c = some (.icmp cc ty x y))
    (wide : Bool) (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32)))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ before.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < before.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ yes no code,labels = [yes,no] ∧ Frag before.base next.base code ∧
      ∀ world,LastBranchExecution F isem yes no (code.map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))))
        (test != 0) before.base next.base ρ world := by
  have constructMono := stock_apply_demand_mono calls.constructRun
  have emitMono := stock_apply_demand_mono calls.emitRun
  have intermediate : ValuesHeld (Demanded calls.middle) ctx fr
      (fun key => ρ (aliasNum aliases key)) := held.mono (by
    intro value needed
    have first := constructMono value
    have second := emitMono value
    unfold Demanded at needed ⊢
    omega)
  have conditionRun := calls.conditionRun
  rw [source] at conditionRun
  obtain ⟨code,fragment,execution⟩ := comparison_source_branch_values inv dfg getC typedReads
    origin wide typeX calls.conditionEnough calls.constructEnough calls.emitEnough conditionRun
    calls.constructRun calls.emitRun refines bounded extent intermediate
  exact ⟨calls.yes,calls.no,code,calls.labels_eq,fragment,execution⟩

end Backend.Stock.Proof.ConditionalCalls

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- A source definition in the original context is also the definition in the
actual terminator context: the defining slot is not the terminator slot. -/
theorem ConditionalBodySpec.defClif_here {f : Clif.Function} {result : Result}
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) {value : Nat} {inst : Clif.Inst}
    (origin : result.ctx.defClif? value = some inst) : spec.core.scan.ctx.defClif? value = some inst := by
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  obtain ⟨original,st0,oldBuild,ctxSpec,view⟩ := buildCtx_source spec.build
  have range : spec.ranges[bi]! = (blockStart f bi,blockStart f bi+b.body.length+1) := by
    simp only [getElem!_def,ctxSpec.ranges bi b block]
  have placeholder : result.ctx.insts[blockStart f bi+b.body.length]? = some ⟨.op .unit,[],[],none⟩ := by
    rw [view.insts]
    exact ctxSpec.facts.term bi b block
  have slot : result.ctx.insts[spec.ranges[bi]!.2-1]? = some ⟨.op .unit,[],[],none⟩ := by
    rw [range]
    simpa only [Nat.add_sub_cancel] using placeholder
  cases defined : result.ctx.defInst? value with
  | none => simp [Ctx.defClif?,defined] at origin
  | some j =>
    cases found : result.ctx.insts[j]? with
    | none => simp [Ctx.defClif?,defined,found] at origin
    | some info =>
      have clif : info.clif = some inst := by simpa [Ctx.defClif?,defined,found] using origin
      have different : j ≠ spec.ranges[bi]!.2-1 := by
        intro same
        rw [same,slot] at found
        cases found
        cases clif
      rw [ctxEq]
      have foundHere : (termCtx result.ctx (spec.ranges[bi]!.2-1) spec.data).insts[j]? = some info := by
        rw [termCtx_insts_ne different]
        exact found
      simp only [Ctx.defClif?,Ctx.defInst?] at defined ⊢
      change (Option.join (result.ctx.valDef[value]?)).bind
        (fun i => ((termCtx result.ctx (spec.ranges[bi]!.2-1) spec.data).insts[i]?).bind (·.clif)) = _
      rw [defined]
      simp [foundHere,clif]

/-- Original source metadata and the retained core derive the named call
packet of a branch on a direct comparison whose first operand is a source
parameter. -/
theorem ConditionalBodySpec.comparison_calls {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y))
    (parameterX : result.ctx.defInst? x = none) :
    ∃ calls : ConditionalCalls.Calls spec.core.scan.ctx (spec.ranges[bi]!.2-1)
      result.order.successors[label]!.toList
      {spec.input with current := some (spec.ranges[bi]!.2-1),color := none,base.emitted := #[]}
      spec.origin.out spec.origin.emission.state,calls.source = .value c := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have originHere := spec.defClif_here block origin
  have parameterHere : spec.core.scan.ctx.defInst? x = none := by rw [ctxEq]; exact parameterX
  have expected : Coverage.blockData f b.term =
      .ok (.data 152 5 [.data 151 1 [],.value c,.blockCalls [0,1]]) := by
    rw [termShape]
    with_unfolding_all rfl
  have dataEq := Except.ok.inj (spec.prepared.symm.trans expected)
  obtain ⟨original,st0,oldBuild,ctxSpec,view⟩ := buildCtx_source spec.build
  have range : spec.ranges[bi]! = (blockStart f bi,blockStart f bi+b.body.length+1) := by
    simp only [getElem!_def,ctxSpec.ranges bi b block]
  have placeholder : result.ctx.insts[blockStart f bi+b.body.length]? = some ⟨.op .unit,[],[],none⟩ := by
    rw [view.insts]
    exact ctxSpec.facts.term bi b block
  have bound : spec.ranges[bi]!.2-1 < result.ctx.insts.size := by
    have inside := (Array.getElem?_eq_some_iff.mp placeholder).1
    rw [range]
    dsimp only
    omega
  have slot : spec.core.scan.ctx.insts[spec.ranges[bi]!.2-1]? =
      some ⟨.data 152 5 [.data 151 1 [],.value c,.blockCalls [0,1]],[],[],none⟩ := by
    rw [ctxEq]
    change (result.ctx.insts.set! (spec.ranges[bi]!.2-1) ⟨spec.data,[],[],none⟩)[spec.ranges[bi]!.2-1]? = _
    simp only [dataEq,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt bound]
  have named : Stock.runTerm spec.core.scan.ctx "lower_branch"
      [.inst (spec.ranges[bi]!.2-1),.labels result.order.successors[label]!.toList]
      {spec.input with current := some (spec.ranges[bi]!.2-1),color := none,base.emitted := #[]} =
      .ok (some spec.origin.out,spec.origin.emission.state,spec.origin.trace) := by
    simpa only [ctxEq] using spec.origin.call
  exact ComparisonBranch.comparison_named_calls inv slot originHere parameterHere named

/-- The actual source-correct wide comparison branch on two source parameters
stops at the last instruction of its real buffer, with the guarded post-frame.
Source context, call selection, alias/demand bounds and the complete guarded
post-frame are derived internally from the real core. -/
theorem ConditionalBodySpec.comparison_branch_values_last {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y)) (wide : Bool)
    (typeX : result.ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (typeY : result.ctx.valueType? y = some (.int (if wide then 64 else 32)))
    (parameterX : result.ctx.defInst? x = none) (parameterY : result.ctx.defInst? y = none)
    {fr : Clif.Frame} {cm : Clif.Mem} {cty : Clif.Ty} {test : BitVec cty.width}
    (getC : (restrict fr (availOf f (availIn f result.ctx) spec.core.scan.block b.body.length)).getAs c cty = .ok test)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (post : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
      (b.body.length,fr,cm) ρ world) :
    ∃ index inst ops regs prefixWorld endWorld,
      seqRun isem (spec.origin.emission.code.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
        some (.stop index inst ops regs prefixWorld [] endWorld (.goto (if test != 0 then 0 else 1))) ∧
      index+1 = spec.origin.emission.code.size ∧
      GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
        (b.body.length,fr,cm) regs endWorld ∧
      inst.targets = result.order.successors[label]!.toList ∧ inst.isTerminator = true := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have originHere := spec.defClif_here block origin
  have typeXHere : spec.core.scan.ctx.valueType? x = some (.int (if wide then 64 else 32)) := by
    rw [ctxEq]; exact typeX
  have typeYHere : spec.core.scan.ctx.valueType? y = some (.int (if wide then 64 else 32)) := by
    rw [ctxEq]; exact typeY
  have parameterXHere : spec.core.scan.ctx.defInst? x = none := by rw [ctxEq]; exact parameterX
  have parameterYHere : spec.core.scan.ctx.defInst? y = none := by rw [ctxEq]; exact parameterY
  obtain ⟨calls,source⟩ := spec.comparison_calls run scope block termShape origin parameterX
  have typedReads : ∀ {value : Nat} {vty : Clif.Ty} {bits : BitVec vty.width},
      (restrict fr (availOf f (availIn f result.ctx) spec.core.scan.block b.body.length)).getAs value vty =
        .ok bits → spec.core.scan.ctx.valueType? value = some (.int vty.width) := by
    intro value vty bits read
    have available := restrict_regs_isSome (by rw [getAs_ok read]; rfl)
    exact stock_lower_available_getAs_type run spec.events available post.2.1 read
  obtain ⟨emission,afterEdges,retained,branchCall,outgoing,scanInput,scanCtx,branchScan,combined⟩ :=
    conditional_core_calls termShape spec.coreRun
  have same : emission = spec.origin.emission := Option.some.inj (retained.symm.trans spec.origin.retained)
  rw [same] at outgoing
  obtain ⟨edgeBase,edgeExtent⟩ := outgoing_base_extent outgoing
  have scanBase : spec.core.scan.input.base = spec.origin.emission.state.base := by rw [scanInput]; exact edgeBase
  have scanExtent : spec.core.scan.input.demand.size = spec.origin.emission.state.demand.size := by rw [scanInput]; exact edgeExtent
  have sizes : spec.origin.emission.state.base.nextVreg = spec.input.base.nextVreg ∧
      spec.origin.emission.state.demand.size = spec.input.demand.size :=
    calls.comparison_wide_bounds inv source originHere wide typeXHere typeYHere parameterXHere parameterYHere
  have termRecorded : spec.term ∈ spec.core.scan.output.records := by rw [spec.split.records]; simp
  have bounded : result.final.alias.size ≤ spec.input.base.nextVreg := by
    have actual := stock_lower_blockScanAliasBounds run spec.core.scan spec.events spec.term termRecorded
    have fresh : (scanState spec.term.input spec.term.inst).base.nextVreg = spec.term.input.base.nextVreg := by
      unfold scanState
      dsimp only
      split <;> rfl
    rw [fresh] at actual
    rw [spec.split.termInput,scanBase,sizes.1] at actual
    exact actual
  have extent : ∀ value r,spec.core.scan.ctx.valueReg? value = some r → value < spec.input.demand.size := by
    intro value r mapped
    have actual := (Extent.lower_mapped_demand_bounds run scope spec.events termRecorded mapped).1
    rw [spec.split.termInput,scanExtent,sizes.2] at actual
    exact actual
  have termDemand := (Control.stock_branch_scan_body_code spec.split spec.origin.branchScan).2
  have held : ValuesHeld (Demanded spec.origin.emission.state) spec.core.scan.ctx
      (restrict fr (availOf f (availIn f result.ctx) spec.core.scan.block b.body.length))
      (fun key => ρ (aliasNum result.final.alias key)) := by
    intro value needed val read
    have av := restrict_regs_isSome (by rw [read]; rfl)
    rw [restrict_regs_of_mem av] at read
    have mono := conditional_core_emission_demand termShape spec.coreRun spec.origin value
    have demanded : Demanded spec.term.output.state value := by
      unfold Demanded at needed ⊢
      rw [termDemand,spec.split.termInput]
      omega
    exact post.2.2.2 value ⟨demanded,av⟩ val read
  obtain ⟨yesLabel,noLabel,code,labels,fragment,execution⟩ := calls.comparison_source_values
    inv source post.2.1 getC typedReads originHere wide typeXHere refines bounded extent held
  obtain ⟨other,otherFragment,noDefs⟩ :=
    calls.comparison_wide_no_defs inv source originHere wide typeXHere typeYHere parameterXHere parameterYHere
  have buffersEq := congrArg Array.toList (fragment.emitted.symm.trans otherFragment.emitted)
  simp only [Array.toList_append] at buffersEq
  have codeSame : code = other := List.append_cancel_left buffersEq
  rw [← codeSame] at noDefs
  have actualCode : spec.origin.emission.code.toList = code := by
    rw [spec.origin.emitted]
    have buffers := congrArg Array.toList fragment.emitted
    simpa only [Array.toList_append,Array.toList_empty,List.toList_toArray,List.nil_append] using buffers
  obtain ⟨index,inst,ops,regs,prefixWorld,endWorld,machine,last,nf,outside,targets,terminal⟩ := execution world
  have frame : ∀ key,regs key = ρ key := by
    intro key
    apply Sequence.stop_frame isem machine key
    intro selected member defined
    obtain ⟨raw,inside,rfl⟩ := List.mem_map.mp member
    rw [Resolved.renamed_defs,noDefs raw inside,List.map_nil] at defined
    exact List.not_mem_nil defined
  have registerEq : regs = ρ := funext frame
  refine ⟨index,inst,ops,regs,prefixWorld,endWorld,?_,?_,?_,targets.trans labels.symm,terminal⟩
  · simpa only [actualCode] using machine
  · rw [List.length_map,← actualCode,Array.length_toList] at last
    exact last
  · refine ⟨post.1,post.2.1,stable _ _ _ _ nf post.2.2.1,?_⟩
    simpa only [registerEq] using post.2.2.2

/-- An original direct wide comparison on two source parameters and the
guarded post-body frame execute the actual retained branch. This is the
comparison analog of `parameter_branch_values`. -/
theorem ConditionalBodySpec.comparison_branch_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y)) (wide : Bool)
    (typeX : result.ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (typeY : result.ctx.valueType? y = some (.int (if wide then 64 else 32)))
    (parameterX : result.ctx.defInst? x = none) (parameterY : result.ctx.defInst? y = none)
    {fr : Clif.Frame} {cm : Clif.Mem} {cty : Clif.Ty} {test : BitVec cty.width}
    (getC : (restrict fr (availOf f (availIn f result.ctx) spec.core.scan.block b.body.length)).getAs c cty = .ok test)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (post : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
      (b.body.length,fr,cm) ρ world) :
    ∃ index inst ops regs prefixWorld endWorld,
      seqRun isem (spec.origin.emission.code.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
        some (.stop index inst ops regs prefixWorld [] endWorld (.goto (if test != 0 then 0 else 1))) ∧
      GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
        (b.body.length,fr,cm) regs endWorld ∧
      inst.targets = result.order.successors[label]!.toList ∧ inst.isTerminator = true := by
  obtain ⟨index,inst,ops,regs,prefixWorld,endWorld,machine,_,guarded,targets,terminal⟩ :=
    spec.comparison_branch_values_last run scope refines stable block termShape origin wide typeX typeY
      parameterX parameterY getC post
  exact ⟨index,inst,ops,regs,prefixWorld,endWorld,machine,guarded,targets,terminal⟩

/-- The real emission of a wide comparison branch on two source parameters
is exactly two instructions. -/
theorem ConditionalBodySpec.comparison_emission_size {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y)) (wide : Bool)
    (typeX : result.ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (typeY : result.ctx.valueType? y = some (.int (if wide then 64 else 32)))
    (parameterX : result.ctx.defInst? x = none) (parameterY : result.ctx.defInst? y = none) :
    spec.origin.emission.code.size = 2 := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have originHere := spec.defClif_here block origin
  have typeXHere : spec.core.scan.ctx.valueType? x = some (.int (if wide then 64 else 32)) := by
    rw [ctxEq]; exact typeX
  have typeYHere : spec.core.scan.ctx.valueType? y = some (.int (if wide then 64 else 32)) := by
    rw [ctxEq]; exact typeY
  have parameterXHere : spec.core.scan.ctx.defInst? x = none := by rw [ctxEq]; exact parameterX
  have parameterYHere : spec.core.scan.ctx.defInst? y = none := by rw [ctxEq]; exact parameterY
  obtain ⟨calls,source⟩ := spec.comparison_calls run scope block termShape origin parameterX
  rw [spec.origin.emitted]
  have actual := calls.comparison_wide_emitted_size inv source originHere wide typeXHere typeYHere
    parameterXHere parameterYHere
  simpa only [Array.size_empty,Nat.zero_add] using actual

end Backend.Stock.Proof.ConditionalValues
