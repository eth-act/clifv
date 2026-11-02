import FV.Backend.Proof.StockInheritedDivision

/-! Carry existing original entry values through the already proved scalar
records. Every outside-interval frame comes from its existing execution proof;
no extra source acceptance or emitted-code certificate is assumed. -/
namespace Backend.Stock.Proof.Inherited
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

private theorem select_operands {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi + j)
    {info : IInfo} {ty : Clif.Ty} {c x y : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.select ty c x y))
    {env : Clif.Env} {cp : Clif.Program} {fr fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (step : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (cty : Clif.Ty) (test : BitVec cty.width) (u v : BitVec ty.width),
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs c cty = .ok test ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v := by
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := step
  cases Option.some.inj (found.symm.trans source)
  cases Option.some.inj (original.symm.trans clif)
  simp only [instOutcome, Clif.evalInst, Backend.Proof.Driver.res_bind_eq_ok, Clif.Res.pure_eq] at evaluated
  obtain ⟨cv, getC, u, getX, v, getY, _⟩ := evaluated
  have getC' : fr.getAs c cv.ty = .ok cv.bits := by
    simp [Clif.Frame.getAs, getC, Clif.Val.as?]
  have available := stock_lower_record_args_available run scope dominated events block statement current source clif
  refine ⟨cv.ty, cv.bits, u, v, ?_, ?_, ?_⟩
  · exact (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := c) (ty := cv.ty) (restrict_regs_of_mem (available c (by simp [Driver.instArgs])))).trans getC'
  · exact (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem (available x (by simp [Driver.instArgs])))).trans getX
  · exact (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := y) (ty := ty) (restrict_regs_of_mem (available y (by simp [Driver.instArgs])))).trans getY


private theorem scan_frontier (st : State) (i : Nat) :
    (scanState st i).base.nextVreg = st.base.nextVreg := by
  unfold scanState
  dsimp only
  split <;> rfl

open Backend.Stock.Proof Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 in
private theorem frame_0 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {z a x y n : Nat} {ty : Clif.Ty} (subtract : Bool) (width : ty.width ≤ 64)
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {next : State} {out : V} {evalTrace : Array RuleId} {trace : List RuleId}
    (evalRun : (evalExpr program (Stock.sem event.ctx) {} (n + 40)
      (if subtract then rule_lower_801 else rule_lower_86).rhs
      (env3 (.ty (.int ty.width)) (.value x) (.value y))).run
        (scanState record.input record.inst, #[]) = .ok (some out, next, evalTrace))
    (rootRun : Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
      .ok (some out, next, trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (operands : ValuesHeld (fun v => v = x ∨ v = y) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width} (sourceX : fr.getAs x ty = .ok u) (sourceY : fr.getAs y ty = .ok v) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty, Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩ (ρ' record.input.base.nextVreg) ∧
      (∀ key, key ≠ record.input.base.nextVreg → ρ' key = ρ key) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          (withValue fr z ⟨ty, Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩)
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  obtain ⟨nx, ny, mx, my, outputs, code, upper, demands⟩ :=
    stock_lower_alu_record_shape run scope events records subtract width source results mapped recorded emitted evalRun rootRun
  have bound : result.final.alias.size ≤ record.input.base.nextVreg := by
    simpa only [scan_frontier] using stock_lower_blockScanAliasBounds run event events record records
  have operation : ((if subtract then ALUOp.sub else .add), (if subtract then Clif.BinaryOp.isub else .iadd)) =
      (.add, .iadd) ∨ ((if subtract then ALUOp.sub else .add), (if subtract then Clif.BinaryOp.isub else .iadd)) =
      (.sub, .isub) ∨ ((if subtract then ALUOp.sub else .add), (if subtract then Clif.BinaryOp.isub else .iadd)) =
      (.and, .band) ∨ ((if subtract then ALUOp.sub else .add), (if subtract then Clif.BinaryOp.isub else .iadd)) =
      (.orr, .bor) ∨ ((if subtract then ALUOp.sub else .add), (if subtract then Clif.BinaryOp.isub else .iadd)) =
      (.eor, .bxor) := by cases subtract <;> simp
  obtain ⟨ρ', executed, value, kept⟩ := stock_alu_rrr_resolved refines operation width bound mx my operands sourceX sourceY
  have actualCode : record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1))) =
      [(MInst.aluRRR (if subtract then .sub else .add) (szOf ty.width)
        (.vreg record.input.base.nextVreg .int) (.vreg nx .int) (.vreg ny .int)).mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1))] := by rw [code]; rfl
  have actualExecution : PRun F isem (record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' := by
    rw [actualCode]; exact executed
  have terminal : aliasNum result.final.alias record.input.base.nextVreg = record.input.base.nextVreg := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bound]
    rfl
  have defs : ∀ m ∈ record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1))), ∀ key ∈ vdefs m,
        record.input.base.nextVreg ≤ key ∧ key < record.output.state.base.nextVreg := by
    rw [actualCode]
    intro m member key defined
    have equal := List.mem_singleton.mp member
    subst m
    simp only [MInst.mapRegs, resolve_vreg] at defined
    change key ∈ [aliasNum result.final.alias record.input.base.nextVreg] at defined
    rw [terminal] at defined
    have equal := List.mem_singleton.mp defined
    subst key
    rw [upper]
    omega
  obtain ⟨w', execution, _⟩ := actualExecution Arm.ArmState.default
  have transferred := stock_lower_fresh_record_values_auto_demand run scope dominated events records
    block statement current source clif results statementResults mapped recorded emitted outputs
    (Nat.le_refl _) held defs execution value
  exact ⟨ρ', actualExecution, value, kept, transferred,fun key outside => kept key (by omega)⟩

open Backend.Stock.Proof.ScalarAddSub Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 in
private theorem frame_1 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (form : Form) (subtract left : Bool) (side : subtract = true → left = false) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (form.rule subtract left).id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width}
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩ (ρ' record.input.base.nextVreg) ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          (withValue fr z ⟨ty,Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩)
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  have restrictedHeld : ValuesHeld (Demanded record.output.state) event.ctx
      (restrict fr (availOf f (availIn f result.ctx) bi j)) (fun k => ρ (aliasNum result.final.alias k)) := by
    intro x needed val lookup
    have available := restrict_regs_isSome (by rw [lookup]; rfl)
    rw [restrict_regs_of_mem available] at lookup
    exact held x ⟨needed,available⟩ val lookup
  obtain ⟨mi,ρ',outputs,code,upper,execution,value,kept⟩ := stock_lower_addsub_fused_record_values
    run scope events records form subtract left side source clif results mapped recorded emitted selectedId
    refines dfg restrictedHeld getX getY
  have resolved := (stock_lower_record_fresh_result run scope dominated.ssa events records
    source clif results mapped recorded emitted outputs (Nat.le_refl _)).2
  have maps := (stock_lower_record_context run scope events).2.1
  refine ⟨ρ',execution,value,kept,?_,fun key outside => kept key (by omega)⟩
  intro y required val lookup
  by_cases equal : y = z
  · subst y
    simp only [withValue,eq_self,ite_true] at lookup
    cases lookup
    exact ⟨a,mapped,by change VHolds _ (ρ' (aliasNum result.final.alias a)); rw [resolved]; exact value⟩
  · simp only [withValue,ite_eq_right equal] at lookup
    have before := available_before_of_after_not_result block statement required.2
      (by simpa only [statementResults,List.mem_singleton] using equal)
    have demand : Demanded record.output.state y := by
      intro zero
      have count := stock_lower_record_demand_mono run events records recorded emitted y
      change record.output.state.demand[y]! = 0 at zero
      rw [zero] at count
      exact required.1 (Nat.eq_zero_of_le_zero count)
    obtain ⟨key,map,old⟩ := held y ⟨demand,before⟩ val lookup
    have outside := stock_lower_available_alias_outside_record run scope dominated events records
      block statement current before (by rw [← maps]; exact map)
    have different : aliasNum result.final.alias key ≠ record.input.base.nextVreg := by
      rw [upper] at outside
      omega
    exact ⟨key,map,by change VHolds val (ρ' (aliasNum result.final.alias key)); rw [kept _ different]; exact old⟩

open Backend.Stock.Proof.ScalarMul.Fused Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 in
private theorem frame_2 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (fusion : Fusion) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary fusion.cop ty (if fusion.left then y else x) (if fusion.left then x else y)))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some fusion.rule.id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width}
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary fusion.cop (if fusion.left then v else u) (if fusion.left then u else v)⟩ (ρ' record.input.base.nextVreg) ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          (withValue fr z ⟨ty,Clif.Sem.binary fusion.cop (if fusion.left then v else u) (if fusion.left then u else v)⟩)
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  have restrictedHeld : ValuesHeld (Demanded record.output.state) event.ctx
      (restrict fr (availOf f (availIn f result.ctx) bi j)) (fun k => ρ (aliasNum result.final.alias k)) := by
    intro x needed val lookup
    have available := restrict_regs_isSome (by rw [lookup]; rfl)
    rw [restrict_regs_of_mem available] at lookup
    exact held x ⟨needed,available⟩ val lookup
  obtain ⟨mi,ρ',outputs,code,upper,execution,value,kept⟩ := stock_lower_mul_fused_record_values
    run scope events records fusion source clif results mapped recorded emitted selectedId
    refines dfg restrictedHeld getX getY
  have resolved := (stock_lower_record_fresh_result run scope dominated.ssa events records
    source clif results mapped recorded emitted outputs (Nat.le_refl _)).2
  have maps := (stock_lower_record_context run scope events).2.1
  refine ⟨ρ',execution,value,kept,?_,fun key outside => kept key (by omega)⟩
  intro y required val lookup
  by_cases equal : y = z
  · subst y
    simp only [withValue,eq_self,ite_true] at lookup
    cases lookup
    exact ⟨a,mapped,by change VHolds _ (ρ' (aliasNum result.final.alias a)); rw [resolved]; exact value⟩
  · simp only [withValue,ite_eq_right equal] at lookup
    have before := available_before_of_after_not_result block statement required.2
      (by simpa only [statementResults,List.mem_singleton] using equal)
    have demand : Demanded record.output.state y := by
      intro zero
      have count := stock_lower_record_demand_mono run events records recorded emitted y
      change record.output.state.demand[y]! = 0 at zero
      rw [zero] at count
      exact required.1 (Nat.eq_zero_of_le_zero count)
    obtain ⟨key,map,old⟩ := held y ⟨demand,before⟩ val lookup
    have outside := stock_lower_available_alias_outside_record run scope dominated events records
      block statement current before (by rw [← maps]; exact map)
    have different : aliasNum result.final.alias key ≠ record.input.base.nextVreg := by
      rw [upper] at outside
      omega
    exact ⟨key,map,by change VHolds val (ρ' (aliasNum result.final.alias key)); rw [kept _ different]; exact old⟩

open Backend.Stock.Proof.LogicalSelected Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 in
private theorem frame_3 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (kind : Kind) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some kind.rule.id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width}
    (sourceX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (sourceY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary kind.cop u v⟩ (ρ' record.input.base.nextVreg) ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          (withValue fr z ⟨ty,Clif.Sem.binary kind.cop u v⟩)
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  have restrictedHeld : ValuesHeld (Demanded record.output.state) event.ctx
      (restrict fr (availOf f (availIn f result.ctx) bi j)) (fun k => ρ (aliasNum result.final.alias k)) := by
    intro x needed val lookup
    have available := restrict_regs_isSome (by rw [lookup]; rfl)
    rw [restrict_regs_of_mem available] at lookup
    exact held x ⟨needed,available⟩ val lookup
  obtain ⟨mi,ρ',outputs,code,upper,execution,value,kept⟩ := stock_lower_logical_record_values
    run scope events records kind source clif results mapped recorded emitted selectedId
    refines dfg restrictedHeld sourceX sourceY
  have resolved := (stock_lower_record_fresh_result run scope dominated.ssa events records
    source clif results mapped recorded emitted outputs (Nat.le_refl _)).2
  have maps := (stock_lower_record_context run scope events).2.1
  refine ⟨ρ',execution,value,kept,?_,fun key outside => kept key (by omega)⟩
  intro y required val lookup
  by_cases equal : y = z
  · subst y
    simp only [withValue,eq_self,ite_true] at lookup
    cases lookup
    exact ⟨a,mapped,by change VHolds _ (ρ' (aliasNum result.final.alias a)); rw [resolved]; exact value⟩
  · simp only [withValue,ite_eq_right equal] at lookup
    have before := available_before_of_after_not_result block statement required.2
      (by simpa only [statementResults,List.mem_singleton] using equal)
    have demand : Demanded record.output.state y := by
      intro zero
      have count := stock_lower_record_demand_mono run events records recorded emitted y
      change record.output.state.demand[y]! = 0 at zero
      rw [zero] at count
      exact required.1 (Nat.eq_zero_of_le_zero count)
    obtain ⟨key,map,old⟩ := held y ⟨demand,before⟩ val lookup
    have outside := stock_lower_available_alias_outside_record run scope dominated events records
      block statement current before (by rw [← maps]; exact map)
    have different : aliasNum result.final.alias key ≠ record.input.base.nextVreg := by
      rw [upper] at outside
      omega
    exact ⟨key,map,by change VHolds val (ρ' (aliasNum result.final.alias key)); rw [kept _ different]; exact old⟩

open Backend.Stock.Proof.LogicalNot Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 Backend.Stock.Proof.LogicalSelected in
private theorem frame_4 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (kind : Kind) (left : Bool) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty (if left then y else x) (if left then x else y)))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (notRule kind left).id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width}
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary kind.cop (if left then v else u) (if left then u else v)⟩ (ρ' record.input.base.nextVreg) ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          (withValue fr z ⟨ty,Clif.Sem.binary kind.cop (if left then v else u) (if left then u else v)⟩)
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  have restrictedHeld : ValuesHeld (Demanded record.output.state) event.ctx
      (restrict fr (availOf f (availIn f result.ctx) bi j)) (fun k => ρ (aliasNum result.final.alias k)) := by
    intro x needed val lookup
    have available := restrict_regs_isSome (by rw [lookup]; rfl)
    rw [restrict_regs_of_mem available] at lookup
    exact held x ⟨needed,available⟩ val lookup
  obtain ⟨mi,ρ',outputs,code,upper,execution,value,kept⟩ := stock_lower_logical_not_record_values
    run scope events records kind left source clif results mapped recorded emitted selectedId
    refines dfg restrictedHeld getX getY
  have resolved := (stock_lower_record_fresh_result run scope dominated.ssa events records
    source clif results mapped recorded emitted outputs (Nat.le_refl _)).2
  have maps := (stock_lower_record_context run scope events).2.1
  refine ⟨ρ',execution,value,kept,?_,fun key outside => kept key (by omega)⟩
  intro y required val lookup
  by_cases equal : y = z
  · subst y
    simp only [withValue,eq_self,ite_true] at lookup
    cases lookup
    exact ⟨a,mapped,by change VHolds _ (ρ' (aliasNum result.final.alias a)); rw [resolved]; exact value⟩
  · simp only [withValue,ite_eq_right equal] at lookup
    have before := available_before_of_after_not_result block statement required.2
      (by simpa only [statementResults,List.mem_singleton] using equal)
    have demand : Demanded record.output.state y := by
      intro zero
      have count := stock_lower_record_demand_mono run events records recorded emitted y
      change record.output.state.demand[y]! = 0 at zero
      rw [zero] at count
      exact required.1 (Nat.eq_zero_of_le_zero count)
    obtain ⟨key,map,old⟩ := held y ⟨demand,before⟩ val lookup
    have outside := stock_lower_available_alias_outside_record run scope dominated events records
      block statement current before (by rw [← maps]; exact map)
    have different : aliasNum result.final.alias key ≠ record.input.base.nextVreg := by
      rw [upper] at outside
      omega
    exact ⟨key,map,by change VHolds val (ρ' (aliasNum result.final.alias key)); rw [kept _ different]; exact old⟩

open Backend.Stock.Proof.LogicalExtr Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 in
private theorem frame_5 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f) (mirrored : Bool)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary .bor ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (extrRule mirrored).id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width}
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary .bor u v⟩ (ρ' record.input.base.nextVreg) ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          (withValue fr z ⟨ty,Clif.Sem.binary .bor u v⟩)
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  have restrictedHeld : ValuesHeld (Demanded record.output.state) event.ctx
      (restrict fr (availOf f (availIn f result.ctx) bi j)) (fun k => ρ (aliasNum result.final.alias k)) := by
    intro x needed val lookup
    have available := restrict_regs_isSome (by rw [lookup]; rfl)
    rw [restrict_regs_of_mem available] at lookup
    exact held x ⟨needed,available⟩ val lookup
  obtain ⟨mi,ρ',outputs,code,upper,execution,value,kept⟩ := record_values
    run scope mirrored events records source clif results mapped recorded emitted selectedId
    refines dfg restrictedHeld getX getY
  have resolved := (stock_lower_record_fresh_result run scope dominated.ssa events records
    source clif results mapped recorded emitted outputs (Nat.le_refl _)).2
  have maps := (stock_lower_record_context run scope events).2.1
  refine ⟨ρ',execution,value,kept,?_,fun key outside => kept key (by omega)⟩
  intro y required val lookup
  by_cases equal : y = z
  · subst y
    simp only [withValue,eq_self,ite_true] at lookup
    cases lookup
    exact ⟨a,mapped,by change VHolds _ (ρ' (aliasNum result.final.alias a)); rw [resolved]; exact value⟩
  · simp only [withValue,ite_eq_right equal] at lookup
    have before := available_before_of_after_not_result block statement required.2
      (by simpa only [statementResults,List.mem_singleton] using equal)
    have demand : Demanded record.output.state y := by
      intro zero
      have count := stock_lower_record_demand_mono run events records recorded emitted y
      change record.output.state.demand[y]! = 0 at zero
      rw [zero] at count
      exact required.1 (Nat.eq_zero_of_le_zero count)
    obtain ⟨key,map,old⟩ := held y ⟨demand,before⟩ val lookup
    have outside := stock_lower_available_alias_outside_record run scope dominated events records
      block statement current before (by rw [← maps]; exact map)
    have different : aliasNum result.final.alias key ≠ record.input.base.nextVreg := by
      rw [upper] at outside
      omega
    exact ⟨key,map,by change VHolds val (ρ' (aliasNum result.final.alias key)); rw [kept _ different]; exact old⟩

open Backend.Stock.Proof.LogicalNot Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 in
private theorem frame_6 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.unary .bnot ty y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some rule_lower_1406.id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u : BitVec ty.width}
    (get : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok u) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bnot u⟩ (ρ' record.input.base.nextVreg) ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          (withValue fr z ⟨ty,Clif.Sem.unary .bnot u⟩)
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  have restrictedHeld : ValuesHeld (Demanded record.output.state) event.ctx
      (restrict fr (availOf f (availIn f result.ctx) bi j)) (fun k => ρ (aliasNum result.final.alias k)) := by
    intro x needed val lookup
    have available := restrict_regs_isSome (by rw [lookup]; rfl)
    rw [restrict_regs_of_mem available] at lookup
    exact held x ⟨needed,available⟩ val lookup
  obtain ⟨mi,ρ',outputs,code,upper,execution,value,kept⟩ := stock_lower_not_xor_record_values
    run scope events records source clif results mapped recorded emitted selectedId
    refines dfg restrictedHeld get
  have resolved := (stock_lower_record_fresh_result run scope dominated.ssa events records
    source clif results mapped recorded emitted outputs (Nat.le_refl _)).2
  have maps := (stock_lower_record_context run scope events).2.1
  refine ⟨ρ',execution,value,kept,?_,fun key outside => kept key (by omega)⟩
  intro y required val lookup
  by_cases equal : y = z
  · subst y
    simp only [withValue,eq_self,ite_true] at lookup
    cases lookup
    exact ⟨a,mapped,by change VHolds _ (ρ' (aliasNum result.final.alias a)); rw [resolved]; exact value⟩
  · simp only [withValue,ite_eq_right equal] at lookup
    have before := available_before_of_after_not_result block statement required.2
      (by simpa only [statementResults,List.mem_singleton] using equal)
    have demand : Demanded record.output.state y := by
      intro zero
      have count := stock_lower_record_demand_mono run events records recorded emitted y
      change record.output.state.demand[y]! = 0 at zero
      rw [zero] at count
      exact required.1 (Nat.eq_zero_of_le_zero count)
    obtain ⟨key,map,old⟩ := held y ⟨demand,before⟩ val lookup
    have outside := stock_lower_available_alias_outside_record run scope dominated events records
      block statement current before (by rw [← maps]; exact map)
    have different : aliasNum result.final.alias key ≠ record.input.base.nextVreg := by
      rw [upper] at outside
      omega
    exact ⟨key,map,by change VHolds val (ρ' (aliasNum result.final.alias key)); rw [kept _ different]; exact old⟩

open Backend.Stock.Proof.Bnot Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 in
private theorem frame_7 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (shifted : Bool) {info : IInfo} {y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.unary .bnot ty y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (rule shifted).id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u : BitVec ty.width}
    (get : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok u) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bnot u⟩ (ρ' record.input.base.nextVreg) ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          (withValue fr z ⟨ty,Clif.Sem.unary .bnot u⟩)
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  have restrictedHeld : ValuesHeld (Demanded record.output.state) event.ctx
      (restrict fr (availOf f (availIn f result.ctx) bi j)) (fun k => ρ (aliasNum result.final.alias k)) := by
    intro x needed val lookup
    have available := restrict_regs_isSome (by rw [lookup]; rfl)
    rw [restrict_regs_of_mem available] at lookup
    exact held x ⟨needed,available⟩ val lookup
  obtain ⟨mi,ρ',outputs,code,upper,execution,value,kept⟩ := stock_lower_bnot_record_values
    run scope events records shifted source clif results mapped recorded emitted selectedId
    refines dfg restrictedHeld get
  have resolved := (stock_lower_record_fresh_result run scope dominated.ssa events records
    source clif results mapped recorded emitted outputs (Nat.le_refl _)).2
  have maps := (stock_lower_record_context run scope events).2.1
  refine ⟨ρ',execution,value,kept,?_,fun key outside => kept key (by omega)⟩
  intro y required val lookup
  by_cases equal : y = z
  · subst y
    simp only [withValue,eq_self,ite_true] at lookup
    cases lookup
    exact ⟨a,mapped,by change VHolds _ (ρ' (aliasNum result.final.alias a)); rw [resolved]; exact value⟩
  · simp only [withValue,ite_eq_right equal] at lookup
    have before := available_before_of_after_not_result block statement required.2
      (by simpa only [statementResults,List.mem_singleton] using equal)
    have demand : Demanded record.output.state y := by
      intro zero
      have count := stock_lower_record_demand_mono run events records recorded emitted y
      change record.output.state.demand[y]! = 0 at zero
      rw [zero] at count
      exact required.1 (Nat.eq_zero_of_le_zero count)
    obtain ⟨key,map,old⟩ := held y ⟨demand,before⟩ val lookup
    have outside := stock_lower_available_alias_outside_record run scope dominated events records
      block statement current before (by rw [← maps]; exact map)
    have different : aliasNum result.final.alias key ≠ record.input.base.nextVreg := by
      rw [upper] at outside
      omega
    exact ⟨key,map,by change VHolds val (ρ' (aliasNum result.final.alias key)); rw [kept _ different]; exact old⟩

open Backend.Stock.Proof Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix Isle Isle.Interp Isle.Aarch64 in
private theorem frame_8 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {z a x y n : Nat} {ty : Clif.Ty} (subtract : Bool) (width : ty.width ≤ 64)
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {next : State} {out : V} {evalTrace : Array RuleId} {trace : List RuleId}
    (evalRun : (evalExpr program (Stock.sem event.ctx) {} (n + 40)
      (if subtract then rule_lower_801 else rule_lower_86).rhs
      (env3 (.ty (.int ty.width)) (.value x) (.value y))).run
        (scanState record.input record.inst, #[]) = .ok (some out, next, evalTrace))
    (rootRun : Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
      .ok (some out, next, trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width} (sourceX : fr.getAs x ty = .ok u) (sourceY : fr.getAs y ty = .ok v) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty, Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩ (ρ' record.input.base.nextVreg) ∧
      (∀ key, key ≠ record.input.base.nextVreg → ρ' key = ρ key) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          (withValue fr z ⟨ty, Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩)
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  have coverage := stock_lower_alu_operand_coverage run scope dominated events records
    block statement current subtract width source clif results mapped recorded emitted evalRun rootRun
  have operands := held.mono coverage
  exact frame_0 run scope dominated events records block statement current
    subtract width source clif results statementResults mapped recorded emitted evalRun rootRun
    refines operands held sourceX sourceY

open Backend.Stock.Proof Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 in
private theorem frame_9 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {z a x y : Nat} {ty : Clif.Ty} (subtract : Bool)
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (if subtract then rule_lower_801 else rule_lower_86).id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width} (sourceX : fr.getAs x ty = .ok u) (sourceY : fr.getAs y ty = .ok v) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty, Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩ (ρ' record.input.base.nextVreg) ∧
      (∀ key, key ≠ record.input.base.nextVreg → ρ' key = ρ key) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          (withValue fr z ⟨ty, Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩)
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  obtain ⟨width, out, next, trace, rhsTrace, rootRun, evalRun⟩ := stock_lower_alu_selected_receipts
    run scope events records subtract source clif recorded emitted selectedId
  exact frame_8 run scope dominated events records block statement current
    subtract width source clif results statementResults mapped recorded emitted (n := 999959) evalRun rootRun
    refines held sourceX sourceY

open Backend.Stock.Proof.ScalarAddSub Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 in
private theorem frame_10 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (subtract : Bool) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width}
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩ (ρ' record.input.base.nextVreg) ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          (withValue fr z ⟨ty,Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩)
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have inv := (stock_lower_record_context run scope events).1
  have member := stock_addsub_selected_rule_ids inv subtract source clif receipt.selected
  have availableX := restrict_regs_isSome (by rw [getAs_ok getX]; rfl)
  have availableY := restrict_regs_isSome (by rw [getAs_ok getY]; rfl)
  have originalX : fr.getAs x ty = .ok u :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem availableX)).symm.trans getX
  have originalY : fr.getAs y ty = .ok v :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := y) (ty := ty) (restrict_regs_of_mem availableY)).symm.trans getY
  cases subtract
  · simp only [Bool.false_eq_true,ite_false,ite_true,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with id595 | id597 | id596 | id598 | id590 | id589 | id592 | id591 | id594 | id593 | id588
    · have last : step.rules.getLast? = some 595 := by
        rw [receipt.rules,receipt.selected.last_rule,id595]
      exact frame_1 run scope dominated events records block statement current
        .shifted false false (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 597 := by
        rw [receipt.rules,receipt.selected.last_rule,id597]
      exact frame_2 run scope dominated events records
        block statement current .addRight source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 596 := by
        rw [receipt.rules,receipt.selected.last_rule,id596]
      exact frame_1 run scope dominated events records block statement current
        .shifted false true (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 598 := by
        rw [receipt.rules,receipt.selected.last_rule,id598]
      exact frame_2 run scope dominated events records
        block statement current .addLeft (x := y) (y := x) source clif results statementResults mapped recorded emitted last refines dfg held getY getX
    · have last : step.rules.getLast? = some 590 := by
        rw [receipt.rules,receipt.selected.last_rule,id590]
      exact frame_1 run scope dominated events records block statement current
        .immediate false true (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 589 := by
        rw [receipt.rules,receipt.selected.last_rule,id589]
      exact frame_1 run scope dominated events records block statement current
        .immediate false false (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 592 := by
        rw [receipt.rules,receipt.selected.last_rule,id592]
      exact frame_1 run scope dominated events records block statement current
        .negative false true (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 591 := by
        rw [receipt.rules,receipt.selected.last_rule,id591]
      exact frame_1 run scope dominated events records block statement current
        .negative false false (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 594 := by
        rw [receipt.rules,receipt.selected.last_rule,id594]
      exact frame_1 run scope dominated events records block statement current
        .extended false true (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 593 := by
        rw [receipt.rules,receipt.selected.last_rule,id593]
      exact frame_1 run scope dominated events records block statement current
        .extended false false (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 588 := by
        rw [receipt.rules,receipt.selected.last_rule,id588]
      exact frame_9 run scope dominated events records block statement current false
        source clif results statementResults mapped recorded emitted last refines held originalX originalY
  · simp only [Bool.false_eq_true,ite_false,ite_true,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with id747 | id748 | id599 | id746 | id749 | id745
    · have last : step.rules.getLast? = some 747 := by
        rw [receipt.rules,receipt.selected.last_rule,id747]
      exact frame_1 run scope dominated events records block statement current
        .negative true false (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 748 := by
        rw [receipt.rules,receipt.selected.last_rule,id748]
      exact frame_1 run scope dominated events records block statement current
        .extended true false (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 599 := by
        rw [receipt.rules,receipt.selected.last_rule,id599]
      exact frame_2 run scope dominated events records
        block statement current .subRight source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 746 := by
        rw [receipt.rules,receipt.selected.last_rule,id746]
      exact frame_1 run scope dominated events records block statement current
        .immediate true false (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 749 := by
        rw [receipt.rules,receipt.selected.last_rule,id749]
      exact frame_1 run scope dominated events records block statement current
        .shifted true false (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 745 := by
        rw [receipt.rules,receipt.selected.last_rule,id745]
      exact frame_9 run scope dominated events records block statement current true
        source clif results statementResults mapped recorded emitted last refines held originalX originalY

open Backend.Stock.Proof.ScalarAddSub Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 in
private theorem frame_11 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (subtract : Bool) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width}
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v)
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩ (ρ' record.input.base.nextVreg) ∧
      cm' = cm ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          fr'
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceProof
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have availableX := restrict_regs_isSome (by rw [getAs_ok getX]; rfl)
  have availableY := restrict_regs_isSome (by rw [getAs_ok getY]; rfl)
  have originalX : fr.getAs x ty = .ok u :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem availableX)).symm.trans getX
  have originalY : fr.getAs y ty = .ok v :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := y) (ty := ty) (restrict_regs_of_mem availableY)).symm.trans getY
  have computed : instOutcome env cp fr cm (.binary (if subtract then .isub else .iadd) ty x y) =
      .ok ([⟨ty,Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩],cm) := by
    cases subtract <;> simp [instOutcome,Clif.evalInst,Clif.BinaryOp.isShift,originalX,originalY]
  have equal := Prod.mk.inj (Clif.Res.ok.inj (evaluated.symm.trans computed))
  have memEq : cm' = cm := equal.2
  have evaluatedValue : instOutcome env cp fr cm (.binary (if subtract then .isub else .iadd) ty x y) =
      .ok ([⟨ty,Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩],cm') := by rw [memEq]; exact computed
  obtain ⟨ρ',execution,value,kept,installed,interval⟩ := frame_10
    run scope dominated events records block statement current subtract source clif results statementResults
    mapped recorded emitted refines dfg held getX getY
  have post := source_single_result_values source clif results sourceStep evaluatedValue installed
  exact ⟨ρ',execution,value,memEq,kept,post,interval⟩

open Backend.Stock.Proof.ScalarAddSub Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 in
private theorem frame_12 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (subtract : Bool) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (u v : BitVec ty.width) (ρ' : Nat → CV),
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v ∧ PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩ (ρ' record.input.base.nextVreg) ∧
      cm' = cm ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          fr'
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  obtain ⟨u,v,getX,getY⟩ := stock_lower_addsub_source_operands run scope dominated events block statement current subtract source clif sourceStep
  obtain ⟨ρ',execution,value,memEq,kept,post,interval⟩ := frame_11
    run scope dominated events records block statement current subtract source clif results statementResults
    mapped recorded emitted refines dfg held getX getY sourceStep
  exact ⟨u,v,ρ',getX,getY,execution,value,memEq,kept,post,interval⟩

open Backend.Stock.Proof.LogicalComplete Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 LogicalSelected in
private theorem frame_13 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (kind : Kind) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some kind.rule.id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width}
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v)
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary kind.cop u v⟩ (ρ' record.input.base.nextVreg) ∧
      cm' = cm ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          fr'
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceProof
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have availableX := restrict_regs_isSome (by rw [getAs_ok getX]; rfl)
  have availableY := restrict_regs_isSome (by rw [getAs_ok getY]; rfl)
  have originalX : fr.getAs x ty = .ok u :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem availableX)).symm.trans getX
  have originalY : fr.getAs y ty = .ok v :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := y) (ty := ty) (restrict_regs_of_mem availableY)).symm.trans getY
  have computed : instOutcome env cp fr cm (.binary kind.cop ty x y) =
      .ok ([⟨ty,Clif.Sem.binary kind.cop u v⟩],cm) := by
    cases kind <;> simp [Kind.cop,instOutcome,Clif.evalInst,Clif.BinaryOp.isShift,originalX,originalY]
  have equal := Prod.mk.inj (Clif.Res.ok.inj (evaluated.symm.trans computed))
  have memEq : cm' = cm := equal.2
  have evaluatedValue : instOutcome env cp fr cm (.binary kind.cop ty x y) =
      .ok ([⟨ty,Clif.Sem.binary kind.cop u v⟩],cm') := by rw [memEq]; exact computed
  obtain ⟨ρ',execution,value,kept,installed,interval⟩ := frame_3
    run scope dominated events records block statement current kind source clif results statementResults
    mapped recorded emitted selectedId refines dfg held getX getY
  have post := source_single_result_values source clif results sourceStep evaluatedValue installed
  exact ⟨ρ',execution,value,memEq,kept,post,interval⟩

open Backend.Stock.Proof.LogicalComplete Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 LogicalSelected in
private theorem frame_14 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (kind : Kind) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some kind.rule.id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (u v : BitVec ty.width) (ρ' : Nat → CV),
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v ∧ PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary kind.cop u v⟩ (ρ' record.input.base.nextVreg) ∧
      cm' = cm ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          fr'
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  obtain ⟨u,v,getX,getY⟩ := source_operands run scope dominated events block statement current kind source clif sourceStep
  obtain ⟨ρ',execution,value,memEq,kept,post,interval⟩ := frame_13
    run scope dominated events records block statement current kind source clif results statementResults
    mapped recorded emitted selectedId refines dfg held getX getY sourceStep
  exact ⟨u,v,ρ',getX,getY,execution,value,memEq,kept,post,interval⟩

open Backend.Stock.Proof.LogicalSelected in
private theorem not_values_same_order {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (kind : Kind) (left : Bool) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (LogicalNot.notRule kind left).id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width}
    (sourceX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (sourceY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary kind.cop u v⟩ (ρ' record.input.base.nextVreg) ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          (withValue fr z ⟨ty,Clif.Sem.binary kind.cop u v⟩)
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  cases left with
  | false =>
    exact frame_4
      run scope dominated events records block statement current kind false source clif results statementResults
      mapped recorded emitted selectedId refines dfg held sourceX sourceY
  | true =>
    exact frame_4 (x := y) (y := x)
      run scope dominated events records block statement current kind true source clif results statementResults
      mapped recorded emitted selectedId refines dfg held sourceY sourceX

open Backend.Stock.Proof.LogicalComplete Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 LogicalSelected in
private theorem frame_15 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (kind : Kind) (left : Bool) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (LogicalNot.notRule kind left).id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width}
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v)
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary kind.cop u v⟩ (ρ' record.input.base.nextVreg) ∧
      cm' = cm ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          fr'
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceProof
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have availableX := restrict_regs_isSome (by rw [getAs_ok getX]; rfl)
  have availableY := restrict_regs_isSome (by rw [getAs_ok getY]; rfl)
  have originalX : fr.getAs x ty = .ok u :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem availableX)).symm.trans getX
  have originalY : fr.getAs y ty = .ok v :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := y) (ty := ty) (restrict_regs_of_mem availableY)).symm.trans getY
  have computed : instOutcome env cp fr cm (.binary kind.cop ty x y) =
      .ok ([⟨ty,Clif.Sem.binary kind.cop u v⟩],cm) := by
    cases kind <;> simp [Kind.cop,instOutcome,Clif.evalInst,Clif.BinaryOp.isShift,originalX,originalY]
  have equal := Prod.mk.inj (Clif.Res.ok.inj (evaluated.symm.trans computed))
  have memEq : cm' = cm := equal.2
  have evaluatedValue : instOutcome env cp fr cm (.binary kind.cop ty x y) =
      .ok ([⟨ty,Clif.Sem.binary kind.cop u v⟩],cm') := by rw [memEq]; exact computed
  obtain ⟨ρ',execution,value,kept,installed,interval⟩ := not_values_same_order
    run scope dominated events records block statement current kind left source clif results statementResults
    mapped recorded emitted selectedId refines dfg held getX getY
  have post := source_single_result_values source clif results sourceStep evaluatedValue installed
  exact ⟨ρ',execution,value,memEq,kept,post,interval⟩

open Backend.Stock.Proof.LogicalComplete Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 LogicalSelected in
private theorem frame_16 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (kind : Kind) (left : Bool) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (LogicalNot.notRule kind left).id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (u v : BitVec ty.width) (ρ' : Nat → CV),
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v ∧ PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary kind.cop u v⟩ (ρ' record.input.base.nextVreg) ∧
      cm' = cm ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          fr'
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  obtain ⟨u,v,getX,getY⟩ := source_operands run scope dominated events block statement current kind source clif sourceStep
  obtain ⟨ρ',execution,value,memEq,kept,post,interval⟩ := frame_15
    run scope dominated events records block statement current kind left source clif results statementResults
    mapped recorded emitted selectedId refines dfg held getX getY sourceStep
  exact ⟨u,v,ρ',getX,getY,execution,value,memEq,kept,post,interval⟩

open Backend.Stock.Proof.LogicalExtr Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 in
private theorem frame_17 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f) (mirrored : Bool)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary .bor ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (extrRule mirrored).id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width}
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v)
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary .bor u v⟩ (ρ' record.input.base.nextVreg) ∧
      cm' = cm ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          fr'
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceProof
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have availableX := restrict_regs_isSome (by rw [getAs_ok getX]; rfl)
  have availableY := restrict_regs_isSome (by rw [getAs_ok getY]; rfl)
  have originalX : fr.getAs x ty = .ok u :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem availableX)).symm.trans getX
  have originalY : fr.getAs y ty = .ok v :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := y) (ty := ty) (restrict_regs_of_mem availableY)).symm.trans getY
  have computed : instOutcome env cp fr cm (.binary .bor ty x y) =
      .ok ([⟨ty,Clif.Sem.binary .bor u v⟩],cm) := by
    simp [instOutcome,Clif.evalInst,Clif.BinaryOp.isShift,originalX,originalY]
  have equal := Prod.mk.inj (Clif.Res.ok.inj (evaluated.symm.trans computed))
  have memEq : cm' = cm := equal.2
  have evaluatedValue : instOutcome env cp fr cm (.binary .bor ty x y) =
      .ok ([⟨ty,Clif.Sem.binary .bor u v⟩],cm') := by rw [memEq]; exact computed
  obtain ⟨ρ',execution,value,kept,installed,interval⟩ := frame_5
    run scope dominated mirrored events records block statement current source clif results statementResults
    mapped recorded emitted selectedId refines dfg held getX getY
  have post := source_single_result_values source clif results sourceStep evaluatedValue installed
  exact ⟨ρ',execution,value,memEq,kept,post,interval⟩

open Backend.Stock.Proof.LogicalExtr Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 in
private theorem frame_18 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f) (mirrored : Bool)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary .bor ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (extrRule mirrored).id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (u v : BitVec ty.width) (ρ' : Nat → CV),
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v ∧ PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary .bor u v⟩ (ρ' record.input.base.nextVreg) ∧
      cm' = cm ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          fr'
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  obtain ⟨u,v,getX,getY⟩ := source_operands run scope dominated mirrored events block statement current source clif sourceStep
  obtain ⟨ρ',execution,value,memEq,kept,post,interval⟩ := frame_17
    run scope dominated mirrored events records block statement current source clif results statementResults
    mapped recorded emitted selectedId refines dfg held getX getY sourceStep
  exact ⟨u,v,ρ',getX,getY,execution,value,memEq,kept,post,interval⟩

open Backend.Stock.Proof.LogicalComplete Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 LogicalSelected in
private theorem frame_19 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (kind : Kind) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (u v : BitVec ty.width) (ρ' : Nat → CV),
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v ∧ PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary kind.cop u v⟩ (ρ' record.input.base.nextVreg) ∧
      cm' = cm ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          fr'
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  have inventory := record_selected_rule_ids run scope events records kind source clif recorded emitted
  obtain ⟨id,last,member⟩ : ∃ id, step.rules.getLast? = some id ∧ id ∈ candidateIds kind := by
    simpa only [Option.any_eq_true,List.contains_iff_mem] using inventory
  cases kind with
  | band =>
    simp only [candidateIds,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact frame_16 run scope dominated events records block statement current .band true
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · exact frame_16 run scope dominated events records block statement current .band false
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · exact frame_14 run scope dominated events records block statement current .band
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
  | bor =>
    simp only [candidateIds,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact frame_18 run scope dominated false events records block statement current
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · exact frame_18 run scope dominated true events records block statement current
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · exact frame_16 run scope dominated events records block statement current .bor true
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · exact frame_16 run scope dominated events records block statement current .bor false
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · exact frame_14 run scope dominated events records block statement current .bor
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
  | bxor =>
    simp only [candidateIds,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact frame_16 run scope dominated events records block statement current .bxor true
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · exact frame_16 run scope dominated events records block statement current .bxor false
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · exact frame_14 run scope dominated events records block statement current .bxor
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep

open Backend.Stock.Proof.BnotComplete Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 in
private theorem frame_20 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {x z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.unary .bnot ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u : BitVec ty.width}
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bnot u⟩ (ρ' record.input.base.nextVreg) ∧
      cm' = cm ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          fr'
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceProof
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have availableX := restrict_regs_isSome (by rw [getAs_ok getX]; rfl)
  have originalX : fr.getAs x ty = .ok u :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem availableX)).symm.trans getX
  have computed : instOutcome env cp fr cm (.unary .bnot ty x) =
      .ok ([⟨ty,Clif.Sem.unary .bnot u⟩],cm) := by
    simp [instOutcome,Clif.evalInst,originalX]
  have equal := Prod.mk.inj (Clif.Res.ok.inj (evaluated.symm.trans computed))
  have memEq : cm' = cm := equal.2
  have evaluatedValue : instOutcome env cp fr cm (.unary .bnot ty x) =
      .ok ([⟨ty,Clif.Sem.unary .bnot u⟩],cm') := by rw [memEq]; exact computed
  have inventory := record_selected_rule_ids run scope events records source clif recorded emitted
  obtain ⟨id,last,member⟩ : ∃ id, step.rules.getLast? = some id ∧ id ∈ candidateIds := by
    simpa only [Option.any_eq_true,List.contains_iff_mem] using inventory
  have values : ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bnot u⟩ (ρ' record.input.base.nextVreg) ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧ y ∈ availOf f (availIn f result.ctx) bi (j+1))
        event.ctx (withValue fr z ⟨ty,Clif.Sem.unary .bnot u⟩)
        (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
    simp only [candidateIds,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact frame_6 run scope dominated events records block statement current
        source clif results statementResults mapped recorded emitted last refines dfg held getX
    · exact frame_7 run scope dominated events records block statement current
        true source clif results statementResults mapped recorded emitted last refines dfg held getX
    · exact frame_7 run scope dominated events records block statement current
        false source clif results statementResults mapped recorded emitted last refines dfg held getX
  obtain ⟨ρ',execution,value,kept,installed,interval⟩ := values
  have post := source_single_result_values source clif results sourceStep evaluatedValue installed
  exact ⟨ρ',execution,value,memEq,kept,post,interval⟩

open Backend.Stock.Proof.BnotComplete Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 in
private theorem frame_21 {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {x z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.unary .bnot ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (u : BitVec ty.width) (ρ' : Nat → CV),
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧ PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bnot u⟩ (ρ' record.input.base.nextVreg) ∧
      cm' = cm ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          fr'
          (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) := by
  obtain ⟨u,getX⟩ := source_operands run scope dominated events block statement current source clif sourceStep
  obtain ⟨ρ',execution,value,memEq,kept,post,interval⟩ := frame_20
    run scope dominated events records block statement current source clif results statementResults
    mapped recorded emitted refines dfg held getX sourceStep
  exact ⟨u,ρ',getX,execution,value,memEq,kept,post,interval⟩

private theorem select_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block + j)
    {info : IInfo} {ty : Clif.Ty} {c x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.select ty c x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (CarryRel f result event.ctx event.block MR needed) record := by
  intro s s' hsource ρ w held
  obtain ⟨indexed, advance, sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func, dfg, memory, values⟩ := held.1
  rw [position] at dfg values
  obtain ⟨cty,test,u,v,getC,getX,getY⟩ := select_operands run scope dominated events block statement current source clif sourceStep
  obtain ⟨d,output,lower,upper,unchanged,execution⟩ := ScalarSelect.stock_lower_select_source_values
    run scope dominated events records block statement current source clif results statementResults mapped
    recorded emitted refines dfg getC getX getY values sourceStep
  obtain ⟨ρ',w',executed,world,post⟩ := execution w
  have kept := post.2.1
  have carried := record_frame_carry run scope dominated events split records statement current
    sourceStep available kept held.2
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,?_,carried⟩
  refine ⟨func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots,unchanged]
    exact stable _ _ _ _ world memory
  · simpa only [advance,position] using post.2.2

private theorem addsub_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block + j)
    (subtract : Bool) {info : IInfo} {ty : Clif.Ty} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (CarryRel f result event.ctx event.block MR needed) record := by
  intro s s' hsource ρ w held
  obtain ⟨indexed, advance, sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func, dfg, memory, values⟩ := held.1
  rw [position] at dfg values
  obtain ⟨u,v,ρ',getX,getY,execution,value,unchanged,kept,post,keptInterval⟩ :=
    frame_12
      run scope dominated events records block statement current subtract source clif results statementResults
      mapped recorded emitted refines dfg values sourceStep
  obtain ⟨w',executed,world⟩ := execution w
  have carried := record_frame_carry run scope dominated events split records statement current
    sourceStep available keptInterval held.2
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,?_,carried⟩
  refine ⟨func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots,unchanged]
    exact stable _ _ _ _ (SameWorld.nf world) memory
  · simpa only [advance,position] using post

private theorem logical_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block + j)
    (kind : LogicalSelected.Kind) {info : IInfo} {ty : Clif.Ty} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.binary kind.cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (CarryRel f result event.ctx event.block MR needed) record := by
  intro s s' hsource ρ w held
  obtain ⟨indexed, advance, sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func, dfg, memory, values⟩ := held.1
  rw [position] at dfg values
  obtain ⟨u,v,ρ',getX,getY,execution,value,unchanged,kept,post,keptInterval⟩ :=
    frame_19
      run scope dominated events records block statement current kind source clif results statementResults
      mapped recorded emitted refines dfg values sourceStep
  obtain ⟨w',executed,world⟩ := execution w
  have carried := record_frame_carry run scope dominated events split records statement current
    sourceStep available keptInterval held.2
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,?_,carried⟩
  refine ⟨func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots,unchanged]
    exact stable _ _ _ _ (SameWorld.nf world) memory
  · simpa only [advance,position] using post

private theorem bnot_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block + j)
    {info : IInfo} {ty : Clif.Ty} {x z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.unary .bnot ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (CarryRel f result event.ctx event.block MR needed) record := by
  intro s s' hsource ρ w held
  obtain ⟨indexed, advance, sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func, dfg, memory, values⟩ := held.1
  rw [position] at dfg values
  obtain ⟨u,ρ',getX,execution,value,unchanged,kept,post,keptInterval⟩ :=
    frame_21
      run scope dominated events records block statement current source clif results statementResults
      mapped recorded emitted refines dfg values sourceStep
  obtain ⟨w',executed,world⟩ := execution w
  have carried := record_frame_carry run scope dominated events split records statement current
    sourceStep available keptInterval held.2
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,?_,carried⟩
  refine ⟨func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots,unchanged]
    exact stable _ _ _ _ (SameWorld.nf world) memory
  · simpa only [advance,position] using post

private theorem mul_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block + j)
    {info : IInfo} {ty : Clif.Ty} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.binary .imul ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (CarryRel f result event.ctx event.block MR needed) record := by
  intro s s' hsource ρ w held
  obtain ⟨indexed, advance, sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func, dfg, memory, values⟩ := held.1
  rw [position] at dfg values
  obtain ⟨ρ',execution,unchanged,post,kept⟩ := MulComplete.record_source_framed
    run scope dominated events records block statement current source clif results statementResults
    mapped recorded emitted refines values sourceStep
  obtain ⟨w',executed,world⟩ := execution w
  have carried := record_frame_carry run scope dominated events split records statement current
    sourceStep available kept held.2
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,?_,carried⟩
  refine ⟨func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots,unchanged]
    exact stable _ _ _ _ (SameWorld.nf world) memory
  · simpa only [advance,position] using post

private theorem shift_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block + j)
    (kind : ScalarShift.Kind) {info : IInfo} {ty : Clif.Ty} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.binary kind.cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (CarryRel f result event.ctx event.block MR needed) record := by
  intro s s' hsource ρ w held
  obtain ⟨indexed, advance, sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func, dfg, memory, values⟩ := held.1
  rw [position] at dfg values
  obtain ⟨ρ',execution,unchanged,post,kept⟩ := ShiftComplete.record_source_framed
    run scope dominated events records block statement current kind source clif results statementResults
    mapped recorded emitted refines dfg values sourceStep
  obtain ⟨w',executed,world⟩ := execution w
  have carried := record_frame_carry run scope dominated events split records statement current
    sourceStep available kept held.2
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,?_,carried⟩
  refine ⟨func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots,unchanged]
    exact stable _ _ _ _ (SameWorld.nf world) memory
  · simpa only [advance,position] using post

private theorem extend_of_memory_formats_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block + j)
    (sourceFamily : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastComplete.MemoryFormat stm.inst) (sg : Bool)
    {info : IInfo} {ty : Clif.Ty} {x z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.extend (ScalarCast.extendOp sg) ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (CarryRel f result event.ctx event.block MR needed) record := by
  intro s s' hsource ρ w held
  obtain ⟨indexed, advance, sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func, dfg, memory, values⟩ := held.1
  rw [position] at dfg values
  obtain ⟨unchanged,execution⟩ := CastComplete.extend_source_of_memory_formats_framed
    run scope dominated events records block statement current sourceFamily sg source clif results statementResults
    mapped recorded emitted refines dfg values sourceStep
  obtain ⟨ρ',w',executed,world,post,kept⟩ := execution w
  have carried := record_frame_carry run scope dominated events split records statement current
    sourceStep available kept held.2
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,?_,carried⟩
  refine ⟨func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots,unchanged]
    exact stable _ _ _ _ world memory
  · simpa only [advance,position] using post

private theorem reduce_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block + j)
    {info : IInfo} {ty : Clif.Ty} {x z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.ireduce ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (CarryRel f result event.ctx event.block MR needed) record := by
  intro s s' hsource ρ w held
  obtain ⟨indexed, advance, sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func, dfg, memory, values⟩ := held.1
  rw [position] at dfg values
  obtain ⟨ρ',execution,unchanged,post,kept⟩ := CastComplete.reduce_source_framed
    run scope dominated events records block statement current source clif results statementResults
    mapped recorded emitted values sourceStep
  obtain ⟨w',executed,world⟩ := execution w
  have carried := record_frame_carry run scope dominated events split records statement current
    sourceStep available kept held.2
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,?_,carried⟩
  refine ⟨func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots,unchanged]
    exact stable _ _ _ _ (SameWorld.nf world) memory
  · simpa only [advance,position] using post

private theorem unary_bit_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block + j)
    {op : Clif.UnaryOp} (unary : BitBody.Unary op)
    {info : IInfo} {ty : Clif.Ty} {x z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.unary op ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (CarryRel f result event.ctx event.block MR needed) record := by
  intro s s' hsource ρ w held
  obtain ⟨indexed, advance, sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func, dfg, memory, values⟩ := held.1
  rw [position] at dfg values
  obtain ⟨ρ',execution,unchanged,post,kept⟩ := BitBody.unary_source_framed
    run scope dominated events records block statement current unary source clif results statementResults
    mapped recorded emitted refines dfg values sourceStep
  obtain ⟨w',executed,world⟩ := execution w
  have carried := record_frame_carry run scope dominated events split records statement current
    sourceStep available kept held.2
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,?_,carried⟩
  refine ⟨func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots,unchanged]
    exact stable _ _ _ _ (SameWorld.nf world) memory
  · simpa only [advance,position] using post

private theorem rotate_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block + j)
    (left : Bool)
    {info : IInfo} {ty : Clif.Ty} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.binary (ScalarRotate.rotateOp left) ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (CarryRel f result event.ctx event.block MR needed) record := by
  intro s s' hsource ρ w held
  obtain ⟨indexed, advance, sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func, dfg, memory, values⟩ := held.1
  rw [position] at dfg values
  obtain ⟨ρ',execution,unchanged,post,kept⟩ := BitBody.rotate_source_framed
    run scope dominated events records block statement current left source clif results statementResults
    mapped recorded emitted refines dfg values sourceStep
  obtain ⟨w',executed,world⟩ := execution w
  have carried := record_frame_carry run scope dominated events split records statement current
    sourceStep available kept held.2
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,?_,carried⟩
  refine ⟨func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots,unchanged]
    exact stable _ _ _ _ (SameWorld.nf world) memory
  · simpa only [advance,position] using post

private theorem popcount_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block + j)
    {info : IInfo} {ty : Clif.Ty} {x z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.unary .popcnt ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (CarryRel f result event.ctx event.block MR needed) record := by
  intro s s' hsource ρ w held
  obtain ⟨indexed, advance, sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func, dfg, memory, values⟩ := held.1
  rw [position] at dfg values
  obtain ⟨u,d,ρ',getX,output,bounds,execution,value,unchanged,kept,post⟩ := ScalarPopcount.stock_lower_popcount_source_by_instruction
    run scope dominated events records block statement current source clif results statementResults
    mapped recorded emitted refines dfg values sourceStep
  obtain ⟨w',executed,world⟩ := execution w
  have carried := record_frame_carry run scope dominated events split records statement current
    sourceStep available kept held.2
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,?_,carried⟩
  refine ⟨func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots,unchanged]
    exact stable _ _ _ _ (SameWorld.nf world) memory
  · simpa only [advance,position] using post

private theorem minmax_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block + j)
    (unsigned maximum : Bool)
    {info : IInfo} {ty : Clif.Ty} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.binary (MinMaxBody.operation unsigned maximum) ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (CarryRel f result event.ctx event.block MR needed) record := by
  intro s s' hsource ρ w held
  obtain ⟨indexed, advance, sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func, dfg, memory, values⟩ := held.1
  rw [position] at dfg values
  obtain ⟨u,v,getX,getY⟩ := ScalarSelect.stock_lower_minmax_source_operands
    run scope dominated events block statement current unsigned maximum source clif sourceStep
  have availableX := restrict_regs_isSome (by rw [getAs_ok getX]; rfl)
  have availableY := restrict_regs_isSome (by rw [getAs_ok getY]; rfl)
  have typeX := stock_lower_available_getAs_type run events availableX dfg getX
  have typeY := stock_lower_available_getAs_type run events availableY dfg getY
  obtain ⟨d,output,lower,upper,unchanged,execution⟩ := ScalarSelect.stock_lower_minmax_actual_source_values
    run scope dominated events records block statement current unsigned maximum source clif typeX typeY
    results statementResults mapped recorded emitted refines dfg getX getY values sourceStep
  obtain ⟨ρ',w',executed,world,value,kept,post⟩ := execution w
  have carried := record_frame_carry run scope dominated events split records statement current
    sourceStep available kept held.2
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,?_,carried⟩
  refine ⟨func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots,unchanged]
    exact stable _ _ _ _ world memory
  · simpa only [advance,position] using post

private theorem cmp_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block + j)
    (cc : Clif.IntCC)
    {info : IInfo} {ty : Clif.Ty} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.icmp cc ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (CarryRel f result event.ctx event.block MR needed) record := by
  intro s s' hsource ρ w held
  obtain ⟨indexed, advance, sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func, dfg, memory, values⟩ := held.1
  rw [position] at dfg values
  obtain ⟨u,v,getX,getY⟩ := ScalarCmp.stock_lower_cmp_nonconstant_source_operands
    run scope dominated events block statement current source clif sourceStep
  have availableX := restrict_regs_isSome (by rw [getAs_ok getX]; rfl)
  have availableY := restrict_regs_isSome (by rw [getAs_ok getY]; rfl)
  have typeX := stock_lower_available_getAs_type run events availableX dfg getX
  have typeY := stock_lower_available_getAs_type run events availableY dfg getY
  obtain ⟨d,output,lower,upper,unchanged,execution⟩ := ScalarCmp.stock_lower_cmp_actual_source_values
    run scope dominated events records block statement current source clif typeX typeY
    results statementResults mapped recorded emitted refines dfg getX getY values sourceStep
  obtain ⟨ρ',w',executed,world,value,kept,post⟩ := execution w
  have carried := record_frame_carry run scope dominated events split records statement current
    sourceStep available kept held.2
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,?_,carried⟩
  refine ⟨func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots,unchanged]
    exact stable _ _ _ _ world memory
  · simpa only [advance,position] using post

private theorem highmul_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block + j)
    (signed : Bool) {info : IInfo} {ty : Clif.Ty} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.binary (if signed then .smulhi else .umulhi) ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (CarryRel f result event.ctx event.block MR needed) record := by
  intro s s' hsource ρ w held
  obtain ⟨indexed, advance, sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func, dfg, memory, values⟩ := held.1
  rw [position] at dfg values
  obtain ⟨u,v,d,ρ',getX,getY,output,bounds,execution,value,unchanged,kept,post⟩ := ScalarHighMul.stock_lower_highmul_source_by_instruction
    run scope dominated events records block statement current signed source clif results statementResults
    mapped recorded emitted refines dfg values sourceStep
  obtain ⟨w',executed,world⟩ := execution w
  have carried := record_frame_carry run scope dominated events split records statement current
    sourceStep available kept held.2
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,?_,carried⟩
  refine ⟨func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots,unchanged]
    exact stable _ _ _ _ (SameWorld.nf world) memory
  · simpa only [advance,position] using post

private theorem bmask_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block+j)
    {info : IInfo} {ty : Clif.Ty} {x z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.bmask ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (CarryRel f result event.ctx event.block MR needed) record := by
  intro s s' sourceRun ρ w held
  obtain ⟨indexed,advance,sourceStep⟩ := sourceRun
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func,dfg,memory,values⟩ := held.1
  rw [position] at dfg values
  obtain ⟨value,d,lookup,unchanged,output,bounds,execution⟩ := ScalarMask.stock_lower_bmask_available_source
    run scope dominated events records block statement current source clif results statementResults mapped
      recorded emitted refines dfg values sourceStep
  obtain ⟨ρ',w',executed,world,valueHeld,kept,post⟩ := execution w
  have carried := record_frame_carry run scope dominated events split records statement current
    sourceStep available kept held.2
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,?_,carried⟩
  refine ⟨func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots,unchanged]
    exact stable _ _ _ _ world memory
  · simpa only [advance,position] using post

private theorem constant_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block + j)
    {info : IInfo} {ty : Clif.Ty} {imm : BitVec ty.width} {x a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.iconst ty imm))
    (results : info.results = [x]) (statementResults : stm.results = [x])
    (mapped : event.ctx.valueReg? x = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (CarryRel f result event.ctx event.block MR needed) record := by
  have normal := stock_lower_constant_scan_fall_refines run scope dominated events records block statement current
    source clif results statementResults mapped recorded emitted refines driver stable (env := env) (cp := cp)
  intro s s' sourceStep ρ w held
  obtain ⟨ρ',w',executed,post⟩ := normal s s' sourceStep ρ w held.1
  have defs := constant_record_fresh_defs run scope events records source clif results mapped recorded emitted
  exact ⟨ρ',w',executed,post,record_fresh_carry run scope dominated events split records statement current
    sourceStep.2.2 available defs executed held.2⟩

private theorem scalar_emitted_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {b : Clif.Block} {j : Nat} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block+j)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {info : IInfo} {z a : Nat} (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some stm.inst) (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    (family : HighMulBody.Family stm.inst)
    (formats : ∀ block ∈ f.blocks,∀ stm ∈ block.body,CastComplete.MemoryFormat stm.inst)
    {term : ScanRecord} {body : BlockScan} (split : SourceBodySplit f event b term body)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (CarryRel f result event.ctx event.block MR needed) record := by
  rcases family with ((((((((((⟨subtract,ty,x,y,shape⟩ | ⟨ty,c,x,y,shape⟩ | ⟨kind,ty,x,y,shape⟩) | ⟨ty,imm,shape⟩) | ⟨ty,x,shape⟩) | ⟨ty,x,y,shape⟩) | ⟨kind,ty,x,y,shape⟩) | ⟨op,ty,x,shape⟩ | ⟨ty,x,shape⟩) | ⟨op,ty,x,unary,shape⟩ | ⟨left,ty,x,y,shape⟩) | ⟨ty,x,shape⟩) | ⟨unsigned,maximum,ty,x,y,shape⟩) | ⟨cc,ty,x,y,shape⟩) | ⟨signed,ty,x,y,shape⟩
  · exact addsub_carry run scope dominated events records block statement current subtract source
      (clif.trans (congrArg some shape)) results statementResults mapped recorded emitted split available refines stable
  · exact select_carry run scope dominated events records block statement current source
      (clif.trans (congrArg some shape)) results statementResults mapped recorded emitted split available refines stable
  · exact logical_carry run scope dominated events records block statement current kind source
      (clif.trans (congrArg some shape)) results statementResults mapped recorded emitted split available refines stable
  · exact constant_carry run scope dominated events records block statement current source
      (clif.trans (congrArg some shape)) results statementResults mapped recorded emitted split available refines driver stable
  · exact bnot_carry run scope dominated events records block statement current source
      (clif.trans (congrArg some shape)) results statementResults mapped recorded emitted split available refines stable
  · exact mul_carry run scope dominated events records block statement current source
      (clif.trans (congrArg some shape)) results statementResults mapped recorded emitted split available refines stable
  · exact shift_carry run scope dominated events records block statement current kind source
      (clif.trans (congrArg some shape)) results statementResults mapped recorded emitted split available refines stable
  · cases op with
    | uextend =>
      exact extend_of_memory_formats_carry run scope dominated events records block statement current formats false
        source (clif.trans (congrArg some shape)) results statementResults mapped recorded emitted split available refines stable
    | sextend =>
      exact extend_of_memory_formats_carry run scope dominated events records block statement current formats true
        source (clif.trans (congrArg some shape)) results statementResults mapped recorded emitted split available refines stable
  · exact reduce_carry run scope dominated events records block statement current source
      (clif.trans (congrArg some shape)) results statementResults mapped recorded emitted split available stable
  · exact unary_bit_carry run scope dominated events records block statement current unary source
      (clif.trans (congrArg some shape)) results statementResults mapped recorded emitted split available refines stable
  · exact rotate_carry run scope dominated events records block statement current left source
      (clif.trans (congrArg some shape)) results statementResults mapped recorded emitted split available refines stable
  · exact popcount_carry run scope dominated events records block statement current source
      (clif.trans (congrArg some shape)) results statementResults mapped recorded emitted split available refines stable
  · exact minmax_carry run scope dominated events records block statement current unsigned maximum source
      (clif.trans (congrArg some shape)) results statementResults mapped recorded emitted split available refines stable
  · exact cmp_carry run scope dominated events records block statement current cc source
      (clif.trans (congrArg some shape)) results statementResults mapped recorded emitted split available refines stable
  · exact highmul_carry run scope dominated events records block statement current signed source
      (clif.trans (congrArg some shape)) results statementResults mapped recorded emitted split available refines stable

private theorem records_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {body : BlockScan}
    (scanned : ScansSpec exec indices input body) :
    ∀ record ∈ body.records,exec record.inst record.input = .ok record.output := by
  induction scanned with
  | nil => simp
  | cons head tail ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member


/-- The complete existing scalar/division/mask source family carries inherited
entry values through an actual body and its first trap. All record frames are
derived from the original compiler run, with no new accepted-input premise. -/
theorem scalar_body_carry_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    (formats : ∀ block ∈ f.blocks,∀ stm ∈ block.body,CastComplete.MemoryFormat stm.inst)
    (family : ∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} :
    (∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
      (sourceBodyIndices f event.block b).reverse s s' → ∀ ρ w,
      CarryRel f result event.ctx event.block MR needed body.state s ρ w → ∃ ρ' w',
        seqRun isem (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
          some (.fall ρ' w') ∧ CarryRel f result event.ctx event.block MR needed term.output.state s' ρ' w') ∧
    (∀ s code,SourceTrapSteps (IndexedSourceInst env cp f event.ctx event.block)
      (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
      (sourceBodyIndices f event.block b).reverse s code → ∀ ρ w,
      CarryRel f result event.ctx event.block MR needed body.state s ρ w →
        TrapRun isem (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w code) := by
  have classified : ∀ record ∈ body.records,MaskBody.Record f event.ctx event.block record := by
    intro record member
    obtain ⟨j,stm,statement,current⟩ := split.positions record member
    obtain ⟨info,source,clif,_⟩ := ArithmeticBody.body_source_info run events split statement current
    rcases family stm (List.mem_of_getElem? statement) with (scalar | ⟨op,ty,x,y,division⟩) | ⟨ty,x,mask⟩ | nop
    · exact .old (.scalar split.block statement current source clif scalar
        (QuietSourceColors.actual_quiet_source_record_at_block run scope events split member statement current
          (HighMulBody.family_quiet scalar) (HighMulBody.family_single scalar f)))
    · exact .old (DivBody.actual_division_record run scope formats events split member statement current division)
    · exact .bmask split.block statement current mask source (clif.trans (congrArg some mask))
        (QuietSourceColors.actual_quiet_source_record_at_block run scope events split member statement current
          (by rw [mask]; rfl) (by rw [mask]; rfl))
    · obtain ⟨step,recorded,omitted⟩ := MaskBody.actual_nop_record_at_block run scope events split member statement current nop
      exact .nop split.block statement current source (clif.trans (congrArg some nop)) recorded omitted
  have locals : ∀ record ∈ body.records,
      ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
        (CarryRel f result event.ctx event.block MR needed) record := by
    intro record member
    have omittedCase : ∀ {j stm step},b.body[j]? = some stm → record.inst = blockStart f event.block+j →
        record.output.step = some step → step.decision = .omitted →
        ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
          (CarryRel f result event.ctx event.block MR needed) record := by
      intro j stm step statement current recorded omitted s s' source ρ w held
      obtain ⟨ρ',w',executed,post⟩ := stock_lower_omitted_scan_fall_refines run scope dominated events
        (split.retained record member) split.block statement current recorded omitted s s' source ρ w held.1
      have empty : record.output.emitted = #[] := by
        obtain ⟨_,_,_,_,_,_,_,empty,_⟩ := scan_omitted (records_execute split.scanned record member) recorded omitted
        exact empty
      exact ⟨ρ',w',executed,post,record_fresh_carry run scope dominated events split
        (split.retained record member) statement current source.2.2 available
        (by simp [empty]) executed held.2⟩
    cases classified record member with
    | old actual =>
      cases actual with
      | scalar block statement current source clif scalar actual =>
        cases Option.some.inj (block.symm.trans split.block)
        obtain ⟨j',b',stm',found,atStmt,indexed,step,recorded,decision⟩ := actual
        cases Option.some.inj (found.symm.trans split.block)
        have sameJ := Nat.add_left_cancel (indexed.symm.trans current)
        subst j'
        cases Option.some.inj (atStmt.symm.trans statement)
        rcases decision with omitted | ⟨emitted,info,z,a,source,clif,one,results,mapped⟩
        · exact omittedCase statement current recorded omitted
        · exact scalar_emitted_carry run scope dominated events (split.retained record member)
            split.block statement current recorded emitted source clif one results mapped scalar formats
            split available refines driver stable
      | division block statement current source clif one results mapped recorded emitted =>
        cases Option.some.inj (block.symm.trans split.block)
        exact division_scan_carry_fall_refines run scope dominated events (split.retained record member)
          split statement current _ source clif one results mapped recorded emitted available refines stable
    | bmask block statement current mask source0 clif0 actual =>
      cases Option.some.inj (block.symm.trans split.block)
      obtain ⟨j',b',stm',found,atStmt,indexed,step,recorded,decision⟩ := actual
      cases Option.some.inj (found.symm.trans split.block)
      have sameJ := Nat.add_left_cancel (indexed.symm.trans current)
      subst j'
      cases Option.some.inj (atStmt.symm.trans statement)
      rcases decision with omitted | ⟨emitted,info,z,a,source,clif,one,results,mapped⟩
      · exact omittedCase statement current recorded omitted
      · exact bmask_carry run scope dominated events (split.retained record member) split.block statement current
          source (clif.trans (congrArg some mask)) one results mapped recorded emitted split available refines stable
    | nop block statement current source clif recorded omitted =>
      cases Option.some.inj (block.symm.trans split.block)
      exact omittedCase statement current recorded omitted
  refine ⟨split.scanned.fall_refines locals,split.scanned.local_trap_refines locals ?_⟩
  intro record member s code failed ρ w held
  exact MaskBody.Record.trap_refines run scope dominated events (split.retained record member)
    (classified record member) refines s code failed ρ w held.1

end Backend.Stock.Proof.Inherited
