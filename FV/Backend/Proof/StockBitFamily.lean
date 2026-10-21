import FV.Backend.Proof.StockUnaryDispatch
import FV.Backend.Proof.StockCastNotrap
import FV.Backend.Proof.StockCastFamily
import FV.Backend.Proof.StockCountSourceValues
import FV.Backend.Proof.StockBitrevSourceValues
import FV.Backend.Proof.StockBswapSourceValues
import FV.Backend.Proof.StockRotateSourceValues
namespace Backend.Stock.Proof.BitBody
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

def Unary (op : Clif.UnaryOp) : Prop := op = .ineg ∨ op = .clz ∨ op = .ctz ∨ op = .bitrev ∨ op = .bswap

def Family (inst : Clif.Inst) : Prop :=
  CastBody.Family inst ∨
    (∃ op ty x, Unary op ∧ inst = .unary op ty x) ∨
    (∃ left ty x y, inst = .binary (ScalarRotate.rotateOp left) ty x y)

theorem family_pure {inst : Clif.Inst} (family : Family inst) : pureInst inst = true := by
  rcases family with old | ⟨op,ty,x,unary,rfl⟩ | ⟨left,ty,x,y,rfl⟩
  · exact CastBody.family_pure old
  · rfl
  · cases left <;> rfl

theorem family_quiet {inst : Clif.Inst} (family : Family inst) : colored inst = false := by
  rcases family with old | ⟨op,ty,x,unary,rfl⟩ | ⟨left,ty,x,y,rfl⟩
  · exact CastBody.family_quiet old
  · rfl
  · cases left <;> rfl

theorem family_single {inst : Clif.Inst} (family : Family inst) (f : Clif.Function) :
    (inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·)).map List.length = some 1 := by
  rcases family with old | ⟨op,ty,x,unary,rfl⟩ | ⟨left,ty,x,y,rfl⟩
  · exact CastBody.family_single old f
  · rfl
  · cases left <;> rfl

/-- Extended pure syntax still derives all cast look-through exclusions. -/
theorem family_formats {inst : Clif.Inst} (family : Family inst) : CastBody.SafeFormat inst := by
  rcases family with old | ⟨op,ty,x,unary,rfl⟩ | ⟨left,ty,x,y,rfl⟩
  · exact CastBody.family_formats old
  · simp [CastBody.SafeFormat,instNames]
  · cases left <;> simp [CastBody.SafeFormat,instNames,ScalarRotate.rotateOp]

theorem bit_inst_notrap {inst : Clif.Inst} (family : Family inst)
    (fr : Clif.Frame) (cm : Clif.Mem) (c : Clif.TrapCode) : Clif.evalInst fr cm inst ≠ .trap c := by
  rcases family with old | ⟨op,ty,x,unary,rfl⟩ | ⟨left,ty,x,y,rfl⟩
  · exact CastBody.cast_inst_notrap old fr cm c
  · cases getX : fr.getAs x ty with
    | trap code => exact False.elim (PureBody.frame_getAs_notrap fr x ty code getX)
    | stuck message => simp [Clif.evalInst,getX]
    | ok u => simp [Clif.evalInst,getX]
  · cases getX : fr.getAs x ty with
    | trap code => exact False.elim (PureBody.frame_getAs_notrap fr x ty code getX)
    | stuck message => simp [Clif.evalInst,getX]
    | ok u =>
      cases count : fr.regs y with
      | none => cases left <;> simp [Clif.evalInst,ScalarRotate.rotateOp,Clif.BinaryOp.isShift,getX,Clif.Frame.get,count]
      | some amount => cases left <;> simp [Clif.evalInst,ScalarRotate.rotateOp,Clif.BinaryOp.isShift,getX,Clif.Frame.get,count,Clif.Sem.shift,Clif.Res.ofOption]

theorem bit_source_notrap {env : Clif.Env} {cp : Clif.Program} (fuel : Nat)
    (s : Clif.State) (callers : s.callers = []) (family : ∀ stm ∈ s.frame.body,Family stm.inst)
    {xs : List Nat} (ret : s.frame.term = .ret xs) (code : Clif.TrapCode) :
    Clif.runLoop env cp fuel s ≠ .trapped code := by
  apply PureBody.pure_source_notrap fuel s callers ?_ ret code
  intro stm member
  exact ⟨family_pure (family stm member),bit_inst_notrap (family stm member)⟩
theorem unary_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {op : Clif.UnaryOp} (unary : Unary op)
    {info : IInfo} {x z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.unary op ty x))
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
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧ cm' = cm ∧
      ValuesHeld (fun v => Demanded record.input v ∧
        v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  rcases unary with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨u,d,ρ',getX,output,bounds,execution,value,unchanged,kept,post⟩ :=
      stock_lower_neg_source_by_instruction run scope dominated events records block statement current
        source clif results statementResults mapped recorded emitted refines held sourceStep
    exact ⟨ρ',execution,unchanged,post⟩
  · obtain ⟨u,d,ρ',getX,output,bounds,execution,value,unchanged,kept,post⟩ :=
      ScalarCount.stock_lower_count_source_by_instruction run scope dominated false events records block statement current
        source clif results statementResults mapped recorded emitted refines dfg held sourceStep
    exact ⟨ρ',execution,unchanged,post⟩
  · obtain ⟨u,d,ρ',getX,output,bounds,execution,value,unchanged,kept,post⟩ :=
      ScalarCount.stock_lower_count_source_by_instruction run scope dominated true events records block statement current
        source clif results statementResults mapped recorded emitted refines dfg held sourceStep
    exact ⟨ρ',execution,unchanged,post⟩
  · obtain ⟨u,d,ρ',getX,output,bounds,execution,value,unchanged,kept,post⟩ :=
      stock_lower_bitrev_source_by_instruction run scope dominated events records block statement current
        source clif results statementResults mapped recorded emitted refines held sourceStep
    exact ⟨ρ',execution,unchanged,post⟩
  · obtain ⟨u,d,ρ',getX,output,bounds,execution,value,unchanged,kept,post⟩ :=
      stock_lower_bswap_source_by_instruction run scope dominated events records block statement current
        source clif results statementResults mapped recorded emitted refines held sourceStep
    exact ⟨ρ',execution,unchanged,post⟩

theorem rotate_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (left : Bool)
    {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.binary (ScalarRotate.rotateOp left) ty x y))
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
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧ cm' = cm ∧
      ValuesHeld (fun v => Demanded record.input v ∧
        v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨u,amount,d,ρ',getX,getY,output,bounds,execution,value,unchanged,kept,post⟩ :=
    ScalarRotate.stock_lower_rotate_source_by_instruction run scope dominated left events records
      block statement current source clif results statementResults mapped recorded emitted refines dfg held sourceStep
  exact ⟨ρ',execution,unchanged,post⟩

end Backend.Stock.Proof.BitBody
