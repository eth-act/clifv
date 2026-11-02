import FV.Backend.Proof.StockArithmeticBodyRefines
import FV.Backend.Proof.StockBlockCode
import FV.Backend.Proof.StockEntryPrelude
import FV.Backend.Proof.StockArithmeticTerminalDefined
import FV.Backend.Proof.StockReturnContract

/-! Original-source simulation for complete straight-line select/add/sub bodies. -/
namespace Backend.Stock.Proof.MixedBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- A syntactic family, with no execution or register-map certificate. -/
def Family (inst : Clif.Inst) : Prop :=
  (∃ subtract : Bool, ∃ ty x y,
    inst = .binary (if subtract then .isub else .iadd) ty x y) ∨
  (∃ ty c x y, inst = .select ty c x y)

private theorem select_result {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i : Nat} {info : IInfo} {ty : Clif.Ty} {c x y : Nat}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.select ty c x y)) :
    ∃ z, info.results = [z] := by
  obtain ⟨tys,result,typed,arity⟩ := inv.resTys i info _ source clif
  have result' : tys = [ty] := by
    simpa [Clif.Inst.resultTypes] using result.symm
  rw [result'] at arity
  cases values : info.results with
  | nil => simp [values] at arity
  | cons z rest =>
    cases rest with
    | nil => exact ⟨z,rfl⟩
    | cons a tail => simp [values] at arity

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

/-- Derive actual emitted/omitted select and arithmetic record coverage from
original source syntax and successful lowering, retaining unused/dead operations. -/
theorem actual_mixed_families {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ term body, SourceBodySplit f event b term body ∧
      ∀ record ∈ body.records, SelectAddSubOrOmittedRecord f event.ctx event.block record := by
  have quiet : ∀ stm ∈ b.body, colored stm.inst = false := by
    intro stm member
    rcases family stm member with ⟨subtract,ty,x,y,shape⟩ | ⟨ty,c,x,y,shape⟩
    · rw [shape]; cases subtract <;> rfl
    · rw [shape]; rfl
  obtain ⟨term,body,split,decisions⟩ := stock_lower_pure_body_decisions run scope blocks quiet events
  refine ⟨term,body,split,?_⟩
  intro record member
  obtain ⟨j,stm,statement,current⟩ := split.positions record member
  obtain ⟨step,recorded,decision⟩ := decisions record member
  rcases decision with omitted | emitted
  · exact Or.inl ⟨j,b,stm,split.block,statement,current,step,recorded,Or.inl omitted⟩
  · obtain ⟨info,source,clif,results⟩ :=
      ArithmeticBody.body_source_info run events split statement current
    have inv := (stock_lower_record_context run scope events).1
    obtain ⟨emission,emissionRun,scan⟩ := stock_emitted_scan
      (scans_execute split.scanned record member) recorded emitted
    have atInst : event.ctx.insts[record.inst]! = info := by
      simp only [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,source,Option.getD_some]
    rcases family stm (List.mem_of_getElem? statement) with
      ⟨subtract,ty,x,y,shape⟩ | ⟨ty,c,x,y,shape⟩
    · have clif' : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y) := by
        rw [clif,shape]
      obtain ⟨z,one⟩ := ArithmeticBody.arithmetic_result inv subtract source clif'
      obtain ⟨r,mapped⟩ := ArithmeticBody.emission_result_mapped emissionRun
        (by rw [atInst]; exact one)
      obtain ⟨a,rfl⟩ := inv.valueReg z r mapped
      exact Or.inr ⟨j,b,stm,split.block,statement,current,step,recorded,emitted,
        subtract,info,ty,x,y,z,a,source,clif',one,results.symm.trans one,mapped⟩
    · have clif' : info.clif = some (.select ty c x y) := by rw [clif,shape]
      obtain ⟨z,one⟩ := select_result inv source clif'
      obtain ⟨r,mapped⟩ := ArithmeticBody.emission_result_mapped emissionRun
        (by rw [atInst]; exact one)
      obtain ⟨a,rfl⟩ := inv.valueReg z r mapped
      exact Or.inl ⟨j,b,stm,split.block,statement,current,step,recorded,Or.inr
        ⟨emitted,info,ty,c,x,y,z,a,source,clif',one,results.symm.trans one,mapped⟩⟩

/-- Complete mixed ordinary-body simulation with record-family and map facts
derived internally, preserving the original source and related-world boundary. -/
theorem actual_mixed_body_refines {f : Clif.Function} {result : Result}
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
  obtain ⟨term,body,split,families⟩ := actual_mixed_families run scope blocks family events
  refine ⟨term,body,split,?_⟩
  intro s s' source ρ w held
  apply stock_lower_select_addsub_omitted_body_fall_refines run scope dominated events
    split.scanned split.retained families refines stable s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using source
  · simpa only [split.state] using held


private theorem step_of_family {env : Clif.Env} {cp : Clif.Program}
    {s : Clif.State} {stm : Clif.Stmt} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) (family : Family stm.inst) :
    Clif.step env cp s = Clif.StepResult.ofRes (Clif.evalInst s.frame s.mem stm.inst)
      (fun (vs,cm) => Clif.continueWith s rest stm.results vs cm) := by
  rcases family with ⟨subtract,ty,x,y,shape⟩ | ⟨ty,c,x,y,shape⟩
  all_goals unfold Clif.step; simp only [remaining,shape]

private theorem outcome_of_family {env : Clif.Env} {cp : Clif.Program}
    {fr : Clif.Frame} {cm : Clif.Mem} {inst : Clif.Inst} (family : Family inst) :
    instOutcome env cp fr cm inst = Clif.evalInst fr cm inst := by
  rcases family with ⟨subtract,ty,x,y,shape⟩ | ⟨ty,c,x,y,shape⟩
  all_goals rw [shape]; rfl

/-- The original executable source step supplies the mixed-family indexed step. -/
theorem actual_mixed_source_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) {record : ScanRecord} {j : Nat} {stm : Clif.Stmt}
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f event.block + j)
    (family : Family stm.inst)
    {env : Clif.Env} {cp : Clif.Program} {s t : Clif.State} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) (next : Clif.step env cp s = .next t) :
    IndexedSourceInst env cp f event.ctx event.block record.inst
      (j,s.frame,s.mem) (j+1,t.frame,t.mem) := by
  obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split statement current
  have remaining' : s.frame.body = ⟨info.results,stm.inst⟩ :: rest := by
    rw [remaining,results]
  rw [step_of_family remaining family] at next
  cases evaluated : Clif.evalInst s.frame s.mem stm.inst with
  | trap code => simp only [evaluated,Clif.StepResult.ofRes] at next; cases next
  | stuck message => simp only [evaluated,Clif.StepResult.ofRes] at next; cases next
  | ok value =>
    obtain ⟨vals,mem⟩ := value
    simp only [evaluated,Clif.StepResult.ofRes] at next
    unfold Clif.continueWith at next
    cases written : s.frame.regs.setMany stm.results vals with
    | none => simp only [written] at next; cases next
    | some regs =>
      simp only [written] at next
      cases next
      refine ⟨current,rfl,info,stm.inst,vals,regs,rest,source,clif,remaining',?_,?_,rfl⟩
      · rw [outcome_of_family family]; exact evaluated
      · rw [results]; exact written

/-- Frame components untouched by the arithmetic source body. -/
def SourceFrameEq (s t : Clif.State) : Prop :=
  t.callers = s.callers ∧ t.frame.func = s.frame.func ∧
    t.frame.slots = s.frame.slots ∧ t.frame.term = s.frame.term

private theorem SourceFrameEq.trans {s t u : Clif.State}
    (first : SourceFrameEq s t) (second : SourceFrameEq t u) : SourceFrameEq s u :=
  ⟨second.1.trans first.1,second.2.1.trans first.2.1,
    second.2.2.1.trans first.2.2.1,second.2.2.2.trans first.2.2.2⟩

private theorem mixed_next_of_returned_frame {env : Clif.Env} {cp : Clif.Program}
    {fuel : Nat} {s : Clif.State} {stm : Clif.Stmt} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) (family : Family stm.inst)
    {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp (fuel+1) s = .returned vals mem) :
    ∃ t, Clif.step env cp s = .next t ∧ t.frame.body = rest ∧
      Clif.runLoop env cp fuel t = .returned vals mem ∧ SourceFrameEq s t := by
  have step : Clif.step env cp s =
      Clif.StepResult.ofRes (Clif.evalInst s.frame s.mem stm.inst)
        (fun (vs,cm) => Clif.continueWith s rest stm.results vs cm) := by
    exact step_of_family remaining family
  rw [Clif.runLoop_succ,step] at returned
  cases evaluated : Clif.evalInst s.frame s.mem stm.inst with
  | trap code => simp only [evaluated,Clif.StepResult.ofRes] at returned; cases returned
  | stuck message => simp only [evaluated,Clif.StepResult.ofRes] at returned; cases returned
  | ok value =>
    obtain ⟨vs,cm⟩ := value
    simp only [evaluated,Clif.StepResult.ofRes] at returned
    unfold Clif.continueWith at returned
    cases written : s.frame.regs.setMany stm.results vs with
    | none => simp only [written] at returned; cases returned
    | some regs =>
      simp only [written] at returned
      refine ⟨{s with frame := {s.frame with regs,body := rest},mem := cm},?_,rfl,returned,rfl,rfl,rfl,rfl⟩
      rw [step,evaluated]
      simp only [Clif.StepResult.ofRes,Clif.continueWith,written]

/-- The actual reference run supplies every ordinary arithmetic source step,
including the residual fuel and the exact state at the terminator. -/
theorem actual_mixed_source_execution_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {env : Clif.Env} {cp : Clif.Program} {fuel j : Nat} {s : Clif.State}
    (bound : j ≤ b.body.length) (remaining : s.frame.body = b.body.drop j)
    {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel s = .returned vals mem) :
    ∃ t left, left + (b.body.length-j) = fuel ∧
      Clif.runLoop env cp left t = .returned vals mem ∧ t.frame.body = [] ∧
      SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        (List.range' (blockStart f event.block+j) (b.body.length-j))
        (j,s.frame,s.mem) (b.body.length,t.frame,t.mem) ∧ SourceFrameEq s t := by
  induction fuel generalizing j s with
  | zero => cases returned
  | succ fuel ih =>
    by_cases done : j = b.body.length
    · subst j
      refine ⟨s,fuel+1,by omega,returned,?_,?_,rfl,rfl,rfl,rfl⟩
      · simpa using remaining
      · simp only [Nat.sub_self,List.range'_zero]
        exact .nil _
    · have inside : j < b.body.length := by omega
      let stm := b.body[j]
      have statement : b.body[j]? = some stm := List.getElem?_eq_getElem inside
      have head : s.frame.body = stm :: b.body.drop (j+1) := by
        rw [remaining,List.drop_eq_getElem_cons inside]
      have instFamily := family stm (List.mem_of_getElem? statement)
      obtain ⟨next,stepped,rest,returned',frame⟩ := mixed_next_of_returned_frame head instFamily returned
      obtain ⟨t,left,total,ends,empty,tail,tailFrame⟩ := ih (by omega) rest returned'
      have current := actual_mixed_source_step run events split
        (record := ⟨blockStart f event.block+j,default,default⟩) statement rfl instFamily head stepped
      refine ⟨t,left,by omega,ends,empty,?_,SourceFrameEq.trans frame tailFrame⟩
      have length : b.body.length-j = (b.body.length-(j+1))+1 := by omega
      rw [length,List.range'_succ]
      simpa only [Nat.add_assoc,Nat.add_comm 1 j] using SourceSteps.cons current tail

private theorem return_done_of_runLoop {env : Clif.Env} {cp : Clif.Program}
    {s : Clif.State} {xs : List Nat} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (empty : s.frame.body = []) (callers : s.callers = []) (term : s.frame.term = .ret xs)
    (returned : Clif.runLoop env cp fuel s = .returned vals mem) :
    Clif.stepTerm env cp s (.ret xs) = .done vals mem := by
  cases fuel with
  | zero => cases returned
  | succ fuel =>
    rw [Clif.runLoop_succ,Clif.step_term env cp s empty,term] at returned
    cases step : Clif.stepTerm env cp s (.ret xs) with
    | next t => exact False.elim ((stepTerm_ret callers).1 t step)
    | done vs cm =>
      simp only [step,Clif.Outcome.returned.injEq] at returned
      obtain ⟨rfl,rfl⟩ := returned
      rfl
    | trapped c => simp only [step] at returned; cases returned
    | stuck message => simp only [step] at returned; cases returned

private theorem factor_seg {vb : VBlock} {pre code post : Array MInst}
    (parts : vb.insts = pre ++ code ++ post) : SegAt vb pre.size code.toList := by
  intro k hk
  have bound : k < code.size := by simpa using hk
  rw [parts,Array.append_assoc,Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [Array.getElem?_append_left bound]
  simp [bound]

/-- Actual source execution and the actual emitted arithmetic body/return reach
an ABI-correct return in Stock's returned VCode. Source steps, terminal definedness,
caller/frame transport and segment placement are all derived internally. -/
theorem actual_mixed_return_refines_at {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {s : Clif.State}
    (func : s.frame.func = f) (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (terminal : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx event.block 0 s.frame)
    {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel s = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR)
    {label : Nat} {vb : VBlock} {pre post : Array MInst}
    (placed : result.code.blocks[label]? = some vb)
    (code : vb.insts = pre ++ event.output.code.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++ post) :
    ∀ ρ w, GuardedScanRel f result event.ctx event.block MR event.output.state
      (0,s.frame,s.mem) ρ w →
      RunOkABI f result.code isem MR s.frame.slots ⟨label,pre.size,ρ,w⟩ (.returned vals mem) := by
  obtain ⟨term,body,split,families⟩ := actual_mixed_families run scope blocks family events
  have start : s.frame.body = b.body.drop 0 := by simpa using remaining
  obtain ⟨t,left,total,ends,empty,steps,frame⟩ := actual_mixed_source_execution_frame
    run events split family (j := 0) (by omega) start returned
  have tDefined : SourceDefinedAt f result.ctx event.block b.body.length t.frame := by
    apply ArithmeticBody.arithmetic_steps_defined run scope dominated events split.block
      (env := env) (cp := cp) (s := (0,s.frame,s.mem)) (t := (b.body.length,t.frame,t.mem))
      (j := 0) (n := b.body.length) (by omega) rfl ?_ defined
    simpa only [Nat.add_zero,Nat.sub_zero] using steps
  have tFunc : t.frame.func = f := frame.2.1.trans func
  have tCallers : t.callers = [] := frame.1.trans callers
  have tTerm : t.frame.term = .ret xs := frame.2.2.2.trans (terminal.trans ret)
  have done := return_done_of_runLoop empty tCallers tTerm ends
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have pieces : vb.insts = pre ++ body.code.map (·.mapRegs resolve) ++
      (term.output.emitted.map (·.mapRegs resolve) ++ post) := by
    simp only [code,split.code,Array.map_append,Array.append_assoc,resolve]
  have bodySeg : SegAt vb pre.size (body.code.toList.map (·.mapRegs resolve)) := by
    simpa only [Array.toList_map] using factor_seg pieces
  have termPieces : vb.insts = (pre ++ body.code.map (·.mapRegs resolve)) ++
      term.output.emitted.map (·.mapRegs resolve) ++ post := by
    simpa only [Array.append_assoc] using pieces
  have termSeg : SegAt vb (pre.size+body.code.size)
      (term.output.emitted.toList.map (·.mapRegs resolve)) := by
    simpa only [Array.size_append,Array.size_map,Array.toList_map] using factor_seg termPieces
  have termMember : term ∈ event.output.records := by rw [split.records]; exact List.mem_cons_self
  intro ρ w held
  obtain ⟨ρ',w',executed,postHeld⟩ := stock_lower_select_addsub_omitted_body_fall_refines
    run scope dominated events split.scanned split.retained families refines stable
    (0,s.frame,s.mem) (b.body.length,t.frame,t.mem)
    (by simpa only [sourceBodyIndices,List.reverse_reverse,Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using steps)
    ρ w (by simpa only [split.state] using held)
  obtain ⟨heldFunc,dfg,memory,values⟩ := postHeld
  obtain ⟨step,rs,ps,extra,recorded,emitted,termCode,rest⟩ :=
    stock_lower_return_record_source_run_auto run scope dominated abi events split.block ret
      termMember split.termInst tFunc tCallers done tDefined values refines stable
  have nonempty : 0 < term.output.emitted.size := by rw [termCode]; exact Nat.zero_lt_succ 0
  have room : pre.size + (body.code.toList.map (·.mapRegs resolve)).length < vb.insts.size := by
    have sizes := congrArg Array.size pieces
    simp only [Array.size_append,Array.size_map] at sizes
    simp only [List.length_map,Array.length_toList]
    omega
  have path := seqRun_fall_star (vc := result.code) (sem := isem) placed bodySeg room executed
  have finished := stock_lower_return_record_runOk run scope dominated abi events split.block ret
    termMember split.termInst tFunc tCallers done tDefined values refines stable placed termSeg w' memory
  have combined := RunOkABI.prefix path (by simpa only [List.length_map,Array.length_toList] using finished)
  simpa only [frame.2.2.1] using combined

/-- Compatibility variant retaining existential body placement. -/
theorem actual_mixed_return_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {s : Clif.State}
    (func : s.frame.func = f) (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (terminal : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx event.block 0 s.frame)
    {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel s = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) :
    ∃ label k, ∀ ρ w, GuardedScanRel f result event.ctx event.block MR event.output.state
      (0,s.frame,s.mem) ρ w →
      RunOkABI f result.code isem MR s.frame.slots ⟨label,k,ρ,w⟩ (.returned vals mem) := by
  obtain ⟨label,vb,pre,post,placed,code⟩ := stock_lower_block_scan_code run events
  exact ⟨label,pre.size,actual_mixed_return_refines_at run scope dominated abi blocks family ret
    events func callers remaining terminal defined returned refines stable placed code⟩

/-- Original function entry derives the frame, caller and source-definedness
premises of the actual arithmetic return simulation. -/
theorem actual_mixed_entered_return_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {args : List Clif.Val} {cm0 cm : Clif.Mem} {fr : Clif.Frame}
    (entered : Clif.enterFunc f args cm0 = .ok (fr,cm))
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) :
    ∃ label k, ∀ ρ w, GuardedScanRel f result event.ctx event.block MR event.output.state
      (0,fr,cm) ρ w →
      RunOkABI f result.code isem MR fr.slots ⟨label,k,ρ,w⟩ (.returned vals mem) := by
  obtain ⟨b',regs,entry,types,paramTypes,set,slots,frame⟩ := Opt.enterFunc_ok entered
  have same : b' = b := by
    have found : some b = some b' := by simpa only [Clif.Function.entry?,blocks,List.head?_cons] using entry
    exact Option.some.inj found.symm
  subst b'
  obtain ⟨term,body,split,families⟩ := actual_mixed_families run scope blocks family events
  have bound := (List.getElem?_eq_some_iff.mp split.block).1
  rw [blocks] at bound
  have zero : event.block = 0 := by simpa using bound
  have defined : SourceDefinedAt f result.ctx event.block 0 fr := by
    rw [zero]
    exact source_defined_enterFunc dominated result.ctx entered
  apply actual_mixed_return_refines run scope dominated abi blocks family ret events
    (s := ⟨fr,[],cm⟩) (by rw [frame]) rfl
    (by rw [frame]) (by rw [frame]) defined returned refines stable

private theorem return_inbounds {vc : VCode} {isem : Backend.Proof.Sem}
    {vs : VState CV Arm.ArmState} {us : List (Reg × Reg)} {vals : List CV} {w : Arm.ArmState}
    (ret : VRetFrom vc isem vs us vals w) {block : VBlock}
    (placed : vc.blocks[vs.b]? = some block) : vs.k < block.insts.size := by
  obtain ⟨b,k,ρ,w₁,vb,ops,outs,path,atBlock,instruction,_⟩ := ret
  cases path with
  | refl =>
    have same : block = vb := Option.some.inj (placed.symm.trans atBlock)
    subst vb
    exact (Array.getElem?_eq_some_iff.mp instruction).1
  | step first rest =>
    cases first with
    | step found instruction operands semantics length next =>
      have same : block = _ := Option.some.inj (placed.symm.trans found)
      subst same
      exact (Array.getElem?_eq_some_iff.mp instruction).1

/-- Complete original-entry-to-return simulation of arbitrary single-block
add/sub bodies in the actual Stock VCode. ABI materialization, omitted parameter
values, final aliases, source execution and machine PC placement are derived
internally. The allocation checker may choose the proof-selected initial file. -/
theorem actual_mixed_entry_return_refines_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ, RunOkABI f result.code isem MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals mem) := by
  obtain ⟨event,vb,pre,body,ρ',w',events,zero,placed,pieces,execution,mem',values,same,
    after,bodyCode⟩ := stock_lower_entry_prelude_refines_frame run scope dominated entered driver
      memorySem stable memory arguments
  have code : vb.insts = pre ++ event.output.code.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++ after := by
    rw [pieces,bodyCode,Array.append_assoc]
  have entryFacts := entered
  obtain ⟨b',regs,entry,argTypes,paramTypes,set,frame⟩ := entryFacts
  have sameBlock : b' = b := by
    have found : some b = some b' := by
      simpa only [Clif.Function.entry?,blocks,List.head?_cons] using entry
    exact Option.some.inj found.symm
  subst b'
  have defined : SourceDefinedAt f result.ctx event.block 0 fr := by
    rw [zero]
    exact source_defined_entry_frame dominated result.ctx entered
  have held := stock_lower_entered_values_guarded_frame run scope dominated events entered values
    event.output.state w' mem'
  have finished := actual_mixed_return_refines_at run scope dominated abi blocks family ret events
    (s := ⟨fr,[],cm⟩) (by rw [frame]) rfl (by rw [frame]) (by rw [frame])
    defined returned refines stable placed code ρ' w' held
  have room : pre.size < vb.insts.size := by
    obtain ⟨us,outs,world,cm',reached,_⟩ := finished
    exact return_inbounds reached placed
  have segment : SegAt vb 0 pre.toList := by
    intro k bound
    have inside : k < pre.size := by simpa only [Array.length_toList] using bound
    rw [Nat.zero_add,pieces,Array.getElem?_append_left inside]
    simp [inside]
  have path := seqRun_fall_star (vc := result.code) (sem := isem) placed segment
    (by simpa only [Nat.zero_add,Array.length_toList] using room) execution
  refine ⟨entrySeed event.ctx fr,RunOkABI.prefix path ?_⟩
  simpa only [Nat.zero_add,Array.length_toList] using finished

/-- Executable-entry compatibility variant; retains the original statement. -/
theorem actual_mixed_entry_return_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    {args : List Clif.Val} {cm0 cm : Clif.Mem} {fr : Clif.Frame}
    (entered : Clif.enterFunc f args cm0 = .ok (fr,cm))
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ, RunOkABI f result.code isem MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals mem) := by
  exact actual_mixed_entry_return_refines_frame run scope dominated abi blocks family ret (SourceEntry.of_enterFunc entered) returned refines driver memorySem stable memory arguments


private theorem get_notrap (fr : Clif.Frame) (x : Nat) (c : Clif.TrapCode) :
    fr.get x ≠ .trap c := by
  cases found : fr.regs x <;> simp [Clif.Frame.get,Clif.Res.ofOption,found]

private theorem getAs_notrap (fr : Clif.Frame) (x : Nat) (ty : Clif.Ty) (c : Clif.TrapCode) :
    fr.getAs x ty ≠ .trap c := by
  cases found : fr.get x with
  | trap code => exact False.elim (get_notrap fr x code found)
  | stuck message => simp [Clif.Frame.getAs,found]
  | ok value => cases cast : value.as? ty <;> simp [Clif.Frame.getAs,found,Clif.Res.ofOption,cast]

private theorem getMany_notrap (fr : Clif.Frame) (xs : List Nat) (c : Clif.TrapCode) :
    fr.getMany xs ≠ .trap c := by
  induction xs generalizing c with
  | nil => simp [Clif.Frame.getMany]
  | cons x xs ih =>
    cases found : fr.get x with
    | trap code => exact False.elim (get_notrap fr x code found)
    | stuck message => simp [Clif.Frame.getMany,found]
    | ok value =>
      cases rest : fr.getMany xs with
      | trap code => exact False.elim ((ih code) rest)
      | stuck message => simp [Clif.Frame.getMany,found,rest]
      | ok values => simp [Clif.Frame.getMany,found,rest]

private theorem arithmetic_notrap (fr : Clif.Frame) (cm : Clif.Mem)
    (subtract : Bool) (ty : Clif.Ty) (x y : Nat) (c : Clif.TrapCode) :
    Clif.evalInst fr cm (.binary (if subtract then .isub else .iadd) ty x y) ≠ .trap c := by
  cases subtract <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,Clif.evalInst,Clif.BinaryOp.isShift]
  all_goals
    cases left : fr.getAs x ty with
    | trap code => exact False.elim (getAs_notrap fr x ty code left)
    | stuck message => simp
    | ok a =>
      cases right : fr.getAs y ty with
      | trap code => exact False.elim (getAs_notrap fr y ty code right)
      | stuck message => simp
      | ok b => simp

private theorem family_notrap (fr : Clif.Frame) (cm : Clif.Mem)
    {inst : Clif.Inst} (family : Family inst) (c : Clif.TrapCode) :
    Clif.evalInst fr cm inst ≠ .trap c := by
  rcases family with ⟨subtract,ty,x,y,rfl⟩ | ⟨ty,condition,x,y,rfl⟩
  · exact arithmetic_notrap fr cm subtract ty x y c
  · simp only [Clif.evalInst]
    cases cond : fr.get condition with
    | trap code => exact False.elim (get_notrap fr condition code cond)
    | stuck message => simp
    | ok cv =>
      cases left : fr.getAs x ty with
      | trap code => exact False.elim (getAs_notrap fr x ty code left)
      | stuck message => simp
      | ok a =>
        cases right : fr.getAs y ty with
        | trap code => exact False.elim (getAs_notrap fr y ty code right)
        | stuck message => simp
        | ok b => simp

/-- Pure add/sub source bodies ending in return cannot produce a trap, even
when malformed operands instead make the executable semantics stuck. -/
theorem mixed_source_notrap {env : Clif.Env} {cp : Clif.Program} (fuel : Nat)
    (s : Clif.State) (callers : s.callers = [])
    (family : ∀ stm ∈ s.frame.body, Family stm.inst)
    {xs : List Nat} (ret : s.frame.term = .ret xs) (code : Clif.TrapCode) :
    Clif.runLoop env cp fuel s ≠ .trapped code := by
  induction fuel generalizing s with
  | zero => simp
  | succ fuel ih =>
    rw [Clif.runLoop_succ]
    cases remaining : s.frame.body with
    | nil =>
      rw [Clif.step_term env cp s remaining,ret,Clif.stepTerm]
      cases values : s.frame.getMany xs with
      | trap c => exact False.elim (getMany_notrap s.frame xs c values)
      | stuck message => simp
      | ok vals =>
        simp only [Clif.StepResult.ofRes]
        by_cases typed : vals.map (·.ty) = Clif.AbiParam.tys s.frame.func.sig.returns <;>
          simp [Clif.returnValues,Clif.checkTys,Clif.Res.check,callers,Clif.StepResult.ofRes,typed]
    | cons stm rest =>
      have instFamily := family stm (by simp [remaining])
      rw [Clif.step_inst env cp s stm rest remaining
        (by
          intro fn args h
          rcases instFamily with ⟨subtract,ty,x,y,shape⟩ | ⟨ty,c,x,y,shape⟩
          all_goals rw [shape] at h; cases h)
        (by
          intro sig callee args h
          rcases instFamily with ⟨subtract,ty,x,y,shape⟩ | ⟨ty,c,x,y,shape⟩
          all_goals rw [shape] at h; cases h)]
      cases evaluated : Clif.evalInst s.frame s.mem stm.inst with
      | trap c => exact False.elim (family_notrap s.frame s.mem instFamily c evaluated)
      | stuck message => simp
      | ok pair =>
        rcases pair with ⟨values,cm⟩
        simp only [Clif.StepResult.ofRes,Clif.continueWith]
        cases written : s.frame.regs.setMany stm.results values with
        | none => simp
        | some regs =>
          simp only
          apply ih {s with frame := {s.frame with regs,body := rest},mem := cm} callers ?_ ret
          intro other member
          apply family other
          rw [remaining]
          exact List.mem_cons_of_mem _ member


end Backend.Stock.Proof.MixedBody
