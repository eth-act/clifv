import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.StockReturnSourceRuns
import FV.Backend.Proof.StockBodyScanOrigin

namespace Backend.Stock.Proof.EmptyBodySplitWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock
private def function : Clif.Function := {
  name := "stock_empty_body_split"
  sig := {params := [],returns := [],callConv := some .systemV}
  blocks := [{id := 0,params := [],body := [],term := .ret []}] }
private def frame : Clif.Frame := {
  func := function,regs := fun _ => none,slots := [],body := [],term := .ret [] }
private def Observed : Prop := (Stock.lower function).toOption.map (fun result =>
  result.blockScans.toList.any (fun event => event.block == 0 && decide (event.output.code = #[.rets []]))) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed; decide +kernel
end Kernel
private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)

/-- A complete zero-statement function inhabits the split's empty-body boundary.
The actual remaining scan code executes a machine return, and the original
source step returns the same empty value list. -/
theorem stock_empty_body_split_witness :
    ∃ (result : Result) (event : BlockScanEvent) (b : Clif.Block) (term : ScanRecord) (body : BlockScan),
      Stock.lower function = .ok result ∧ LowerScope function ∧ event ∈ result.blockScans.toList ∧
      SourceBodySplit function event b term body ∧ event.block = 0 ∧ b.body = [] ∧
      term.inst = 0 ∧ body.records = [] ∧ body.code = #[] ∧ body.state = term.output.state ∧
      event.output.code = #[.rets []] ∧ term.output.emitted = #[.rets []] ∧
      Clif.step Clif.Env.empty {funcs := []} ⟨frame,[],Clif.Mem.empty⟩ = .done [] Clif.Mem.empty ∧
      ∀ ρ world, seqRun ispec (event.output.code.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
          some (.stop 0 (.rets []) #[] ρ world [] world .ret) := by
  have actual := observed
  unfold Observed at actual
  cases run : Stock.lower function with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,List.any_eq_true,
      Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at actual
    obtain ⟨event,events,blockIndex,code⟩ := actual
    obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope events
    have blockEq : b = function.blocks[0]! := by
      have found := split.block
      rw [blockIndex] at found
      exact Option.some.inj found.symm
    have empty : b.body = [] := by rw [blockEq]; rfl
    have termIndex : term.inst = 0 := by rw [split.termInst,split.termIndex,blockIndex,empty]; rfl
    have records : body.records = [] := by
      have order := split.scanned.order
      simp only [sourceBodyIndices,empty,List.length_nil,List.range_zero,List.map_nil,List.reverse_nil] at order
      exact List.map_eq_nil_iff.mp order
    have bodyCode : body.code = #[] := by
      have exactCode := split.scanned.code
      rw [records] at exactCode
      exact Array.toList_inj.mp exactCode
    have state : body.state = term.output.state := by
      have chain := split.scanned.chain
      simpa only [records,StateChain] using chain
    have termCode : term.output.emitted = #[.rets []] := by
      have joined := split.code
      rw [code,bodyCode,Array.empty_append] at joined
      exact joined.symm
    refine ⟨result,event,b,term,body,rfl,scope,events,split,blockIndex,empty,termIndex,records,bodyCode,state,code,termCode,rfl,?_⟩
    intro ρ world
    rw [code]
    rfl

private theorem emptyDominated : Dominated function := by
  constructor
  · change ([] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b found
    cases bi with
    | zero =>
      simp [function] at found
      subst b
      constructor
      · intro j stm statement; simp at statement
      · intro x member
        change x ∈ ([] : List Nat) at member
        cases member
    | succ bi => simp [function] at found
  · intro ctx ranges st build tl x incoming notLocal y member
    have bound := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x incoming
    have length : function.blocks.length = 1 := rfl
    omega

/-- The new source/ABI/helper semantics include the zero-operand return case
of an actual complete original driver and a real successful source activation. -/
theorem stock_empty_return_helper_source_witness :
    ∃ (result : Result) (event : BlockScanEvent) (st next : State),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      event ∈ result.blockScans.toList ∧ SourceDefinedAt function result.ctx event.block 0 frame ∧
      Clif.enterFunc function [] Clif.Mem.empty = .ok (frame,Clif.Mem.empty) ∧
      ApplyInternal program (Stock.sem event.ctx) {} 999 25 294 [.values []]
        (st,#[]) (.regsVec []) (next,#[rule_prelude_lower_1493.id]) ∧
      ∀ ρ world,∃ ops world',seqRun ispec [.rets []] ρ world =
          some (.stop 0 (.rets []) ops ρ world [] world' .ret) ∧ AllHold [] (vuses ops ρ) := by
  obtain ⟨result,event,b,term,body,run,scope,events,split,blockIndex,empty,termIndex,records,bodyCode,
    bodyState,code,termCode,sourceDone,actualExecution⟩ := stock_empty_body_split_witness
  let st := scanState term.input term.inst
  let next : State := {st with base := st.base.emit (.rets [])}
  have inv := (stock_lower_record_context run scope events).1
  have pinSelection : returnPins event.ctx.func 0 = some [] := by rw [inv.func]; rfl
  have helper : ApplyInternal program (Stock.sem event.ctx) {} 999 25 294 [.values []]
      (st,#[]) (.regsVec []) (next,#[rule_prelude_lower_1493.id]) :=
    stock_lower_return_call data_program event.ctx rfl [] [] [] st #[] 940 (by simp) rfl pinSelection
  have entered : Clif.enterFunc function [] Clif.Mem.empty = .ok (frame,Clif.Mem.empty) := rfl
  have defined : SourceDefinedAt function result.ctx event.block 0 frame := by
    rw [blockIndex]; exact source_defined_enterFunc emptyDominated result.ctx entered
  have sourceReturn : Clif.stepTerm Clif.Env.empty {funcs := []} ⟨frame,[],Clif.Mem.empty⟩ (.ret []) =
      .done [] Clif.Mem.empty := rfl
  have block : function.blocks[event.block]? = some b := split.block
  have sourceRet : b.term = .ret [] := by
    have found := block
    rw [blockIndex] at found
    have equal : b = function.blocks[0]! := Option.some.inj found.symm
    rw [equal]; rfl
  refine ⟨result,event,st,next,run,scope,emptyDominated,events,defined,entered,helper,?_⟩
  intro ρ world
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ world _ h => ⟨world,h,SameWorld.refl _ _⟩
  have stable : MRStable (fun _ => True) (fun _ cm _ => cm = Clif.Mem.empty) := by intro _ _ _ _ _ h; exact h
  obtain ⟨rs,ps,extra,mapped,pinned,count,read,state,output,execution⟩ := stock_lower_return_source_run
    run scope emptyDominated rfl events block sourceRet rfl rfl sourceReturn
    (by simpa only [empty,List.length_nil] using defined) (by decide : 60 ≤ 999) helper
    (ρ := ρ) (by intro x member; cases member) self stable
  have sameRs : rs = [] := Option.some.inj mapped.symm
  subst rs
  have samePs : ps = [] := Option.some.inj pinned.symm
  subst ps
  have sameExtra : extra = [] := by
    change Clif.Res.ok [] = .ok extra at read
    exact Clif.Res.ok.inj read.symm
  subst extra
  obtain ⟨ops,world',executed,values,memory⟩ := execution world rfl
  exact ⟨ops,world',executed,values⟩
end Backend.Stock.Proof.EmptyBodySplitWitness
