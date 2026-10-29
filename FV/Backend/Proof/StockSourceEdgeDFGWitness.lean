module

public import FV.Backend.Proof.StockSourceEdgeDFG
public import FV.Backend.Proof.StockMaskBlockWitness

@[expose] public section

namespace Backend.Stock.Proof.SourceSuccessorWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private abbrev function := QuietBlockWitness.function
private def zero : Clif.Val := ⟨.i64,0⟩
private def one : Clif.Val := ⟨.i64,1⟩
private def initial : Clif.Frame := {
  func := function,regs := (Clif.Regs.empty.set 1 zero).set 6 one,slots := [],
  body := function.blocks[0]!.body,term := function.blocks[0]!.term }
private def middle : Clif.Frame := {initial with regs := initial.regs.set 100 zero,body := [⟨[],.nop⟩]}
private def before : Clif.Frame := {middle with body := []}
private def after : Clif.Frame := {before with
  regs := (before.regs.set 2 zero).set 3 one
  body := function.blocks[1]!.body
  term := function.blocks[1]!.term}

/-- Genuine entry, two actual source statements and nonempty successor binding
inhabit source consistency in the real predecessor and successor scan contexts. -/
theorem actual_source_successor_dfg_witness : ∃ result first second,
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    first ∈ result.blockScans.toList ∧ first.block = 0 ∧
    second ∈ result.blockScans.toList ∧ second.block = 1 ∧
    Clif.enterFunc function [zero,one] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) ∧
    Clif.step Clif.Env.empty {funcs := []} ⟨initial,[],Clif.Mem.empty⟩ = .next ⟨middle,[],Clif.Mem.empty⟩ ∧
    Clif.step Clif.Env.empty {funcs := []} ⟨middle,[],Clif.Mem.empty⟩ = .next ⟨before,[],Clif.Mem.empty⟩ ∧
    Clif.enterBlock before ⟨10,[1,6]⟩ = .ok after ∧
    DFGCons first.ctx (restrict before (availOf function (availIn function result.ctx) 0 2)) ∧
    DFGCons second.ctx (restrict after (availOf function (availIn function result.ctx) 1 0)) := by
  obtain ⟨result,second,oldTerm,oldBody,run,scope,dominated,secondEvents,secondAt,rest⟩ :=
    MaskBlockWitness.actual_family_records_witness
  obtain ⟨ranges,params,input,data,core,raw,vb,sizes,build,coreRun,assembled,firstEvents,placed,code⟩ :=
    stock_lower_entry_assembly run scope
  have firstAt : core.scan.block = 0 := (stock_lowerBlockCore_scanOrigin coreRun).2.2.1
  obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope firstEvents
  have same : b = function.blocks[0]! := Option.some.inj (split.block.symm.trans (by rw [firstAt]; rfl))
  subst b
  have entered : Clif.enterFunc function [zero,one] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) := rfl
  have entryDfg := stock_lower_entered_restrict_dfg run dominated firstEvents entered
    (availOf function (availIn function result.ctx) 0 0)
  have firstStep := LocalBody.actual_local_source_step run firstEvents split
    (env := Clif.Env.empty) (cp := {funcs := []})
    (record := ⟨0,default,default⟩) (j := 0) (stm := ⟨[100],.iconst .i64 0⟩)
    rfl (by rw [firstAt]; rfl) rfl
    (s := ⟨initial,[],Clif.Mem.empty⟩) (t := ⟨middle,[],Clif.Mem.empty⟩) rfl rfl
  have middleDfg := stock_lower_source_step_dfg run scope dominated firstEvents
    (record := ⟨0,default,default⟩) (bi := 0) (b := function.blocks[0]!) rfl
    (j := 0) (stm := ⟨[100],.iconst .i64 0⟩) rfl rfl rfl entryDfg firstStep.2.2
  have secondStep := LocalBody.actual_local_source_step run firstEvents split
    (env := Clif.Env.empty) (cp := {funcs := []})
    (record := ⟨1,default,default⟩) (j := 1) (stm := ⟨[],.nop⟩)
    rfl (by rw [firstAt]; rfl) True.intro
    (s := ⟨middle,[],Clif.Mem.empty⟩) (t := ⟨before,[],Clif.Mem.empty⟩) rfl rfl
  have beforeDfg := stock_lower_source_step_dfg run scope dominated firstEvents
    (record := ⟨1,default,default⟩) (bi := 0) (b := function.blocks[0]!) rfl
    (j := 1) (stm := ⟨[],.nop⟩) rfl rfl rfl middleDfg secondStep.2.2
  have transferred := stock_lower_source_enterBlock_dfg run scope dominated firstEvents secondEvents
    (bi := 0) (tl := 1) (b := function.blocks[0]!) (target := function.blocks[1]!)
    (bc := ⟨10,[1,6]⟩) rfl rfl (by decide +kernel) rfl
    (fr := before) (fr' := after) rfl beforeDfg rfl
  exact ⟨result,core.scan,second,run,scope,dominated,firstEvents,firstAt,secondEvents,secondAt,
    entered,rfl,rfl,rfl,beforeDfg,transferred⟩

end Backend.Stock.Proof.SourceSuccessorWitness
