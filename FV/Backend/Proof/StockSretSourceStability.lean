import FV.Backend.Proof.StockMemorySourceExecution
import FV.Backend.Proof.StockSourceEntry
import FV.Backend.Proof.SretStableX
import FV.Backend.Proof.LowerShapeOkFacts
import FV.Backend.Proof.LowerLoopCtx
import FV.Backend.Proof.LowerCertBase
import FV.Backend.Proof.LowerTotal

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

theorem sret_entry_parameter {f : Clif.Function} {x : Nat} (member : x ∈ sretRet f) :
    ∃ entry : Clif.Block, f.blocks[0]? = some entry ∧ x ∈ entry.params.map (·.1) := by
  unfold sretRet at member
  split at member
  · cases head : f.blocks.head? with
    | none => simp only [head,List.not_mem_nil] at member
    | some entry =>
      cases index : f.sig.params.findIdx? (·.purpose == .sret) with
      | none => simp only [head,index,List.not_mem_nil] at member
      | some i =>
        rw [head,index] at member
        cases param : entry.params[i]? with
        | none => simp [param] at member
        | some pair =>
          simp only [param,Option.map_some,Option.toList_some,List.mem_singleton] at member
          subst x
          exact ⟨entry,by simpa only [List.head?_eq_getElem?] using head,
            List.mem_map.mpr ⟨pair,List.mem_of_getElem? param,rfl⟩⟩
  · cases member

private theorem entry_parameter_not_target {f : Clif.Function} (scope : LowerScope f)
    (dominated : Dominated f) {entry : Clif.Block} (atEntry : f.blocks[0]? = some entry)
    {x : Nat} (parameter : x ∈ entry.params.map (·.1))
    {block target : Clif.Block} (blockMember : block ∈ f.blocks) {id : Nat}
    (successor : id ∈ succIds block.term) (found : f.block? id = some target)
    (targetParameter : x ∈ target.params.map (·.1)) : False := by
  have targetMember : target ∈ f.blocks := List.mem_of_find?_eq_some found
  obtain ⟨j,bound,equal⟩ := List.getElem_of_mem targetMember
  have atTarget : f.blocks[j]? = some target := by simpa only [equal] using List.getElem?_eq_getElem bound
  have same : 0 = j := flatMap_nodup_idx dominated.ssa atEntry atTarget
    (List.mem_append_left _ parameter) (List.mem_append_left _ targetParameter)
  subst j
  have head : f.blocks.head? = some target := by simpa only [List.head?_eq_getElem?] using atTarget
  have selected : (target.id == id) = true := List.find?_some (p := fun b : Clif.Block => b.id == id) (a := target) found
  have index : blockIdx? f id = some 0 := by
    cases blocks : f.blocks with
    | nil => simp [blocks] at head
    | cons first rest =>
      have firstEqual : first = target := by simpa only [blocks,List.head?_cons,Option.some.injEq] using head
      subst first
      simp [blockIdx?,blocks,List.findIdx?_cons,selected]
  exact scope.noEntryPred block blockMember id successor index

/-- The original scope and SSA conditions derive sret stability, including handler edges. -/
theorem sret_stable_of_original_scope {f : Clif.Function} (scope : LowerScope f)
    (dominated : Dominated f) : SretStableX f := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · intro x member
    obtain ⟨entry,atEntry,parameter⟩ := sret_entry_parameter member
    simpa only [Clif.Function.freshValue,maxVOf] using
      maxV_bound f x (mem_valueDefs_par atEntry parameter)
  · intro x member entry head
    have atEntry : f.blocks[0]? = some entry := by simpa only [List.head?_eq_getElem?] using head
    exact (List.nodup_append.mp (block_nodup dominated.ssa atEntry)).1
  · intro x member block blockMember stmt stmtMember result
    obtain ⟨entry,atEntry,parameter⟩ := sret_entry_parameter member
    exact param_not_result dominated.ssa (List.mem_of_getElem? atEntry) blockMember parameter
      (List.mem_flatMap.mpr ⟨stmt,stmtMember,result⟩)
  · intro x member block blockMember id targetMember target found parameter
    obtain ⟨entry,atEntry,entryParameter⟩ := sret_entry_parameter member
    have successor : id ∈ succIds block.term := by
      cases term : block.term <;> simp_all [runTargets,succIds,Clif.ExnTable.dests]
    exact entry_parameter_not_target scope dominated atEntry entryParameter blockMember successor found parameter
  · intro x member block blockMember id targetMember target found parameter
    obtain ⟨entry,atEntry,entryParameter⟩ := sret_entry_parameter member
    have successor : id ∈ succIds block.term := by
      cases term : block.term <;> simp_all [exnTargets,succIds,Clif.ExnTable.dests]
    exact entry_parameter_not_target scope dominated atEntry entryParameter blockMember successor found parameter


theorem sret_stableB_of_stable {f : Clif.Function} (stable : SretStable f) : sretStableB f = true := by
  simp only [sretStableB,List.all_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  intro x member
  refine ⟨⟨stable.fresh x member,?_⟩,?_⟩
  · cases head : f.blocks.head? with
    | none => simp [head]
    | some entry => simpa [head] using stable.entry x member entry head
  · intro block blockMember
    refine ⟨?_,?_⟩
    · intro stmt stmtMember
      simpa using stable.results x member block blockMember stmt stmtMember
    · intro id targetMember
      cases found : f.block? id with
      | none => simp [found]
      | some target => simpa [found] using stable.targets x member block blockMember id targetMember target found

theorem sret_stableXB_of_stable {f : Clif.Function} (stable : SretStableX f) : sretStableXB f = true := by
  simp only [sretStableXB,Bool.and_eq_true,List.all_eq_true]
  refine ⟨sret_stableB_of_stable stable.base,?_⟩
  intro x member block blockMember id targetMember
  cases found : f.block? id with
  | none => simp [found]
  | some target => simpa [found] using stable.exn x member block blockMember id targetMember target found

theorem sret_stableXB_of_original_scope {f : Clif.Function} (scope : LowerScope f)
    (dominated : Dominated f) : sretStableXB f = true :=
  sret_stableXB_of_stable (sret_stable_of_original_scope scope dominated)



end Backend.Stock.Proof
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

theorem ordinary_cfg_sret_step {env : Clif.Env} {cp : Clif.Program} {f : Clif.Function}
    (stable : SretStable f)
    (family : ∀ block ∈ f.blocks,∀ stmt ∈ block.body,OrdinaryBody.OrdinaryInst stmt.inst)
    (terms : ∀ block ∈ f.blocks,(∃ dest,block.term = .jump dest) ∨ (∃ xs,block.term = .ret xs))
    {regs : Clif.Regs} {s t : Clif.State} (invariant : StOk f regs s)
    (step : Clif.step env cp s = .next t) : StOk f regs t := by
  obtain ⟨callers,func,values,block,member,position⟩ := invariant
  have invariant : StOk f regs s := ⟨callers,func,values,block,member,position⟩
  have position : s.frame.term = block.term ∧ ∀ stmt ∈ s.frame.body,stmt ∈ block.body := by
    rcases position with position | ⟨empty,et,dest,tryCall,normal,jump⟩
    · exact position
    · rcases terms block member with ⟨dest',term⟩ | ⟨xs,term⟩ <;>
        rcases tryCall with ⟨fn,args,tryCall⟩ | ⟨callee,args,tryCall⟩ <;> rw [term] at tryCall <;> cases tryCall
  cases remaining : s.frame.body with
  | cons stmt rest =>
    have present : stmt ∈ block.body := position.2 stmt (by simp [remaining])
    have ordinary := family block member stmt present
    rw [Clif.step_inst env cp s stmt rest remaining ordinary.1 ordinary.2] at step
    cases evaluated : Clif.evalInst s.frame s.mem stmt.inst with
    | trap code => simp [evaluated,Clif.StepResult.ofRes] at step
    | stuck message => simp [evaluated,Clif.StepResult.ofRes] at step
    | ok pair =>
      obtain ⟨vals,mem⟩ := pair
      simp only [evaluated,Clif.StepResult.ofRes,Clif.continueWith] at step
      cases written : s.frame.regs.setMany stmt.results vals with
      | none => simp [written] at step
      | some nextRegs =>
        simp only [written] at step
        cases step
        refine ⟨callers,func,?_,block,member,.inl ⟨position.1,?_⟩⟩
        · intro x implicit
          exact (setMany_other written (stable.results x implicit block member stmt present)).trans (values x implicit)
        · intro stmt' present'
          exact position.2 stmt' (by rw [remaining]; exact List.mem_cons_of_mem _ present')
  | nil =>
    rw [Clif.step_term env cp s remaining,position.1] at step
    rcases terms block member with ⟨dest,jump⟩ | ⟨xs,ret⟩
    · rw [jump] at step
      obtain ⟨j,dest',fr,edge,present,entered,equal⟩ := stepTerm_branch (by simp [dests]) step
      subst t
      have target : dest'.block ∈ runTargets block.term := by
        rw [jump]
        exact runTargets_of_dests (List.mem_of_getElem? present)
      exact stOk_enter stable invariant member target entered
    · rw [ret] at step
      exact False.elim ((stepTerm_ret callers).1 t step)

theorem ordinary_cfg_sret_reach {env : Clif.Env} {cp : Clif.Program} {f : Clif.Function}
    (stable : SretStable f)
    (family : ∀ block ∈ f.blocks,∀ stmt ∈ block.body,OrdinaryBody.OrdinaryInst stmt.inst)
    (terms : ∀ block ∈ f.blocks,(∃ dest,block.term = .jump dest) ∨ (∃ xs,block.term = .ret xs))
    {regs : Clif.Regs} {s t : Clif.State} (invariant : StOk f regs s)
    (path : Reach env cp s t) : StOk f regs t := by
  induction path with
  | refl => exact invariant
  | step step _ ih => exact ih (ordinary_cfg_sret_step stable family terms invariant step)

/-- Original source entry and an actual path identify the implicit pointer without a caller certificate. -/
theorem ordinary_cfg_sret_argument {f : Clif.Function} (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ block ∈ f.blocks,∀ stmt ∈ block.body,OrdinaryBody.OrdinaryInst stmt.inst)
    (terms : ∀ block ∈ f.blocks,(∃ dest,block.term = .jump dest) ∨ (∃ xs,block.term = .ret xs))
    {args : List Clif.Val} {fr : Clif.Frame} (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {cm : Clif.Mem} {terminal : Clif.State}
    (path : Reach env cp ⟨fr,[],cm⟩ terminal) :
    terminal.frame.getMany (sretRet f) = .ok (sretArg f args) := by
  have stable := (sret_stable_of_original_scope scope dominated).base
  obtain ⟨entry,regs,head,argTypes,paramTypes,set,frame⟩ := entered
  have atEntry : f.blocks[0]? = some entry := by
    simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using head
  have initial : StOk f fr.regs ⟨fr,[],cm⟩ := by
    refine ⟨rfl,?_,fun _ _ => rfl,entry,List.mem_of_getElem? atEntry,.inl ⟨?_,?_⟩⟩
    · exact congrArg Clif.Frame.func frame
    · exact congrArg Clif.Frame.term frame
    · intro stmt present
      rw [congrArg Clif.Frame.body frame] at present
      exact present
  have final := ordinary_cfg_sret_reach stable family terms initial path
  rw [getMany_congr final.regs]
  exact getMany_sretRet_entry stable atEntry (by rw [congrArg Clif.Frame.regs frame]; exact set) paramTypes

end Backend.Stock.Proof

