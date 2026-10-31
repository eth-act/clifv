import FV.Backend.Proof.StockMemoryNotrap
import FV.Backend.Proof.StockMemoryCfgClass
import FV.Backend.Proof.LowerLemmas

namespace Backend.Stock.Proof.OrdinaryCfg
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem getMany_notrap (fr : Clif.Frame) (xs : List Nat) (c : Clif.TrapCode) :
    fr.getMany xs ≠ .trap c := by
  induction xs generalizing c with
  | nil => simp [Clif.Frame.getMany]
  | cons x xs ih =>
    cases found : fr.get x with
    | trap code => exact False.elim (fr.get_ne_trap x code found)
    | stuck message => simp [Clif.Frame.getMany,found]
    | ok value =>
      cases rest : fr.getMany xs with
      | trap code => exact False.elim ((ih code) rest)
      | stuck message => simp [Clif.Frame.getMany,found,rest]
      | ok values => simp [Clif.Frame.getMany,found,rest]

private theorem enterBlock_notrap (fr : Clif.Frame) (bc : Clif.BlockCall) (c : Clif.TrapCode) :
    Clif.enterBlock fr bc ≠ .trap c := by
  intro trapped
  unfold Clif.enterBlock at trapped
  rcases Clif.res_bind_eq_trap trapped with bad | ⟨block,_,bad⟩
  · exact Clif.Res.ofOption_ne_trap _ _ c bad
  · rcases Clif.res_bind_eq_trap bad with bad | ⟨args,_,bad⟩
    · exact getMany_notrap fr bc.args c bad
    · rcases Clif.res_bind_eq_trap bad with bad | ⟨unit,_,bad⟩
      · exact Clif.Res.check_ne_trap _ _ c bad
      · rcases Clif.res_bind_eq_trap bad with bad | ⟨regs,_,bad⟩
        · exact Clif.Res.ofOption_ne_trap _ _ c bad
        · cases bad

/-- Ordinary nontrapping bodies remain nontrapping across original jumps and returns. -/
theorem ordinary_jump_return_notrap {env : Clif.Env} {cp : Clif.Program} {f : Clif.Function}
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,OrdinaryBody.OrdinaryInst stm.inst ∧
      ∀ fr cm c,Clif.evalInst fr cm stm.inst ≠ .trap c)
    (terms : ∀ b ∈ f.blocks,(∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs))
    (fuel : Nat) (s : Clif.State) (func : s.frame.func = f) (callers : s.callers = [])
    (body : ∀ stm ∈ s.frame.body,OrdinaryBody.OrdinaryInst stm.inst ∧
      ∀ fr cm c,Clif.evalInst fr cm stm.inst ≠ .trap c)
    (term : (∃ bc,s.frame.term = .jump bc) ∨ (∃ xs,s.frame.term = .ret xs))
    (code : Clif.TrapCode) : Clif.runLoop env cp fuel s ≠ .trapped code := by
  induction fuel generalizing s with
  | zero => simp
  | succ fuel ih =>
    cases remaining : s.frame.body with
    | nil =>
      rcases term with ⟨bc,jump⟩ | ⟨xs,ret⟩
      · rw [Clif.runLoop_succ,Clif.step_term env cp s remaining,jump,Clif.stepTerm]
        cases entered : Clif.enterBlock s.frame bc with
        | trap c => exact False.elim (enterBlock_notrap s.frame bc c entered)
        | stuck message => simp only [Clif.StepResult.ofRes]; simp
        | ok fr =>
          simp only [Clif.StepResult.ofRes]
          obtain ⟨block,args,regs,found,read,types,set,frame⟩ := enterBlock_spec entered
          have member : block ∈ f.blocks := by
            apply List.mem_of_find?_eq_some
            simpa only [func,Clif.Function.block?] using found
          apply ih {s with frame := fr} (by rw [frame]; exact func) callers
          · intro stm present
            apply family block member stm
            simpa only [frame] using present
          · simpa only [frame] using terms block member
      · exact OrdinaryBody.ordinary_source_notrap (fuel+1) s callers body ret code
    | cons stm rest =>
      have here := body stm (by simp [remaining])
      rw [Clif.runLoop_succ,Clif.step_inst env cp s stm rest remaining here.1.1 here.1.2]
      cases evaluated : Clif.evalInst s.frame s.mem stm.inst with
      | trap c => exact False.elim (here.2 s.frame s.mem c evaluated)
      | stuck message => simp
      | ok pair =>
        rcases pair with ⟨values,cm⟩
        simp only [Clif.StepResult.ofRes,Clif.continueWith]
        cases written : s.frame.regs.setMany stm.results values with
        | none => simp
        | some regs =>
          simp only
          apply ih {s with frame := {s.frame with regs,body := rest},mem := cm} func callers ?_ term
          intro other present
          apply body other
          rw [remaining]
          exact List.mem_cons_of_mem _ present

end Backend.Stock.Proof.OrdinaryCfg

namespace Backend.Stock.MemoryCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The captured source class cannot produce a trap, including after its jump. -/
theorem TwoBlockClass.source_notrap {f : Clif.Function} (family : TwoBlockClass f)
    {args : List Clif.Val} {fr : Clif.Frame} (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {cm : Clif.Mem} (fuel : Nat) (code : Clif.TrapCode) :
    Clif.runLoop env cp fuel ⟨fr,[],cm⟩ ≠ .trapped code := by
  obtain ⟨entry,target,x,z,flags,blocks,entryBody,targetBody,jump,ret,parameter,notrap⟩ := family.shape
  have nop (stm : Clif.Stmt) (isNop : stm.inst = .nop) : OrdinaryBody.OrdinaryInst stm.inst ∧
      ∀ fr cm c,Clif.evalInst fr cm stm.inst ≠ .trap c := by
    constructor
    · simp [OrdinaryBody.OrdinaryInst,isNop]
    · intro fr cm c trapped
      rw [isNop] at trapped
      cases trapped
  have all : ∀ b ∈ f.blocks,∀ stm ∈ b.body,OrdinaryBody.OrdinaryInst stm.inst ∧
      ∀ fr cm c,Clif.evalInst fr cm stm.inst ≠ .trap c := by
    intro b present stm member
    simp [blocks] at present
    rcases present with rfl | rfl
    · have equal : stm = ⟨[],.nop⟩ := by simpa only [entryBody,List.mem_singleton] using member
      subst stm
      exact nop _ rfl
    · have cases : stm = ⟨[],.nop⟩ ∨ stm = ⟨[z],.load .load .i32 flags x 0⟩ := by
        simpa [targetBody] using member
      rcases cases with rfl | rfl
      · exact nop _ rfl
      · refine ⟨?_,?_⟩
        · simp [OrdinaryBody.OrdinaryInst]
        · intro fr cm c
          exact Clif.evalInst_notrap rfl notrap c
  have terms : ∀ b ∈ f.blocks,(∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) := by
    intro b present
    simp [blocks] at present
    rcases present with rfl | rfl
    · exact .inl ⟨_,jump⟩
    · exact .inr ⟨_,ret⟩
  obtain ⟨original,regs,first,argTypes,paramTypes,set,frame⟩ := entered
  have source : f.blocks[0]? = some original := by
    simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using first
  have member : original ∈ f.blocks := List.mem_of_getElem? source
  have body : ∀ stm ∈ fr.body,OrdinaryBody.OrdinaryInst stm.inst ∧
      ∀ fr cm c,Clif.evalInst fr cm stm.inst ≠ .trap c := by
    intro stm present
    apply all original member stm
    rw [frame] at present
    exact present
  exact OrdinaryCfg.ordinary_jump_return_notrap all terms fuel ⟨fr,[],cm⟩
    (by rw [frame]) rfl body (by rw [frame]; exact terms original member) code

end Backend.Stock.MemoryCfg
