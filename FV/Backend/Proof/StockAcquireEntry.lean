import FV.Backend.Proof.StockAcquireSourceOutcome
import FV.E2E.Statement
import FV.Clif.MemTrap

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- Every original pointer and memory instantiate the unchanged source entry. -/
theorem original_source_entry (pointer : BitVec 64) (memory : Clif.Mem) :
    ClifEntry function [⟨.i64,pointer⟩] ⟨entry pointer,[],memory⟩ := by
  refine ⟨rfl,rfl,rfl,⟨function.blocks[0]!,rfl,rfl,rfl,rfl,?_⟩,rfl⟩
  rfl

/-- A source trap identifies the real initial atomic memory access.
No heap acceptance guard is added. -/
theorem first_source_memory_trap (env : Clif.Env) (program : Clif.Program)
    (pointer : BitVec 64) (memory : Clif.Mem) (fuel : Nat) (code : Clif.TrapCode)
    (trapped : Clif.runLoop env program fuel ⟨entry pointer,[],memory⟩ = .trapped code) :
    Clif.MemTrapAt env program ⟨entry pointer,[],memory⟩ code
      (Clif.effAddr ⟨.i64,pointer⟩ 0) 1 := by
  obtain ⟨positive,loadTrap⟩ := (source_first_trap env program pointer memory fuel code).mp trapped
  have one := (source_first_trap env program pointer memory 1 code).mpr ⟨by decide,loadTrap⟩
  have first : Clif.step env program ⟨entry pointer,[],memory⟩ = .trapped code := by
    rw [Clif.runLoop_succ] at one
    cases observed : Clif.step env program ⟨entry pointer,[],memory⟩ with
    | next next => simp only [observed,Clif.runLoop_zero] at one; cases one
    | done values mem => simp only [observed] at one; cases one
    | trapped actual => simp only [observed,Clif.Outcome.trapped.injEq] at one; cases one; rfl
    | stuck message => simp only [observed] at one; cases one
  refine ⟨first,(Clif.Mem.load_trap loadTrap).1,?_⟩
  refine ⟨⟨[0],.atomicLoad .i8 {} 1⟩,[⟨[2],.extend .uextend .i64 0⟩],rfl,?_⟩
  exact .atomicLoad rfl

end Backend.Stock.Proof.Acquire810
