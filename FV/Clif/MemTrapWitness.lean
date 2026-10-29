module

public import FV.Clif.MemTrap
public import FV.Clif.Parse
public meta import FV.Clif.Run
public meta import FV.Clif.Syntax
public meta import FV.Clif.Mem

@[expose] public section

/-!
# Witness: an `atomic_rmw` on the null page traps `heap_oob` (A3, #412, F2)

`Clif.Mem.next` starts at `0x10000`, so no allocation covers address 0: the `atomic_rmw` of
`%f` at address 0 traps with its flags' (default) code `heap_oob`. `MemTrapAt` holds at the
state before it (`f_memTrapAt`), the run traps (`f_run`), and the trap is the one
`memTrapAt_of_trapped` describes.
-/

namespace Clif.MemTrapWitness

def src : String := "function %f() -> i64 system_v {
block0:
    v0 = iconst.i64 0
    v1 = iconst.i64 1
    v2 = atomic_rmw.i64 add v0, v1
    return v2
}"

def f : Function :=
  match (parseFile src).funcs[0]? with
  | some p => match p.func with
    | .ok f => f
    | .error _ => default
  | none => default

def prog : Program := { funcs := [f] }

deriving instance Inhabited for Frame
deriving instance Inhabited for State

def nextOf : StepResult → State
  | .next s => s
  | _ => default

def s0 : State :=
  match initState prog "f" [] Mem.empty with
  | .ok s => s
  | _ => default

/-- The state before the `atomic_rmw` (after the two `iconst`s). -/
def s2 : State := nextOf (step Env.empty prog (nextOf (step Env.empty prog s0)))

def isHeapOob : StepResult → Bool
  | .trapped .heapOob => true
  | _ => false

theorem s2_step_b : isHeapOob (step Env.empty prog s2) = true := by native_decide

theorem s2_step : step Env.empty prog s2 = .trapped .heapOob := by
  have h := s2_step_b
  revert h
  cases step Env.empty prog s2 with
  | trapped c => cases c <;> simp [isHeapOob]
  | _ => simp [isHeapOob]

theorem s2_body : s2.frame.body.head? = some ⟨[2], .atomicRmw .add .i64 {} 0 1⟩ := by
  native_decide

theorem s2_v0 : s2.frame.regs 0 = some ⟨.i64, 0#64⟩ := by native_decide

theorem s2_invalid : s2.mem.valid 0 8 = false := by native_decide

theorem f_memTrapAt : MemTrapAt Env.empty prog s2 .heapOob 0 8 := by
  refine ⟨s2_step, s2_invalid, ?_⟩
  have hb := s2_body
  cases hbd : s2.frame.body with
  | nil => rw [hbd] at hb; cases hb
  | cons st rest =>
    rw [hbd] at hb
    simp only [List.head?_cons, Option.some.injEq] at hb
    subst hb
    refine ⟨_, rest, rfl, ?_⟩
    have hv : s2.frame.get 0 = .ok ⟨.i64, 0#64⟩ := by
      simp only [Frame.get, s2_v0, Res.ofOption_some]
    exact .atomicRmw (ty := .i64) hv

/-- It is a `memTrapInst` statement, so `memTrapAt_of_trapped` applies. -/
theorem f_memTrapInst : (s2.frame.body.head?.map (memTrapInst ·.inst)) = some true := by
  rw [s2_body]; rfl

def isRunHeapOob : Outcome → Bool
  | .trapped .heapOob => true
  | _ => false

/-- **`Clif.run` traps `heap_oob`.** -/
theorem f_run : isRunHeapOob (run Env.empty prog "f" [] 10) = true := by native_decide

end Clif.MemTrapWitness
