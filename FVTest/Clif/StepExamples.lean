import FV.Clif

/-!
# Symbolic execution through `Clif.run`

Checks that `Clif.run` can be computed through in proofs about arbitrary inputs (the use
M2 makes of it): straight-line code and a call by `rfl` (kernel evaluation with free
variables), a branch on a symbolic condition by `simp`, and a stack-slot round trip on a
concrete input by `decide`.
-/

namespace ClifTest.StepExamples

open Clif

def p32 : AbiParam := { ty := .i32 }

/-- `function %add(i32, i32) -> i32 { block0(v0, v1): v2 = iadd v0, v1; return v2 }` -/
def addFn : Function where
  name := "add"
  sig := { params := [p32, p32], returns := [p32] }
  blocks := [{ id := 0, params := [(0, .i32), (1, .i32)],
               body := [{ results := [2], inst := .binary .iadd .i32 0 1 }],
               term := .ret [2] }]

/-- `%max`: `brif (icmp ugt v0, v1), block1(v0), block1(v1)`; `block1(v2): return v2`. -/
def maxFn : Function where
  name := "max"
  sig := { params := [p32, p32], returns := [p32] }
  blocks := [{ id := 0, params := [(0, .i32), (1, .i32)],
               body := [{ results := [2], inst := .icmp .ugt .i32 0 1 }],
               term := .brif 2 ⟨1, [0]⟩ ⟨1, [1]⟩ },
             { id := 1, params := [(3, .i32)], term := .ret [3] }]

/-- `%twice(v0) = call %add(v0, v0)`. -/
def twiceFn : Function where
  name := "twice"
  sig := { params := [p32], returns := [p32] }
  externs := [(0, { name := "add", sig := { params := [p32, p32], returns := [p32] } })]
  blocks := [{ id := 0, params := [(0, .i32)],
               body := [{ results := [1], inst := .call 0 [0, 0] }],
               term := .ret [1] }]

/-- Store to a stack slot and load back. -/
def slotFn : Function where
  name := "slot"
  sig := { params := [p32], returns := [p32] }
  slots := [(0, { size := 4 })]
  blocks := [{ id := 0, params := [(0, .i32)],
               body := [{ results := [1], inst := .stackAddr .i64 0 0 },
                        { inst := .store .store .i32 { trapCode := none } 0 1 0 },
                        { results := [2], inst := .load .load .i32 { trapCode := none } 1 0 }],
               term := .ret [2] }]

def prog : Program := { funcs := [addFn, maxFn, twiceFn, slotFn] }

theorem add_run (x y : BitVec 32) :
    (run {} prog "add" [⟨.i32, x⟩, ⟨.i32, y⟩] 10).returnedVals? = some [⟨.i32, x + y⟩] := rfl

theorem twice_run (x : BitVec 32) :
    (run {} prog "twice" [⟨.i32, x⟩] 10).returnedVals? = some [⟨.i32, x + x⟩] := rfl

set_option maxHeartbeats 2000000 in
/-- A branch on a symbolic condition: split on the condition, then compute. -/
theorem max_run (x y : BitVec 32) :
    (run {} prog "max" [⟨.i32, x⟩, ⟨.i32, y⟩] 10).returnedVals? =
      some [⟨.i32, if y.ult x then x else y⟩] := by
  cases h : y.ult x <;> simp [run, Program.initMem, runWith, initState, enterFunc, runLoop, step,
    stepTerm, evalInst, enterBlock, continueWith, returnValues, Frame.get, Frame.getAs,
    Frame.getMany, checkTys, Sem.icmp, Sem.intcc, Sem.bool8, Sem.truthy, prog, addFn, maxFn,
    twiceFn, slotFn, Function.block?, Function.entry?, Program.func?, AbiParam.tys,
    Regs.setMany, Regs.set, p32, Mem.free, Mem.empty, Outcome.returnedVals?, Val.as?, Ty.width, h]

/-- The stack slot program on a concrete input. -/
theorem slot_run_42 :
    (run {} prog "slot" [⟨.i32, 42#32⟩] 10).returnedVals? = some [⟨.i32, 42#32⟩] := by
  decide

end ClifTest.StepExamples
