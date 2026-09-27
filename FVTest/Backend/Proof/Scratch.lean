import FV.Backend
open Backend Isle Isle.Aarch64

def p8 : Clif.AbiParam := { ty := .i8 }
def addFn : Clif.Function where
  name := "add"
  sig := { params := [p8, p8], returns := [p8] }
  blocks := [{ id := 0, params := [(0, .i8), (1, .i8)],
               body := [{ results := [2], inst := .binary .iadd .i8 0 1 }],
               term := .ret [2] }]

def ctxSt : Except String (Ctx × Array (Nat × Nat) × LState) := buildCtx addFn

#eval match ctxSt with
  | .ok (ctx, _, st) => repr ((runTerm ctx "lower" [.inst 0] st).map fun (v, s, tr) => (s.emitted, tr))
  | .error e => repr e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
example : (program.rulesOf 686).length = 0 := by decide +kernel
