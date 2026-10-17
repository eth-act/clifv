import FV.Backend

/-!
The typed AAPCS64 placement of a function's own signature (S11e3, #238), on the lowering itself.
`lowerFunction` of `(f64, i64, f32) -> f64` defines its parameters by an `Args` pinning the
values' vregs (class `float`, `int`, `float`) to v0, x0, v1 (X and V registers counted
separately), and returns the `f64` in v0; an integer signature lowers as before (x0, x1, and
the return in x0). `lake build FVTest.Backend.AbiTyped`.
-/

open Backend

/-- The first function of a CLIF text, lowered. -/
def lowerText (src : String) : Except String VCode :=
  match (Clif.parseFile src).funcs with
  | p :: _ => match p.func with
    | .ok f => lowerFunction f
    | .error _ => .error "parse error"
  | [] => .error "no function"

/-- `(f64, i64, f32) -> f64`, returning its first parameter. -/
def fifSrc : String :=
  "function %fif(f64, i64, f32) -> f64 {\nblock0(v0: f64, v1: i64, v2: f32):\n    return v0\n}\n"

/-- `(i64, i64) -> i64`, returning its second parameter. -/
def iiSrc : String :=
  "function %ii(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    return v1\n}\n"

/-- The entry block's instructions and the vreg classes of a lowering. -/
def entryOf (src : String) : Option (List MInst × List RegClass) :=
  match lowerText src with
  | .ok vc => vc.blocks[0]?.map fun b => (b.insts.toList, vc.classes.toList)
  | .error _ => none

-- floats in v0, v1, the integer in x0 (separate counters); the `f64` returned in v0
#guard entryOf fifSrc ==
  some ([.args [(.vreg 0 .float, .v 0), (.vreg 1 .int, .x 0), (.vreg 2 .float, .v 1)],
    .rets [(.vreg 0 .float, .v 0)]], [.float, .int, .float])

-- an integer signature: x0, x1, the return in x0, integer vregs (as before the typed ABI)
#guard entryOf iiSrc ==
  some ([.args [(.vreg 0 .int, .x 0), (.vreg 1 .int, .x 1)], .rets [(.vreg 1 .int, .x 0)]],
    [.int, .int])
