import FV.Backend.Isel

/-!
The typed AAPCS64 placement of a function's own signature (S11e3, #238), on the lowering itself.
`lowerFunction` of `(f64, i64, f32) -> f64` defines its parameters by an `Args` pinning the
values' vregs (class `float`, `int`, `float`) to v0, x0, v1 (X and V registers counted
separately), and returns the `f64` in v0; an integer signature lowers as before (x0, x1, and
the return in x0). A `call` of an extern `(f64, i64, f32) -> f64` (S11e5a) uses its arguments
in v0, x0, v1 and defines a fresh `float` vreg from v0, as Cranelift places them (natively
checked against Cranelift's code with C callees, `docs/contracts/e2e.md` "Typed ABI placement").
`lake build FVTest.Backend.AbiTyped`.
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

/-- `(f64, i64, f32) -> f64` calling an extern of the same signature with its parameters. -/
def callFifSrc : String :=
  "function %callfif(f64, i64, f32) -> f64 {\n    fn0 = %callee(f64, i64, f32) -> f64\n\n" ++
  "block0(v0: f64, v1: i64, v2: f32):\n    v3 = call fn0(v0, v1, v2)\n    return v3\n}\n"

/-- `(f32, i64, f64) -> f64` calling the same extern with its parameters reversed: the
`f64` comes in v1 and goes out in v0, the `f32` the other way round. -/
def callPermSrc : String :=
  "function %callperm(f32, i64, f64) -> f64 {\n    fn0 = %callee(f64, i64, f32) -> f64\n\n" ++
  "block0(v0: f32, v1: i64, v2: f64):\n    v3 = call fn0(v2, v1, v0)\n    return v3\n}\n"

/-- The uses and defs of the entry block's call. -/
def callOf (src : String) : Option (List (Reg × Reg) × List (Reg × Reg)) :=
  (entryOf src).bind fun (is, _) => is.findSome? fun
    | .call ci => some (ci.uses, ci.defs)
    | _ => none

-- the call's arguments in v0, x0, v1, its `f64` result defined from v0 into a `float` vreg
#guard callOf callFifSrc ==
  some ([(.vreg 0 .float, .v 0), (.vreg 1 .int, .x 0), (.vreg 2 .float, .v 1)],
    [(.v 0, .vreg 4 .float)])

-- reversed floats: the `f64` value (vreg 2, entered in v1) goes out in v0, the `f32` in v1
#guard callOf callPermSrc ==
  some ([(.vreg 2 .float, .v 0), (.vreg 1 .int, .x 0), (.vreg 0 .float, .v 1)],
    [(.v 0, .vreg 4 .float)])
