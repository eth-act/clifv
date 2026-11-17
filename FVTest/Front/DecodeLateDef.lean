import FV.Front.Bundle
import FV.Front.Raw

/-! # #1073: float instructions whose operand is defined later in the text

cg_clif writes the blocks of a function in creation order, not in dominance order, so a use may
precede its definition in the text, directly or through a value alias `vA -> vB` whose
destination is defined in a later block (cranelift-reader accepts both for an instruction with
an explicit type). `clif-decode` rejected such dumps with `cannot infer the type of vN (not yet
defined)`: the parser looked up the operand type of every float instruction, also of those whose
type is explicit (`fneg.f64 v56` in `plotters_backend::rasterizer::path::get_dir_vector`). Now
the operand type is looked up for the conversions only, and their checks (an i128 or f16 operand
is outside S) run at the end of the body when the operand is defined later.
-/

namespace DecodeLateDef

open Clif Front

/-- The shape of `get_dir_vector`'s dump, minimised: `fneg.f64` and `fcvt_to_sint.i64` of
aliases of a value defined in a later block. -/
def dump : String := "target aarch64

; symbol _RNlate
function u0:0(f64) -> f64, i64 system_v {
                                block0(v0: f64):
@0000                               jump block2

                                block1:
@0001                               v1 = fneg.f64 v5
@0002                               v2 = fcvt_to_sint.i64 v6
@0003                               return v1, v2

                                block2:
@0004                               v7 = fadd v0, v0
                                    v5 -> v7
                                    v6 -> v7
@0005                               jump block1
}

; clifv-extnames 1
; decl u0:0 func local \"_RNlate\"
; end clifv-extnames
"

/-- `clif-decode`'s `decodeText`: the dump read and decoded, its printed function checked to
parse back to it (`mkInput`). -/
def decoded : Except String String := do
  let d ← readDump dump
  let g ← decodeFn (← unitTable [d]) d
  pure (← mkInput d.header g "").clif

#guard decoded matches .ok _
-- the aliases are resolved: both instructions use the definition
#guard match decoded with
  | .ok t => (t.splitOn "fneg.f64 v7").length == 2 && (t.splitOn "fcvt_to_sint.i64 v7").length == 2
  | .error _ => false

/-- The parse result of the first function of a CLIF text. -/
def parse1 (src : String) : Option (Except ParseError Function) :=
  (parseFile src).funcs.head?.map (·.func)

-- a conversion of a value defined later, without an alias
#guard parse1 "function %f(f32) -> f64 {
block0(v0: f32):
    jump block2

block1:
    v1 = fpromote.f64 v6
    return v1

block2:
    v6 = fadd v0, v0
    jump block1
}
" matches some (.ok _)

-- the deferred checks still reject an i128 or f16 operand, and a value that is never defined
#guard parse1 "function %f(i64) -> f64 {
block0(v0: i64):
    jump block2

block1:
    v1 = fcvt_from_sint.f64 v5
    return v1

block2:
    v6 = sextend.i128 v0
    v5 -> v6
    jump block1
}
" matches some (.error (.unsupported "fcvt_from_sint with an i128 operand or result"))

#guard parse1 "function %f(i16) -> f32 {
block0(v0: i16):
    jump block2

block1:
    v1 = fpromote.f32 v5
    return v1

block2:
    v6 = bitcast.f16 v0
    v5 -> v6
    jump block1
}
" matches some (.error (.unsupported "fpromote of an f16 (f16 values are only moved)"))

#guard parse1 "function %f(i64) -> f64 {
block0(v0: i64):
    v1 = fcvt_from_sint.f64 v9
    return v1
}
" matches some (.error (.malformed "cannot infer the type of v9 (never defined)"))

end DecodeLateDef
