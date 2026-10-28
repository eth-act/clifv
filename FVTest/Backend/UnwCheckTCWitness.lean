import FV.Backend.Proof.LowerSimUCheckTC
import FVTest.Backend.FloatDriverT

/-!
Non-vacuity of the typed-try_call exceptional-edge validator (S11e6, #585): the compiled
functions of `FVTest/Backend/float_try.clif`'s typed-`try_call` functions `%try_scale`,
`%try_pair` and `%try_stk` (direct `try_call`s of callees with `f32`/`f64` parameters and
returns) meet `lowerCheckUTC = lowerCheckTC && unwCheckTC` — `unwCheckTC` replays the typed
lowering (`lowBlocksC`, `tryRegsOfC`: the returns' vregs of their classes) and checks the
exceptional edges with the class-aware handler-argument registers (`exnArgRegC`). The integer
validator `unwCheck` replays the integer lowering (`lowBlocks`, `tryRegsOf`) and rejects all
three (the reported "unwinding check failed: unwCheck"). Checks by `native_decide`
(witness only).
`lake build FVTest.Backend.UnwCheckTCWitness`.
-/

open Backend Backend.Proof Backend.Proof.Driver

namespace UnwCheckTCWitness

/-- `%try_scale(f64, i64) -> f64` (`float_try.clif`). -/
def fTryScale : Clif.Function := FloatDriverT.fnOfText
  "function %try_scale(f64, i64) -> f64 {
    sig0 = (f64, i64) -> f64
    fn0 = %scale(f64, i64) -> f64

block0(v0: f64, v1: i64):
    try_call fn0(v0, v1), sig0, block1(ret0), [ tag1: block2(exn0) ]

block1(v2: f64):
    return v2

block2(v3: i64):
    return v0
}
"

/-- `%try_pair(f32, i64) -> i64, f32` (`float_try.clif`). -/
def fTryPair : Clif.Function := FloatDriverT.fnOfText
  "function %try_pair(f32, i64) -> i64, f32 {
    sig0 = (f32, i64) -> f32, i64
    fn0 = %pair(f32, i64) -> f32, i64

block0(v0: f32, v1: i64):
    try_call fn0(v0, v1), sig0, block1(ret1, ret0), [ tag1: block2(exn0) ]

block1(v2: i64, v3: f32):
    return v2, v3

block2(v6: i64):
    return v6, v0
}
"

/-- `%try_stk(f64, f64) -> f64` (`float_try.clif`; the callee takes stack arguments). -/
def fTryStk : Clif.Function := FloatDriverT.fnOfText
  "function %try_stk(f64, f64) -> f64 {
    sig0 = (f64, f64, f64, f64, f64, f64, f64, f64, f64) -> f64
    fn0 = %stk(f64, f64, f64, f64, f64, f64, f64, f64, f64) -> f64

block0(v0: f64, v1: f64):
    try_call fn0(v0, v0, v0, v0, v0, v0, v0, v0, v1), sig0, block1(ret0), [ tag1: block2(exn0) ]

block1(v2: f64):
    return v2

block2(v3: i64):
    return v0
}
"

/-- **Witness**: the exceptional-edge validator holds for the three compiled functions. -/
theorem unwCheckTC_true (f : Clif.Function) (hc : f = fTryScale ∨ f = fTryPair ∨ f = fTryStk) :
    unwCheckTC f (FloatDriverT.vcOf f) = true := by
  rcases hc with rfl | rfl | rfl <;> native_decide

/-- **Witness**: `lowerCheckUTC` holds for the three compiled functions. -/
theorem lowerCheckUTC_true (f : Clif.Function) (hc : f = fTryScale ∨ f = fTryPair ∨ f = fTryStk) :
    lowerCheckUTC f (FloatDriverT.vcOf f) = true := by
  rcases hc with rfl | rfl | rfl <;> native_decide

/-- The integer validator rejects them (the reported `unwinding check failed: unwCheck`). -/
theorem unwCheck_false (f : Clif.Function) (hc : f = fTryScale ∨ f = fTryPair ∨ f = fTryStk) :
    unwCheck f (FloatDriverT.vcOf f) = false := by
  rcases hc with rfl | rfl | rfl <;> native_decide

end UnwCheckTCWitness
