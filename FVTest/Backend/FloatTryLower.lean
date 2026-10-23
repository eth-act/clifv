import FVTest.Backend.FloatCtlT
import FV.Backend.Proof.LowerLoopT
import FV.Backend.Proof.SpillEdgesLowT

/-!
Non-vacuity of the typed `try_call` lowering (S11e6 slice 2b, #419): `lowerFunction` lowers a
direct `try_call` of a callee with `f32`/`f64` parameters or returns (`exnTableOpndC`,
`tryCallDataC`, `tryRegsOfC`), which the integer operand `exnTableOpnd` rejects.

* `fTryF` calls `%g(f64, i64) -> f64` (system_v): the `tryCall`'s fixed uses are v0 (the `f64`)
  and x0 (the `i64`), its defs are v0 into a fresh float vreg (the return) and x0, x1 into fresh
  integer vregs (the exception payloads, `payloadRegs`); the normal-return edge passes the float
  vreg to `block1`'s `f64` parameter.
* `fTryMix` calls `%h(i64) -> f64, i64`: the returns are in v0 and x0 (`retRegsC`), so the first
  payload (x0) shares the second return's vreg (`set_vreg_alias`), the second (x1) is fresh.

The typed loop's statements now take the externs' integer signatures (`loop_runT`,
`lowerFunction_runT`, `lowT_of`); `runT_fTryI` applies `lowerFunction_runT` to an integer
`try_call`. `lake build FVTest.Backend.FloatTryLower`.
-/

open Backend Backend.Proof Backend.Proof.Driver

namespace FloatTryLower

open FloatCtlT

/-- A `try_call` of a callee taking and returning `f64`. -/
def fTryF : Clif.Function := fnOfText
  "function %t(f64, i64) -> f64 {
    sig0 = (f64, i64) -> f64
    fn0 = %g(f64, i64) -> f64
block0(v0: f64, v1: i64):
    try_call fn0(v0, v1), sig0, block1(ret0), [ default: block2(exn0) ]
block1(v2: f64):
    return v2
block2(v3: i64):
    return v0
}
"

/-- A `try_call` of a callee returning an `f64` and an `i64`. -/
def fTryMix : Clif.Function := fnOfText
  "function %m(i64) -> i64 {
    sig0 = (i64) -> f64, i64
    fn0 = %h(i64) -> f64, i64
block0(v0: i64):
    try_call fn0(v0), sig0, block1(ret1), [ tag1: block2(exn0), default: block2(exn1) ]
block1(v1: i64):
    return v1
block2(v2: i64):
    return v2
}
"

/-- An integer `try_call`. -/
def fTryI : Clif.Function := fnOfText
  "function %i(i64) -> i64 {
    sig0 = (i64) -> i64
    fn0 = %k(i64) -> i64
block0(v0: i64):
    try_call fn0(v0), sig0, block1(ret0), [ default: block2(exn0) ]
block1(v1: i64):
    return v1
block2(v2: i64):
    return v2
}
"

/-- The VCode of `f` (`default` if lowering fails). -/
def vcOf (f : Clif.Function) : VCode :=
  match lowerFunction f with
  | .ok vc => vc
  | .error _ => default

/-- The `tryCall`s of `f`'s VCode. -/
def tryCallsOf (f : Clif.Function) : List CallInfo :=
  (vcOf f).blocks.toList.flatMap fun b => b.insts.toList.filterMap fun
    | .tryCall c _ => some c
    | _ => none

/-- The exception table operand of the first block's terminator, integer and typed. -/
def opnds (f : Clif.Function) : Bool × Bool :=
  match (f.blocks[0]?.map (·.term)) with
  | some (.tryCall _ _ et) => ((exnTableOpnd f et).toBool, (exnTableOpndC f et).toBool)
  | _ => (false, false)

-- the integer operand rejects the float signatures, the typed one accepts them
#guard opnds fTryF == (false, true) && opnds fTryMix == (false, true) && opnds fTryI == (true, true)
-- `lowerFunction` lowers all three
#guard (lowerFunction fTryF).toBool && (lowerFunction fTryMix).toBool && (lowerFunction fTryI).toBool
-- `fTryF`: uses v0 (f64), x0 (i64); defs v0 into a float vreg, the payloads x0, x1 into int vregs
#guard (tryCallsOf fTryF).map (·.uses.map (·.2)) == [[.v 0, .x 0]]
#guard (tryCallsOf fTryF).map (·.defs.map (·.1)) == [[.v 0, .x 0, .x 1]]
#guard (tryCallsOf fTryF).map (·.defs.map (·.2.homeCls)) == [[.float, .int, .int]]
-- `fTryMix`: returns in v0 and x0, then the fresh payload x1 (x0's payload is the second return)
#guard (tryCallsOf fTryMix).map (·.defs.map (·.1)) == [[.v 0, .x 0, .x 1]]
#guard (tryCallsOf fTryMix).map (·.defs.map (·.2.homeCls)) == [[.float, .int, .int]]
-- the integer `try_call` is lowered as before (x0 return aliased by the first payload)
#guard (tryCallsOf fTryI).map (·.defs.map (·.1)) == [[.x 0, .x 1]]

/-- **`lowerFunction` lowers a `try_call` of a callee returning `f64`** (witness:
`native_decide`). -/
theorem lowerFunction_fTryF_ok : ∃ vc, lowerFunction fTryF = .ok vc := by
  have h : (lowerFunction fTryF).toBool = true := by native_decide
  cases hl : lowerFunction fTryF with
  | ok vc => exact ⟨vc, rfl⟩
  | error e => rw [hl] at h; cases h

/-- The integer operand rejects `fTryF`'s exception table (before S11e6 slice 2b `lowerFunction`
failed with "try_call with f32/f64 parameters or returns"). -/
theorem exnTableOpnd_fTryF_rejects : (opnds fTryF).1 = false := by native_decide

/-- `fTryI`'s externs have integer signatures. -/
theorem externs_fTryI : fTryI.externs.all (Compile.sigE ·.2.sig) = true := by native_decide

theorem lowerFunction_fTryI_ok : ∃ vc, lowerFunction fTryI = .ok vc := by
  have h : (lowerFunction fTryI).toBool = true := by native_decide
  cases hl : lowerFunction fTryI with
  | ok vc => exact ⟨vc, rfl⟩
  | error e => rw [hl] at h; cases h

/-- **`lowerFunction_runT` applies to an integer `try_call`** (its new premise holds). -/
theorem runT_fTryI : ∃ vc ctx ranges st0 bl, lowerFunction fTryI = .ok vc ∧
    buildCtx fTryI = .ok (ctx, ranges, st0) ∧
    lowBlocks fTryI (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 fTryI.blocks st0
      fTryI.blocks.length = some bl ∧
    vc.blocks = vcBlocksOfT fTryI ctx bl ∧ vc.outgoing = outOf st0 bl ∧ LoopFactsT fTryI ctx bl := by
  obtain ⟨vc, h⟩ := lowerFunction_fTryI_ok
  obtain ⟨ctx, ranges, st0, bl, h1, h2, h3, h4, h5⟩ := lowerFunction_runT externs_fTryI h
  exact ⟨vc, ctx, ranges, st0, bl, h, h1, h2, h3, h4, h5⟩

/-- **`lowT_of` applies to an integer `try_call`.** -/
theorem lowT_fTryI : ∃ vc ctx st0 bl RR, lowerFunction fTryI = .ok vc ∧
    Spill.LowT fTryI vc ctx st0 bl RR := by
  obtain ⟨vc, h⟩ := lowerFunction_fTryI_ok
  obtain ⟨ctx, st0, bl, RR, H⟩ := Spill.lowT_of externs_fTryI h
  exact ⟨vc, ctx, st0, bl, RR, h, H⟩

end FloatTryLower
