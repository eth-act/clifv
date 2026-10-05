import FV.E2E.PrepDirect
import FV.Backend.Proof.LowerComplete
import FV.Clif.Parse

/-!
# The end-to-end chain without the lowering and `prepare` validators

`Compiled` records that `lowerCheck` accepted `lowerFunction`'s output and `prepCheck`
`prepare`'s. On `Dominated` input in `LowerScope` (decidable conditions on the CLIF function
alone, `dominatedB`/`lowerScopeB`) both are theorems: `lowerCheck_complete` (V1) and
`prepCheck_complete` on `PrepDomain` VCode, which `lowerFunction` always produces
(`prepDomain_of_lower`, V2). So `Compiled.of_lower` builds `Compiled` from the pipeline's
results alone: every end-to-end theorem taking `hc : Compiled …` (`backend_correct_final`,
`backend_correct_opt_proven`, `backend_correct_legal`, …) holds with `Compiled.of_lower …` in
place of `hc`, without a validator premise.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Prep

/-- **`Compiled` without the `lowerCheck` and `prepCheck` premises**: the pipeline's results
and the input conditions `Dominated f`, `LowerScope f`. -/
theorem Compiled.of_lower {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hd : Dominated f) (hs : LowerScope f)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hch : checkAlloc vcp rf = .ok ()) (ha : lowerRFunc vcp rf = .ok af)
    (he : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb) : Compiled f k vc vcp rf af fa fb :=
  Compiled.of_prepDomain hl (lowerCheck_complete hd hs hl) hp
    (prepDomain_of_lower hs hl hs.nonempty) hch ha he hla

/-- `Compiled.of_lower` with the input conditions decided. -/
theorem Compiled.of_lowerB {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hd : dominatedB f = true)
    (hs : lowerScopeB f = true) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare vc = .ok vcp) (hch : checkAlloc vcp rf = .ok ())
    (ha : lowerRFunc vcp rf = .ok af) (he : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb) :
    Compiled f k vc vcp rf af fa fb :=
  Compiled.of_lower (dominated_of hd) (lowerScope_of hs) hl hp hch ha he hla

/-! ## Non-vacuity

A function with a loop (block parameters, a back edge with arguments through an edge block, a
value defined in the loop and used after it) satisfies both input conditions, and
`lowerFunction` lowers it: `lowerCheck_complete`'s premises hold together. -/

/-- The witness's source. -/
def lowerWitnessSrc : String := "function %sum(i64) -> i64 {
block0(v0: i64):
    v1 = iconst.i64 0
    jump block1(v0, v1)
block1(v2: i64, v3: i64):
    v4 = iadd v3, v2
    v5 = iconst.i64 1
    v6 = isub v2, v5
    brif v6, block1(v6, v4), block2
block2:
    return v4
}"

/-- The witness function. -/
def lowerWitness : Clif.Function :=
  match (Clif.parseFile lowerWitnessSrc).funcs[0]? with
  | some p => match p.func with
    | .ok f => f
    | .error _ => default
  | none => default

theorem lowerWitness_checks :
    dominatedB lowerWitness = true ∧ lowerScopeB lowerWitness = true ∧
      (lowerFunction lowerWitness).isOk = true ∧ lowerWitness.blocks.length = 3 := by
  native_decide

/-- **Non-vacuity of `lowerCheck_complete`**: its premises hold for `lowerWitness`, so the
validator accepts its lowering without being run. -/
theorem lowerCheck_complete_witness :
    Dominated lowerWitness ∧ LowerScope lowerWitness ∧
      ∃ vc, lowerFunction lowerWitness = .ok vc ∧ lowerCheck lowerWitness vc = true := by
  obtain ⟨hd, hs, hl, -⟩ := lowerWitness_checks
  have hd := dominated_of hd
  have hs := lowerScope_of hs
  cases h : lowerFunction lowerWitness with
  | error e => rw [h] at hl; cases hl
  | ok vc => exact ⟨hd, hs, vc, rfl, lowerCheck_complete hd hs h⟩

end E2E
