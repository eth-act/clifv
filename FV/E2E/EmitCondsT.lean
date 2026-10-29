import FV.E2E.SizeLowerT
import FV.E2E.EmitCondsLowerT
import FV.Backend.Proof.IselEmitTDriver
import FV.E2E.LinkScopeInputT2

/-!
# The emission conditions on the typed scope (S11 #35)

`emitCondsB` (the size bound `spillSizeOkB`, the immediates `immsOkB`, no `al`/`nv` branch
`noAlwaysB`, block-label branch targets `branchTargetsOkB`) of the prepared VCode, proven from the
input on the typed scope, so `lowerOutTB` need not run it:

* the size bound from `IselSzT` (`Driver.iselSzT`, `spillSizeOkB_of_sizeOkBT`), the other three
  from `IselEmitT` (`Driver.iselEmitT`, `emitParts_lowerT`);
* `emitConds_lowerT`: on `prepare vc` of `lowerFunction f = .ok vc`;
* `emitConds_cleanup_lowerT`: on `prepare (prune vc)`, the dead-code cleanup's output;
* `emitCondsB_of_T2`, `emitCondsB_cleanup_of_T2`: on `fnScopeInTB2` with `bitcastWidthB`
  (every `bitcast` between types of one width, the CLIF verifier's rule; `bitcast.f32` of an
  `i8` would lower to an unencodable `fmov`).

The premises are `formsCovered_completeT`'s (`Dominated`, `LowerScopeT`, class-checked float
`store`s and `select`s) with `extendsWidenB`, `bitcastWidthB` and `sizeOkB`, and the literal loads'
reach `poolReachB` of the prepared VCode (#565: the typed lowering may use the literal pool; a
function over 1 MiB with a literal load is outside `spillSizeOkB`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **The emission conditions of the pipeline's output on the typed scope**: for `f` in
`Dominated` and `LowerScopeT` with class-checked float `store`s and `select`s, whose extends
widen, whose `bitcast`s keep the width and which meets the size bound, the prepared VCode of
`lowerFunction f` meets `emitCondsB`. -/
theorem emitConds_lowerT {f : Clif.Function} {vc vcp : VCode} (hdom : dominatedB f = true)
    (hs : LowerScopeT f) (hst : Compile.storeTypedB f = true) (hsel : Compile.selectTypedB f = true)
    (hw : extendsWidenB f = true) (hbw : bitcastWidthB f = true) (hsz : sizeOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hpool : poolReachB vcp = true) : emitCondsB vcp = true := by
  have h0 := spillSizeOkB_of_sizeOkBT hdom hs hst hsel hsz hl hp hpool
  obtain ⟨h1, h2, h3⟩ := emitParts_lowerT hdom hs (iselEmitT hdom hs hst hsel hw hbw) hl hp
  simp [emitCondsB, h0, h1, h2, h3]

/-- **`emitConds_lowerT` after the dead-code cleanup**: the prepared `prune`d VCode meets
`emitCondsB`. -/
theorem emitConds_cleanup_lowerT {f : Clif.Function} {vc vcp : VCode} (hdom : dominatedB f = true)
    (hs : LowerScopeT f) (hst : Compile.storeTypedB f = true) (hsel : Compile.selectTypedB f = true)
    (hw : extendsWidenB f = true) (hbw : bitcastWidthB f = true) (hsz : sizeOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare (prune vc) = .ok vcp)
    (hpool : poolReachB vcp = true) : emitCondsB vcp = true := by
  have h0 := spillSizeOkB_cleanup_of_sizeOkBT hdom hs hst hsel hsz hl hp hpool
  obtain ⟨h1, h2, h3⟩ := emitParts_cleanup_lowerT hdom hs (iselEmitT hdom hs hst hsel hw hbw) hl hp
  simp [emitCondsB, h0, h1, h2, h3]

end E2E

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- The conjuncts of `fnScopeInTB2` the emission conditions need. -/
theorem emitParts_of_T2 {g : Clif.Function} (h : fnScopeInTB2 g = true) :
    dominatedB g = true ∧ LowerScopeT g ∧ Compile.storeTypedB g = true ∧
      Compile.selectTypedB g = true ∧ extendsWidenB g = true ∧ sizeOkB g = true := by
  obtain ⟨hT, -, hsel⟩ := fnScopeInT2_parts h
  have p := fnScopeInT_parts hT
  exact ⟨p.2.2.2.2.2.2.2.2.2.2.1, lowerScopeT_of p.2.2.2.2.2.2.2.2.2.2.2.1, p.2.1, hsel,
    p.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- **`emitCondsB` holds on `fnScopeInTB2` with `bitcastWidthB`**: of `prepare`'s output of
`lowerFunction`'s VCode. -/
theorem emitCondsB_of_T2 {g : Clif.Function} {vc vcp : VCode} (h : fnScopeInTB2 g = true)
    (hbw : bitcastWidthB g = true) (hl : lowerFunction g = .ok vc) (hp : prepare vc = .ok vcp)
    (hpool : poolReachB vcp = true) : emitCondsB vcp = true :=
  let ⟨hdom, hs, hst, hsel, hw, hsz⟩ := emitParts_of_T2 h
  emitConds_lowerT hdom hs hst hsel hw hbw hsz hl hp hpool

/-- **`emitCondsB` holds on `fnScopeInTB2` with `bitcastWidthB`, after the dead-code cleanup**:
of `prepare`'s output of the `prune`d VCode. -/
theorem emitCondsB_cleanup_of_T2 {g : Clif.Function} {vc vcp : VCode} (h : fnScopeInTB2 g = true)
    (hbw : bitcastWidthB g = true) (hl : lowerFunction g = .ok vc)
    (hp : prepare (prune vc) = .ok vcp) (hpool : poolReachB vcp = true) : emitCondsB vcp = true :=
  let ⟨hdom, hs, hst, hsel, hw, hsz⟩ := emitParts_of_T2 h
  emitConds_cleanup_lowerT hdom hs hst hsel hw hbw hsz hl hp hpool

end E2E.LinkCheck
