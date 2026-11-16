import FV.Backend.Proof.LowerSimTC
import FV.E2E.TypedRulesS

/-!
# The typed driver simulation over an abstract scope (#1002 part 2)

`LowerSimTC.lean`'s simulation never reads the shape's instruction scope: its hypotheses
`DriverHypTCS S` (`DriverHypTC` whose shape is `LowerShapeTCS S`, `ShapeS.lean`) give the same
theorems for every scope `S : InstScope`. They are `LowerSimTC.lean`'s proofs transported
(`scopeS_transport`, `ScopeTransport.lean`): `driver_correctTCS`, `driver_correctTCS_abi`,
`entry_step2TCS`, `sim_runTCS`. `DriverHypTC` and its theorems are unchanged.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- **`DriverHypTC` over the scope `S`** (#1002 part 2): the same hypotheses, the shape
`LowerShapeTCS S`. -/
structure DriverHypTCS (S : InstScope) (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState)
    (R : Reg → Reg) (gn : Nat → Nat) (bl : List BLow) (A : Nat → Nat → List Clif.ValueId)
    {W : Type} (sem : ISem CV W) (MR : MemRelTW W) (env : Clif.Env) (p : Clif.Program) : Prop where
  shape : LowerShapeTCS S f vc ctx st0 R gn bl
  cert : Cert f ctx st0 gn bl A
  dsem : DriverSemG sem
  /-- `lower` on statements (`instCallsT_of_rules`) -/
  insts : InstCallsT f ctx sem MR env p
  /-- terminator calls (`termCallsT_of_rules`) -/
  terms : TermCallsT ctx sem MR
  ext : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ fn args, st.inst = .call fn args →
    ∀ e, f.extern? fn = some e → p.func? e.name = none
  /-- the signature of an indirect call is among `f`'s indirect-call signatures, with register
  arguments (`E2E.InSubset.indSigs`) -/
  indSig : ∀ B ∈ f.blocks, ∀ st ∈ B.body, IndSigOk f (indSigs f) st.inst
  /-- `f` is in the typed scope with typed `try_call`s and the proven float operations -/
  subETC : Compile.functionETCF f = true
  /-- `br_table` indices have at most 32 bits (`lowerCheck`'s `brIdxOk`) -/
  brIdx : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term
  /-- no tail calls (`return_call` is outside clif-subset-v2 E) -/
  noTail : ∀ B ∈ f.blocks, ∀ fn args, B.term ≠ .returnCall fn args
  /-- M4: `lower_branch` on `try_call`s (`tryCalls_of_rules`), for an outgoing area that holds
  every `try_call`'s stack arguments (`lowerCheck`'s `callsStackOkB`) -/
  tries : ∃ out, TryCallsTC f ctx sem MR env p out ∧ TryStack f out
  /-- a `try_call` calls an extern (`E2E.InSubset.tryExterns`) -/
  tryExt : ∀ B ∈ f.blocks, ∀ fn args et, B.term = .tryCall fn args et →
    ∀ e, f.extern? fn = some e → p.func? e.name = none
  /-- M4: `lower_branch` on `try_call_indirect`s (`tryIndCalls_of_rules`) -/
  tryInd : TryIndCallsT f ctx sem MR env p (indSigs f)
  /-- the signature of a `try_call_indirect` is among `f`'s indirect-call signatures
  (`E2E.InSubset.indSigs`) -/
  tryIndSig : ∀ B ∈ f.blocks, ∀ c args et s, B.term = .tryCallIndirect c args et →
    f.sigDecls.lookup et.sig = some s → s ∈ indSigs f
  cfg : ∃ ss ps, vc.cfg = .ok (ss, ps)
  /-- the signature's parameter locations and byte sizes compute, one per parameter
  (`lowerCheckT`'s `entryOkBT`) -/
  entryLocs : (locsOf f.sig).length = f.sig.params.length ∧ ∃ bytes, sigParamBytes f.sig = .ok bytes

-- **The typed driver simulation over `DriverHypTCS S`** (`LowerSimTC.lean`'s, transported).
scopeS_transport driver_correctTC => driver_correctTCS
scopeS_transport driver_correctTC_abi => driver_correctTCS_abi
scopeS_transport entry_step2TC => entry_step2TCS
scopeS_transport sim_runTC => sim_runTCS

end Backend.Proof.Driver
