import FV.E2E.VerifiableT
import FVTest.E2E.FloatFinalT
import FVTest.Backend.FloatArithCtxT
import FV.E2E.LinkCheck
import FV.Backend.Proof.LowerCompleteTCF

/-!
Non-vacuity of the literal-pool `f64const` in the typed final theorem (#1002 part 2).

* `fLit` (`%litpool` of `FVTest/Backend/float_litpool.clif`: `f64const 0x1.7b8bac710cb29p0`,
  bits `0x3ff7b8bac710cb29`, none of `constant_f64`'s cheaper forms) is outside the typed scopes
  without literal pool (`Compile.functionET`, `Compile.functionETF`: `PoolLoadWitness.fLit_outside`)
  and inside `InSubsetTCF` (`Compile.functionETCF`'s statements are `Compile.instETFL`); its whole
  pipeline succeeds (`CompiledTCF`: the validator `lowerCheckTCF` accepts it), the prepared
  code's forms are covered (the pool load in `FormsCovered`'s third category), and the backend
  reports it verified (`verdict_lit`). These are `backend_correct_finalTCF`'s premises besides the
  run/link contracts (`backend_correct_finalTCF_lit`).
* `fDup` (`%litpool_dup`: two `f64const`s of the same bits): two literal loads of one
  constant-pool entry (`VCodeConstants` deduplicates by value, as Cranelift; the bytes are
  `scripts/lean-backend-encode-check.sh FVTest/Backend/float_litpool.clif`'s), verified too.
* `fF32` (an `f32const` without `fmov` immediate): `constant_f32` never uses the literal pool
  (`mov w, #imm; fmov s, w`, Cranelift's `inst.isle:4252`), so the prepared code has no pool load.
* `shapeOkTF_eq_S_old_false`: the statement of `Driver.shapeOkTF_eq_S` before #1002 part 2 (the
  check `instScopeOkF`) is false: `shapeOkTF` accepts `fLit`'s lowering, which `instScopeOkF`
  rejects.

Checks by `native_decide` (witness only). `lake build FVTest.E2E.PoolConstFinalTCF`.
-/

open Backend Backend.Proof Backend.Proof.Driver E2E E2E.LinkCheck

namespace PoolConstFinalTCF

open FloatFinalT

/-- `f64const 0x1.7b8bac710cb29p0`: a literal-pool constant. -/
def fLit : Clif.Function := fnOfTextA
  "function %litpool() -> f64 {\nblock0:\n    v0 = f64const 0x1.7b8bac710cb29p0\n    return v0\n}\n"

/-- Two `f64const`s of the same bits: one constant-pool entry, two literal loads. -/
def fDup : Clif.Function := fnOfTextA
  "function %litpool_dup() -> f64 {\nblock0:\n    v0 = f64const 0x1.7b8bac710cb29p0\n    v1 = f64const 0x1.7b8bac710cb29p0\n    v2 = fadd v0, v1\n    return v2\n}\n"

/-- An `f32const` without `fmov` immediate (bits `0x3f91a2b4`). -/
def fF32 : Clif.Function := fnOfTextA
  "function %f32nopool() -> f32 {\nblock0:\n    v0 = f32const 0x1.234568p0\n    return v0\n}\n"

-- `fLit`: outside the typed scopes without literal pool, inside the scope with float calls
#guard !Compile.functionE fLit && !Compile.functionET fLit && !Compile.functionETF fLit &&
  !Compile.functionETC fLit && Compile.functionETCF fLit
#guard lowerCheckTCF fLit (FloatDriverT.vcOf fLit)
#guard (unverifiedReason? fLit).isNone && verifiableTCF fLit
-- its prepared code has a literal-pool load of the entry `0x3ff7b8bac710cb29`
#guard (vcpOf fLit).blocks.any fun vb => vb.insts.any fun i =>
  i.isPoolLoad && match i with
    | .fpuLoad .size64 _ (.const c) _ => Nat.beq c 0x3ff7b8bac710cb29
    | _ => false

-- `fDup`: verified; two literal loads, one entry (its two data words once each)
#guard Compile.functionETCF fDup && lowerCheckTCF fDup (FloatDriverT.vcOf fDup) &&
  (unverifiedReason? fDup).isNone
#guard (faOf fDup).lines.toList.countP Line.isLit == 2
#guard (faOf fDup).lines.toList.countP (· matches .data 0xc710cb29) == 1 &&
  (faOf fDup).lines.toList.countP (· matches .data 0x3ff7b8ba) == 1

-- `fF32`: in the typed scope already (`f32const` needs no pool), no pool load
#guard Compile.functionET fF32 && (unverifiedReason? fF32).isNone && (vcpOf fF32).noPoolB

/-- **Witness**: `fLit` is in the scope with the float operations, in a program without
functions. -/
theorem inSubsetTCF_lit : InSubsetTCF { funcs := [] } fLit :=
  InSubsetTCF.of_verifiableTCF (by native_decide) fun _ => rfl

/-- **Witness**: the compiled-code premise holds for `fLit`. -/
theorem compiledTCF_lit :
    CompiledTCF fLit 0 (FloatDriverT.vcOf fLit) (vcpOf fLit) (rfOf fLit) (afOf fLit) (faOf fLit)
      (fbOf fLit) := by
  refine ⟨?_, by native_decide, ?_, by native_decide, ?_, ?_, ?_, ?_⟩
  · have hok : (lowerFunction fLit).toBool = true := by native_decide
    unfold FloatDriverT.vcOf
    cases h : lowerFunction fLit with
    | error e => rw [h] at hok; cases hok
    | ok vc => rfl
  · have hok : (Backend.prepare (FloatDriverT.vcOf fLit)).toBool = true := by native_decide
    unfold vcpOf
    cases h : Backend.prepare (FloatDriverT.vcOf fLit) with
    | error e => rw [h] at hok; cases hok
    | ok vcp => rfl
  · have hok : (checkAlloc (vcpOf fLit) (rfOf fLit)).isOk = true := by native_decide
    cases h : checkAlloc (vcpOf fLit) (rfOf fLit) with
    | error e => rw [h] at hok; cases hok
    | ok u => rfl
  · have hok : (lowerRFunc (vcpOf fLit) (rfOf fLit)).toBool = true := by native_decide
    unfold afOf
    cases h : lowerRFunc (vcpOf fLit) (rfOf fLit) with
    | error e => rw [h] at hok; cases hok
    | ok af => rfl
  · have hok : (emitFunc 0 (afOf fLit)).toBool = true := by native_decide
    unfold faOf
    cases h : emitFunc 0 (afOf fLit) with
    | error e => rw [h] at hok; cases hok
    | ok fa => rfl
  · have hok : (faOf fLit).layout.toBool = true := by native_decide
    unfold fbOf
    cases h : (faOf fLit).layout with
    | error e => rw [h] at hok; cases hok
    | ok fb => rfl

/-- **Witness**: the prepared code's forms are covered (its literal-pool load in the third
category). -/
theorem formsCovered_lit : FormsCovered ⟨(faOf fLit).k, (afOf fLit).slotBase⟩ (vcpOf fLit) :=
  (formsCoveredB_iff _ _).mp (by native_decide)

/-- **Witness**: the backend reports `fLit` verified: no reason, in the scope with the float
operations only, and its validated lowering passes `lowerCheckTCF`. -/
theorem verdict_lit : unverifiedReason? fLit = none ∧
    (Compile.functionE fLit = false ∧ Compile.functionET fLit = false ∧
      Compile.functionETC fLit = false ∧ verifiableTCF fLit = true) ∧
    lowerFunction fLit = .ok (getOk (lowerChecked fLit true)) ∧
      lowerCheckTCF fLit (getOk (lowerChecked fLit true)) = true := by
  have hn : unverifiedReason? fLit = none := by native_decide
  have hE : Compile.functionE fLit = false := by native_decide
  have hT : Compile.functionET fLit = false := by native_decide
  have hTC : Compile.functionETC fLit = false := by native_decide
  have hv : (lowerChecked fLit true).toBool = true := by native_decide
  refine ⟨hn, ?_, lowerChecked_specTCF (getOk_eq hv) hE hT hTC⟩
  rcases verdict_of_unverifiedReasonF hn with h | ⟨-, h⟩ | ⟨-, -, h⟩ | h
  · simp [Backend.verifiable, hE] at h
  · simp [Backend.verifiableT, hT] at h
  · simp [Backend.verifiableTC, hTC] at h
  · exact h

/-- **The typed final theorem applies to a literal-pool `f64const`** (`fLit`): with its subset,
compiled code and form coverage discharged above, the Arm run of the compiled function (whose
`ldr d0, <entry>` reads the constant-pool entry after the body) refines the CLIF run, under the
remaining run/link contracts. -/
theorem backend_correct_finalTCF_lit
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hC : ∀ s, CalleeOk (frameW K (RAFrame.compute (vcpOf fLit) (rfOf fLit)).intBase
      (RAFrame.compute (vcpOf fLit) (rfOf fLit)).size (afOf fLit) s) K X H (vcpOf fLit).CallSite)
    (hCT : (∃ B ∈ fLit.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute (vcpOf fLit) (rfOf fLit)).intBase
        (RAFrame.compute (vcpOf fLit) (rfOf fLit)).size (afOf fLit) s) X H (vcpOf fLit).TrySite)
    (hTls : hasTls fLit = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute (vcpOf fLit) (rfOf fLit)).intBase
        (RAFrame.compute (vcpOf fLit) (rfOf fLit)).size (afOf fLit) s) K X H)
    (hX : ∀ s, XCallsOk env (fLit.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fLit) (rfOf fLit)).intBase
        (RAFrame.compute (vcpOf fLit) (rfOf fLit)).size (afOf fLit) s, syms,
        slotOff, (RAFrame.compute (vcpOf fLit) (rfOf fLit)).intBase⟩ fLit sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs fLit) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fLit) (rfOf fLit)).intBase
        (RAFrame.compute (vcpOf fLit) (rfOf fLit)).size (afOf fLit) s, syms,
        slotOff, (RAFrame.compute (vcpOf fLit) (rfOf fLit)).intBase⟩ fLit sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : (afOf fLit).slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (fbOf fLit) base ra s) (hres : StackAvail K (afOf fLit) s)
    (hbe : BodyEntry (afOf fLit) s w₀)
    (hargs : ArgsIn fLit.sig args s) (hcs : ClifEntry fLit args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute (vcpOf fLit) (rfOf fLit)).intBase
      (RAFrame.compute (vcpOf fLit) (rfOf fLit)).size (afOf fLit) s,
      syms, slotOff, (RAFrame.compute (vcpOf fLit) (rfOf fLit)).intBase⟩ fLit
        cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env { funcs := [] } cs) (fuel : Nat) :
    ArmRefinesT (fbOf fLit) base ra (ArmStepX X H (faOf fLit)) s
      (Clif.runLoop env { funcs := [] } fuel cs) :=
  backend_correct_finalTCF inSubsetTCF_lit compiledTCF_lit formsCovered_lit hC hCT hTls hX hXI hsym
    hslot hent hres hbe hargs hcs hrel htr fuel

/-- `shapeOkTF` accepts `fLit`'s lowering, and `shapeOkTS` at the check `instScopeOkF` rejects
it (the `f64const` is not `Compile.instETF`). -/
def oldDiffers (f : Clif.Function) (vc : VCode) : Bool :=
  match buildCtx f with
  | .error _ => false
  | .ok (ctx, _, st0) =>
    match lowBlocksC f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => false
    | some bl =>
      let gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))
      shapeOkTF f vc ctx st0 gn bl && !shapeOkTS (instScopeOkF ctx) f vc ctx st0 gn bl

/-- **The statement of `Driver.shapeOkTF_eq_S` before #1002 part 2 is false**: `shapeOkTF`
changed (its check is `instScopeOkFL`), and on `fLit`'s lowering it differs from `shapeOkTS` at
the old check `instScopeOkF`. -/
theorem shapeOkTF_eq_S_old_false :
    ¬ ∀ (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState) (gn : Nat → Nat)
      (bl : List BLow), shapeOkTF f vc ctx st0 gn bl = shapeOkTS (instScopeOkF ctx) f vc ctx st0 gn bl := by
  intro h
  have hd : oldDiffers fLit (FloatDriverT.vcOf fLit) = true := by native_decide
  unfold oldDiffers at hd
  split at hd
  · cases hd
  · split at hd
    · cases hd
    · simp [h] at hd

end PoolConstFinalTCF
