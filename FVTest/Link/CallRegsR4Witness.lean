import FV.Link.TypedStockShared
import FV.Link.TypedCompileModes
import FV.E2E.StockProductionFixtures
import FV.Backend.Lowering.StockArithmeticNI
import FVTest.Link.DeadCleanupWitness

/-! # Witnesses of #753 stage R4 (the typed Stock route with the register-guarded calls)

**The fixture (std's A1 shape, #753):** `%g` makes a vtable call: `call_indirect sig0` (no `sret`,
x0, x1) through a pointer loaded from its first argument (a `blr` whose register is no GOT load).
It also declares, non-colocated (called through the GOT), two functions of the program:
* `%h`, with the site's signature (x0, x1 → x0). A vtable `blr` of `%g` may enter it.
* `%s(i64 sret, i64)` (x8, x0). Its registers are not the site's.

The checks before R4 (`okRWithTS`, `okBTS`) asked the vtable site to pass its arguments in the
registers of every function of the program it may enter, `%s` included. That fails
(`callRegs/blrRegs`), so `%g` was left out. Since R4 `attemptT` checks the site for its shape. A
`blr` enters a function only with that function's registers: this is the register guard of the
world theorems, discharged from the link's declarations (`LinkSys.regCompatGotR`, `regCompatIndR`).

**Coverage of calls:** `attemptT` succeeds on the fixture's Stock placement, and `attemptT_correct`
applies to `%g` (`correct_applies`). Its conclusion is about every run of `%g`: through its vtable
`blr` into `%h`, and through its GOT call of `%s`.

**The three changed texts are false in their old form:** `attemptT_spec_old_false`,
`attempt_spec_old_false`, `attemptTFrom_stockFails_old_false`.

**Negative witnesses (#753's sret/x8 mismatch):**
* At the vtable site with `%s`'s address as the target, `%s`'s registers are not the site's
  (`¬ SiteRegsR`). So the register guard fails (`RegGuard` with `%s`'s signature at that address)
  and the guarded step is undefined there (`mismatch_guard_false`). The source semantics does not
  enter `%s` there either: `call_indirect sig0` does not `abiMatch` `%s` (`mismatch_abiMatch`), and
  CLIF's call is `stuck`.
* A GOT call whose declaration (no `sret`, x0, x1) disagrees with its definition (`sret`, x8, x0)
  fails the link check `declSig`. The typed route then rejects the program and lean-link leaves
  the caller out (`stockFailsR` names it, `mismatch_left_out`).

Decided by `native_decide` (witness only): `lake build FVTest.Link.CallRegsR4Witness`. -/

namespace E2E.CallRegsR4Witness
set_option autoImplicit false
open E2E E2E.LinkCheck Link Backend Backend.Proof Backend.Proof.Driver
open E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes
open E2E.DeadCleanupExecutableWitness (placeholder)

def srcH : String := "function %h(i64, i64) -> i64 system_v {
block0(v0: i64, v1: i64):
    v2 = iadd v0, v1
    return v2
}
"

def srcS : String := "function %s(i64 sret, i64) system_v {
block0(v0: i64, v1: i64):
    store notrap aligned v1, v0
    return
}
"

/-- The A1 shape: a vtable `call_indirect` without `sret` next to GOT calls of `%h` and of the
`sret` function `%s`. -/
def srcG : String := "function %g(i64, i64, i64) -> i64 system_v {
    ss0 = explicit_slot 8, align = 8
    sig0 = (i64, i64) -> i64 system_v
    fn0 = %s(i64 sret, i64) system_v
    fn1 = %h(i64, i64) -> i64 system_v
block0(v0: i64, v1: i64, v2: i64):
    v3 = stack_addr.i64 ss0
    call fn0(v3, v2)
    v4 = load.i64 notrap aligned readonly v0+8
    v5 = call_indirect sig0, v4(v1, v2)
    v6 = call fn1(v5, v1)
    return v6
}
"

/-- `%g` with `%s` declared without its `sret` parameter (a declaration with other registers than
the definition's). -/
def srcGBad : String := "function %g(i64, i64, i64) -> i64 system_v {
    sig0 = (i64, i64) -> i64 system_v
    fn0 = %s(i64, i64) system_v
    fn1 = %h(i64, i64) -> i64 system_v
block0(v0: i64, v1: i64, v2: i64):
    call fn0(v1, v2)
    v4 = load.i64 notrap aligned readonly v0+8
    v5 = call_indirect sig0, v4(v1, v2)
    v6 = call fn1(v5, v1)
    return v6
}
"

/-- The Stock route of the fixture. -/
def lower : ProductionLowering := Stock.Arithmetic.lowerValidated

def specOf (g : String) : LinkSpec :=
  ({ funcs := [{ clif := srcH, ra := "{}" }, { clif := srcS, ra := "{}" }, { clif := g, ra := "{}" }],
     names := [], sizes := [], outside := [], symNames := [], R := 0x1000000 } : LinkSpec).placedProductionWith
    lower true

def fileOf (S : LinkSpec) : ByteArray :=
  placeholder S.R S.size (S.addrs.map fun p => (BinCheck.symName p.1, p.2))

/-- The Stock route's placement of the fixture. -/
def spec : LinkSpec := specOf srcG
def file0 : ByteArray := fileOf spec
def input : SemanticStackBound.CompilerInput := SemanticCompilerWith.input lower spec true
/-- The route's results (`attemptTFast`'s). -/
def res : Res := spec.input0.resultsProductionWith lower true

/-- `%g`'s prepared code has a vtable `blr` site (a call through a register that no GOT load
defines) passing in x0, x1, and a GOT `blr` site. -/
def vtableSiteB : Bool :=
  input.results.any fun row => match row.2 with
    | .error _ => false
    | .ok a =>
      row.1.name == "g" && a.vcp.blocks.any fun vb => vb.insts.any fun i => match i with
        | .call info => match info.dest with
          | .reg (.vreg t _) => (E2E.gotOf a.vcp t).isNone && info.uses.map (·.2) == [.x 0, .x 1]
          | _ => false
        | _ => false

def checks : Bool :=
  vtableSiteB && !SemanticStackBound.okBTS input && SemanticStackBound.okBTSR input &&
    TypedStockShared.stockFails spec res == [("g", ["callRegs/blrRegs"])] &&
    (TypedStockShared.stockFailsR spec res).isEmpty &&
    (SemanticCompilerWith.attemptT lower spec file0).toBool &&
    (TypedStockShared.attemptTFrom spec file0 res).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem checks_true : checks = true := by native_decide -- witness: native_decide

theorem parts : vtableSiteB = true ∧ SemanticStackBound.okBTS input = false ∧
    SemanticStackBound.okBTSR input = true ∧
    TypedStockShared.stockFails spec res = [("g", ["callRegs/blrRegs"])] ∧
    (∃ file, SemanticCompilerWith.attemptT lower spec file0 = .ok file) ∧
    ∃ file, TypedStockShared.attemptTFrom spec file0 res = .ok file := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hv, hb⟩, hr⟩, hs⟩, -⟩, ha⟩, hf⟩ := h
  refine ⟨hv, hb, hr, hs, ?_, ?_⟩
  · cases e : SemanticCompilerWith.attemptT lower spec file0 with
    | error m => rw [e] at ha; cases ha
    | ok file => exact ⟨file, rfl⟩
  · cases e : TypedStockShared.attemptTFrom spec file0 res with
    | error m => rw [e] at hf; cases hf
    | ok file => exact ⟨file, rfl⟩

/-- **`attemptT_spec`'s text before R4 is false**: `attemptT` succeeds where `okBTS` fails. -/
theorem attemptT_spec_old_false : ¬ ∀ {lower : ProductionLowering} {S : LinkSpec}
    {file0 file : ByteArray}, SemanticCompilerWith.attemptT lower S file0 = .ok file →
      SemanticStackBound.okBTS (SemanticCompilerWith.input lower S true) = true ∧
      leanLinkProductionWith lower S file0 true = .ok file := by
  intro hold
  obtain ⟨-, hb, -, -, ⟨file, hf⟩, -⟩ := parts
  have := (hold hf).1
  rw [show SemanticCompilerWith.input lower spec true = input from rfl, hb] at this
  cases this

/-- **`attempt_spec`'s text before R4 is false** (`attempt … true` is `attemptT`). -/
theorem attempt_spec_old_false : ¬ ∀ {lower : ProductionLowering} {S : LinkSpec} {cleanup : Bool}
    {file0 file : ByteArray}, TypedCompilerWith.attempt lower S file0 cleanup = .ok file →
      SemanticStackBound.okBTS (SemanticCompilerWith.input lower S cleanup) = true ∧
      leanLinkProductionWith lower S file0 cleanup = .ok file := by
  intro hold
  obtain ⟨-, hb, -, -, ⟨file, hf⟩, -⟩ := parts
  rw [← TypedCompilerWith.attempt_cleanup_eq] at hf
  have := (hold hf).1
  rw [show SemanticCompilerWith.input lower spec true = input from rfl, hb] at this
  cases this

/-- **`attemptTFrom_stockFails`'s text before R4 is false**: `attemptTFrom` succeeds where the
failures of `okRWithTS` (`stockFails`) are not empty. -/
theorem attemptTFrom_stockFails_old_false : ¬ ∀ (SP : LinkSpec) (file0 : ByteArray) (R : Res),
    TypedStockShared.attemptTFrom SP file0 R = if (TypedStockShared.stockFails SP R).isEmpty then
      leanLinkWithResults SP file0 (fun _ => R) else .error SemanticCompilerWith.outOkTSMsg := by
  intro hold
  obtain ⟨-, -, -, hs, -, ⟨file, hf⟩⟩ := parts
  have := hold spec file0 res
  rw [hf, hs] at this
  cases this

/-- **`attemptT_correct` applies to `%g`**, a function with a vtable `blr` next to GOT calls of
a function with its registers (`%h`) and of one with others (`%s`): every run of `%g`, through
its calls, is refined by the executable's. -/
theorem correct_applies : ∃ file g,
    SemanticCompilerWith.attemptT lower spec file0 = .ok file ∧
    (prog input).func? "g" = some g ∧
    ∀ (B : BaseEnv), BaseOk (sys input B) → HooksSim input B →
    ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls input input.results) g →
    ∀ (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State},
    (imageOf file).Intact r →
    OutsideCall input (BinCheck.roByte input spec.data) g
      (SemanticStackBound.stackFn input g) r args cs.mem →
    ClifRun input B g r args cs →
    TrapsExplicit (Clif.linkEnvN (prog input) B.env M) (prog input).bare cs →
    ExecBytes.ExecRefinesT (art input g).fb (art input g).base (xreg 30 r) (step input B file) r
      (RelocAtWithResults input input.results) (Clif.runLoop B.env (prog input) (M + 1) cs) := by
  obtain ⟨-, -, -, -, ⟨file, hf⟩, -⟩ := parts
  cases eg : (prog input).func? "g" with
  | none =>
    have : ((prog input).func? "g").isSome = true := by native_decide -- witness: native_decide
    rw [eg] at this; cases this
  | some g =>
    exact ⟨file, g, hf, eg, fun B hB hH hc M r args cs hX ho hr htr =>
      SemanticCompilerWith.attemptT_correct hf B hB hH eg hc M hX ho hr htr⟩

/-! ## Negative witnesses: the sret/x8 mismatch -/

/-- The vtable site's signature `sig0` and `%s`'s. -/
def sig0 : Clif.Signature :=
  { params := [{ ty := .i64 }, { ty := .i64 }], returns := [{ ty := .i64 }], callConv := some .systemV }
def sigS : Clif.Signature :=
  { params := [{ ty := .i64, purpose := .sret }, { ty := .i64 }], returns := [], callConv := some .systemV }

/-- `%s`'s parsed signature is `sigS`, and `%g`'s vtable site's is `sig0`. -/
theorem sigs_parsed : ((prog input).func? "s").map (·.sig) = some sigS ∧
    sig0 ∈ indSigs (((prog input).func? "g").getD default) := by
  constructor <;> native_decide -- witness: native_decide

/-- The site's registers: arguments in x0, x1 (`regLocs sig0`), result from x0. -/
def siteUses : List (Reg × Reg) := [(.vreg 0 .int, .x 0), (.vreg 1 .int, .x 1)]
def siteDefs : List (Reg × Reg) := [(.x 0, .vreg 2 .int)]

/-- **`%s`'s registers are not the site's** (x8, x0 against x0, x1). -/
theorem mismatch_regs : regLocs sigS = [.x 8, .x 0] ∧ regLocs sig0 = [.x 0, .x 1] ∧
    ¬ SiteRegsR sigS siteUses siteDefs ∧ SiteRegsR sig0 siteUses siteDefs := by
  refine ⟨by native_decide, by native_decide, fun h => absurd h.1 (by native_decide), -- witness: native_decide
    show _ ∧ _ from ⟨by native_decide, by native_decide⟩⟩ -- witness: native_decide

/-- **The register guard fails at the vtable site when the target is `%s`'s address**: for any
guard predicate `P` placing `%s`'s signature at the target, the step of the guarded semantics is
undefined (`regG`), whatever the base semantics. -/
theorem mismatch_guard_false {P : BitVec 64 → Clif.Signature → Prop} {u : CV} (us : List CV)
    (hP : P (lo64 u) sigS) {W : Type} (sem : ISem CV W) (w : W) :
    ¬ RegGuard P ⟨.reg (.vreg 3 .int), siteUses, siteDefs⟩ (u :: us) ∧
      regG P sem (.call ⟨.reg (.vreg 3 .int), siteUses, siteDefs⟩) (u :: us) w = none := by
  have hg : ¬ RegGuard P ⟨.reg (.vreg 3 .int), siteUses, siteDefs⟩ (u :: us) :=
    fun h => mismatch_regs.2.2.1 (h (.vreg 3 .int) u rfl rfl sigS hP)
  exact ⟨hg, by simp [regG, RegGuardI, hg]⟩

/-- **The source semantics does not enter `%s` from the site either**: `sig0` does not `abiMatch`
`sigS` (a `call_indirect` of a function of the program whose signature does not match is
`stuck`, `Clif.stepCallIndirect`), and the two have different registers (`SigRegsEq`). -/
theorem mismatch_abiMatch : sig0.abiMatch sigS = false ∧ ¬ SigRegsEq sigS sig0 := by
  exact ⟨by native_decide, fun h => absurd h.1 (by native_decide)⟩ -- witness: native_decide

def specBad : LinkSpec := specOf srcGBad
def fileBad : ByteArray := fileOf specBad
def resBad : Res := specBad.input0.resultsProductionWith lower true

def checksBad : Bool :=
  !(SemanticCompilerWith.attemptT lower specBad fileBad).toBool &&
    (TypedStockShared.stockFailsR specBad resBad).any fun e => e.1 == "g" && e.2.contains "declSig"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem checksBad_true : checksBad = true := by native_decide -- witness: native_decide

/-- **A GOT callee declared with other registers than its definition's is left out**: the typed
route fails (`attemptT` errs), and its failures (`stockFailsR`, what lean-link leaves out) name
`%g` with `declSig`. -/
theorem mismatch_left_out : (∃ m, SemanticCompilerWith.attemptT lower specBad fileBad = .error m) ∧
    ∃ e ∈ TypedStockShared.stockFailsR specBad resBad, e.1 = "g" ∧ "declSig" ∈ e.2 := by
  have h := checksBad_true
  simp only [checksBad, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, beq_iff_eq,
    List.contains_iff_mem] at h
  obtain ⟨ha, e, he, hn, hd⟩ := h
  refine ⟨?_, e, he, hn, hd⟩
  cases r : SemanticCompilerWith.attemptT lower specBad fileBad with
  | error m => exact ⟨m, rfl⟩
  | ok f => rw [r] at ha; cases ha

end E2E.CallRegsR4Witness
