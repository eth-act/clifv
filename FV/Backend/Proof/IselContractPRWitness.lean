import FV.Backend.Proof.IselCtlCallPR
import FV.Backend.Proof.IselCtlCallTPR
import FV.Backend.Proof.IselCtlCallTFPR

/-!
# Witnesses for the call contracts with registers (#753, stage R1)

* The #753 shape on concrete signatures: k256's `try_call_indirect` site `(i64, i64) -> i64`
  passes its arguments in x0, x1; the functions its caller declares through the GOT have
  `(i64 sret, i64)`, whose registers are x8, x0 (`regLocs_sigSret`); the two signatures do not
  `abiMatch` (`abiMatch_sigPlain_sigSret`), so the CLIF semantics enters no such function from
  that site, and a site with the registers of its own signature (`SiteRegsR`) has not those of the
  GOT callee.
* `regLocs_of_abiMatch` on signatures that differ in an extension flag only.
* `siteRegsR_int` on a concrete emitted `call` of the `sret` signature.
* The program families with registers give the existing ones (`…_via_PR`), so the rule theorems
  of `IselCtlCallPR`, `IselCtlCallTPR` and `IselCtlCallTFPR` are not weaker than those of
  `IselCtl`, `IselCtlCallTI` and `IselCtlCallF`.
-/

namespace Backend.Proof.IselContractPRWitness

open Backend Backend.Proof Isle.Aarch64

set_option autoImplicit false

/-- `(i64 sret, i64)`: the struct pointer in x8, the next argument in x0. -/
def sigSret : Clif.Signature := { params := [{ ty := .i64, purpose := .sret }, { ty := .i64 }] }

/-- `(i64, i64) -> i64`. -/
def sigPlain : Clif.Signature :=
  { params := [{ ty := .i64 }, { ty := .i64 }], returns := [{ ty := .i64 }] }

theorem regLocs_sigSret : E2E.regLocs sigSret = [.x 8, .x 0] := by decide

theorem regLocs_sigPlain : E2E.regLocs sigPlain = [.x 0, .x 1] := by decide

theorem abiMatch_sigPlain_sigSret : sigPlain.abiMatch sigSret = false := by decide

/-- A site with the registers of `(i64, i64) -> i64` has not those of `(i64 sret, i64)`. -/
theorem siteRegsR_sigPlain_not_sigSret {us ds : List (Reg × Reg)}
    (h : SiteRegsR sigPlain us ds) : ¬ SiteRegsR sigSret us ds := fun h' => by
  have := h.1.symm.trans h'.1
  rw [regLocs_sigPlain, regLocs_sigSret] at this
  cases this

/-- `(i32 uext)`. -/
def sigUext : Clif.Signature := { params := [{ ty := .i32, ext := .uext }] }

/-- `(i32)`. -/
def sigI32 : Clif.Signature := { params := [{ ty := .i32 }] }

theorem regLocs_sigUext_sigI32 : E2E.regLocs sigUext = E2E.regLocs sigI32 :=
  regLocs_of_abiMatch (by decide)

theorem sigArgLocs_sigSret : sigArgLocs sigSret = .ok ([.reg (.x 8), .reg (.x 0)], 0) := by
  rfl

theorem sigParamBytes_sigSret : sigParamBytes sigSret = .ok [8, 8] := by decide

/-- The call the lowering emits for `(i64 sret, i64)` on the values 5, 6 has the signature's
registers. -/
theorem siteRegsR_sigSret_call :
    SiteRegsR sigSret (retPairs (regPairsOf (([.reg (.x 8), .reg (.x 0)].zip [5, 6]).zip [8, 8])))
      (callDefs (outDefs 7 0)) :=
  siteRegsR_int sigArgLocs_sigSret sigParamBytes_sigSret rfl (by decide) 7 (Nat.le_refl _)

set_option maxRecDepth 100000

theorem callRulesCorrectP_via_PR : CallRulesCorrectP program :=
  callRulesCorrectP_of_PR callRulesCorrectPR

theorem indRulesCorrectP_via_PR : IndRulesCorrectP program :=
  indRulesCorrectP_of_PR indRulesCorrectPR

theorem tryRulesCorrectP_via_PR : TryRulesCorrectP program :=
  tryRulesCorrectP_of_PR tryRulesCorrectPR

theorem tryIndRulesCorrectP_via_PR : TryIndRulesCorrectP program :=
  tryIndRulesCorrectP_of_PR tryIndRulesCorrectPR

theorem callRulesCorrectTP_via_PR : CallRulesCorrectTP program :=
  callRulesCorrectTP_of_PR callRulesCorrectTPR_program

theorem indRulesCorrectTP_via_PR : IndRulesCorrectTP program :=
  indRulesCorrectTP_of_PR indRulesCorrectTPR_program

theorem tryRulesCorrectTP_via_PR : TryRulesCorrectTP program :=
  tryRulesCorrectTP_of_PR tryRulesCorrectTPR_program

theorem tryIndRulesCorrectTP_via_PR : TryIndRulesCorrectTP program :=
  tryIndRulesCorrectTP_of_PR tryIndRulesCorrectTPR_program

theorem callRulesCorrectTFP_via_PR : CallRulesCorrectTFP program :=
  callRulesCorrectTFP_of_PR callRulesCorrectTFPR_program

theorem tryRulesCorrectTFP_via_PR : TryRulesCorrectTFP program :=
  tryRulesCorrectTFP_of_PR tryRulesCorrectTFPR_program

end Backend.Proof.IselContractPRWitness
