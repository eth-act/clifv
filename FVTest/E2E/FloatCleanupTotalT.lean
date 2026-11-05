import FVTest.E2E.FloatTotalT
import FV.E2E.LinkScopeInputCleanupT

/-!
Non-vacuity of the dead-cleanup pipeline's per-function totality on the typed input scope
(S11e5 Stage C, slice 8), on `FloatTotalT`'s `fW` (float `load`, `f64const`, `select`, `store`,
`bitcast`; outside subset E) and the crates `crateW`/`crateInt`:

* the transfer lemmas on `fW`'s prepared code (`preparedCleanup_formsCovered`,
  `preparedCleanup_ctlInsts`, `preparedCleanup_emitCondsB`, `spillAccepted_cleanupT`) and
  `backend_total_emit_cleanupT` (any allocator answer);
* `pipeCleanupT_okT` on `fW`, `resultsCleanupT_ok_inT` on `crateW`, `resultsCleanupT_ok_input`
  on the integer `crateInt`.
Checks by `native_decide` (witness only). `lake build FVTest.E2E.FloatCleanupTotalT`.
-/

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.DeadCleanup E2E
  E2E.LinkCheck

namespace FloatCleanupTotalT

open FloatDriverT FloatFinalT FloatLinkT FloatTotalT

/-- `fW`'s cleaned prepared code. -/
abbrev cleanW : VCode := preparedCleanup (vcOf fW) (vcpOf fW)

theorem prune_prepare_w : Backend.prepare (prune (vcOf fW)) = .ok cleanW := prune_prepare_ok prepare_w

theorem cfg_w : ∃ ss ps, (vcpOf fW).cfg = .ok (ss, ps) :=
  cfg_ok_of_prepare prepare_w (prepDomain_ofT dominated_w lowerScopeT_w lowerFunction_w)

/-- **Witness**: the transfer lemmas on `fW`'s cleaned code. -/
theorem formsCovered_clean_w : FormsCovered default cleanW :=
  preparedCleanup_formsCovered FloatTotalT.formsCovered_w
theorem ctlInsts_clean_w : CtlInsts cleanW := preparedCleanup_ctlInsts ctlInsts_w
theorem emitCondsB_clean_w : emitCondsB cleanW = true :=
  let ⟨_, _, hc⟩ := cfg_w
  preparedCleanup_emitCondsB hc emitCondsB_w

theorem spillAccepted_clean_w : AllocChecked cleanW (spillAlloc cleanW) :=
  spillAccepted_cleanupT dominated_w lowerScopeT_w arity_w tryArg_w resClass_w lowerFunction_w
    prepare_w ctlSpill_w FloatTotalT.formsCovered_w killFreeB_w

/-- **Witness**: allocation, emission and layout of `fW`'s cleaned code succeed by the theorem,
with any allocator answer. -/
theorem backend_total_emit_cleanupT_w (ra : Except String RFunc) :
    AllocChecked cleanW (allocResult cleanW (readyAnswer cleanW ra)) ∧
    ∃ af, lowerAllocReady cleanW ra = .ok af ∧ ∃ fa fb, emitFunc 0 af = .ok fa ∧ fa.layout = .ok fb :=
  backend_total_emit_cleanupT dominated_w lowerScopeT_w arity_w tryArg_w resClass_w
    lowerFunction_w prepare_w ctlSpill_w FloatTotalT.formsCovered_w killFreeB_w ctlInsts_w
    emitCondsB_w ra 0

/-- **Witness**: the cleanup pipeline compiles `fW`, for every allocator answer. -/
theorem pipeCleanupT_okT_w (o : Lean.Json) :
    ∃ a, pipeCleanupT fW 0 0 o = .ok a ∧ lowerCheckT fW a.vc = true ∧
      prepCheck (cleanupStage fW a.vc) a.vcp = true ∧ AllocChecked a.vcp a.rf ∧
      FormsCovered ⟨a.fa.k, a.af.slotBase⟩ a.vcp :=
  pipeCleanupT_okT fnScopeInTB_w 0 0 o

/-- **Witness** (subset E): the cleanup pipeline compiles `fInt` through the integer branch. -/
theorem pipeCleanupT_okT_int (o : Lean.Json) : ∃ a, pipeCleanupT fInt 0 0 o = .ok a :=
  let ⟨a, ha, _⟩ := pipeCleanupT_okT fnScopeInTB_int 0 0 o
  ⟨a, ha⟩

/-- **Witness**: every function of the float crate compiles with cleanup. -/
theorem resultsCleanupT_ok_inT_w : crateW.resultsCleanupT.all (·.2.toBool) = true :=
  resultsCleanupT_ok_inT inScopeInT_w

/-- **Witness** (integer): the integer crate compiles with cleanup. -/
theorem resultsCleanupT_ok_input_int : crateInt.resultsCleanupT.all (·.2.toBool) = true :=
  resultsCleanupT_ok_input inScopeIn_int

end FloatCleanupTotalT
