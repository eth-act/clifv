import FV.Backend.ReturnPinProduction

/-!
# The Stock path's validator implies `SemanticABI.checkCalls` (#1101)

`lean-backend`'s Stock path (`compileFileReturnPinWhen true`, `FVTest/Backend/Main.lean`) names
`E2E.backend_correct_world_niX_semantic_return_pins` with the artifact
`E2E.CompiledSemanticReturnPins.of_checks_calls`, whose first premise is
`SemanticABI.checkCalls f vc = true` for the raw lowering `vc` the allocated code is the cleanup
stage `Stock.Arithmetic.stageF cleanup f vc` of. This module proves it from the compiler's own
runs instead of reading it from the code:

* `lowerCheckedX_checkCalls`: every per-function wrapper the file driver reaches accepts a lowering
  with `verify = true` only when `SemanticABI.checkCalls` accepts it (subset E, `Compile.functionE`:
  the legacy fallback `lowerChecked` validates with `lowerCheck` there), each by the next one's;
* `lowerForAllocationX_callsRoute`: the code the file driver hands the allocator for such a
  lowering is `stageF cleanup f vc` of a `vc` that `checkCalls` accepts (`CallsRoute`);
* `compileFileReturnPinWhen_runsRoutes`: the Stock file driver only runs
  `compileFileWithLowering L` for those 23 lowerings `L` (`RunsRoutes`), in any monad;
* `compileFileReturnPinWhen_checkCalls`: in `lean-backend`'s monad (`IO` is an `EStateM`), a
  function the driver reports compiled, neither unverified nor unvalidated, was lowered by one of
  those lowerings with verification on, and the code the allocator received for it is the stage
  of a `checkCalls`-accepted lowering.
-/

namespace Backend
set_option autoImplicit false

/-! ## The per-function wrappers -/

/-- The validated attempt every route wrapper starts with accepts only what its validator accepts. -/
theorem attempt_ok {lower : Except String VCode} {chk : VCode → Bool} {msg : String} {v : VCode}
    (h : (do
        let vc ← lower
        if true && !chk vc then
          throw msg
        pure vc : Except String VCode) = .ok v) : chk v = true := by
  cases hl : lower with
  | error e => simp [hl, bind, Except.bind] at h
  | ok w =>
    cases hc : chk w
    · simp [hl, hc, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    · simp only [hl, hc, bind, Except.bind, Bool.true_and, Bool.not_true, Bool.false_eq_true,
        ite_false, pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ hc

theorem checkCalls_of_lowerCheck {f : Clif.Function} {vc : VCode}
    (h : Proof.Driver.lowerCheck f vc = true) : SemanticABI.checkCalls f vc = true :=
  SemanticABI.previous_check_calls (SemanticABI.previous_check (by simp [SemanticNI.check, h]))

theorem checkCalls_of_semanticNI {f : Clif.Function} {vc : VCode}
    (h : SemanticNI.check f vc = true) : SemanticABI.checkCalls f vc = true :=
  SemanticABI.previous_check_calls (SemanticABI.previous_check h)

variable {f : Clif.Function} {vc : VCode}

theorem lowerChecked_checkCalls (hE : Compile.functionE f = true)
    (h : lowerChecked f true = .ok vc) : SemanticABI.checkCalls f vc = true :=
  checkCalls_of_lowerCheck (lowerChecked_lowerCheck h hE)

/-- `lowerCheckedProduction_lowerCheck` for the parameterised wrapper. -/
theorem lowerCheckedProductionWith_lowerCheck {lower : Clif.Function → Except String VCode}
    (h : lowerCheckedProductionWith lower f true = .ok vc) (hE : Compile.functionE f = true) :
    Proof.Driver.lowerCheck f vc = true := by
  unfold lowerCheckedProductionWith at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact attempt_ok hv
  · exact lowerChecked_lowerCheck h hE

theorem lowerCheckedProductionWith_checkCalls {lower : Clif.Function → Except String VCode}
    (hE : Compile.functionE f = true) (h : lowerCheckedProductionWith lower f true = .ok vc) :
    SemanticABI.checkCalls f vc = true :=
  checkCalls_of_lowerCheck (lowerCheckedProductionWith_lowerCheck h hE)

theorem lowerCheckedArithmeticNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedArithmeticNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedArithmeticNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedProductionWith_checkCalls hE h

theorem lowerCheckedMixedNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedMixedNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedMixedNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedArithmeticNI_checkCalls hE h

theorem lowerCheckedLogicalNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedLogicalNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedLogicalNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedMixedNI_checkCalls hE h

theorem lowerCheckedScalarNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedScalarNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedScalarNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedLogicalNI_checkCalls hE h

theorem lowerCheckedTwoBlockNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedTwoBlockNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedTwoBlockNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedScalarNI_checkCalls hE h

theorem lowerCheckedTwoBlockEntryNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedTwoBlockEntryNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedTwoBlockEntryNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedTwoBlockNI_checkCalls hE h

theorem lowerCheckedLinearCfgNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedLinearCfgNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedLinearCfgNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedTwoBlockEntryNI_checkCalls hE h

theorem lowerCheckedForwardCfgNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedForwardCfgNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedForwardCfgNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedLinearCfgNI_checkCalls hE h

theorem lowerCheckedConditionalCfgNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedConditionalCfgNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedConditionalCfgNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedForwardCfgNI_checkCalls hE h

theorem lowerCheckedConditionalForwardCfgNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedConditionalForwardCfgNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedConditionalForwardCfgNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedConditionalCfgNI_checkCalls hE h

theorem lowerCheckedParameterCfgNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedParameterCfgNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedParameterCfgNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedConditionalForwardCfgNI_checkCalls hE h

theorem lowerCheckedMemoryNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedMemoryNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedMemoryNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedParameterCfgNI_checkCalls hE h

theorem lowerCheckedMemoryCfgNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedMemoryCfgNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedMemoryCfgNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedMemoryNI_checkCalls hE h

theorem lowerCheckedMemoryIntegerNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedMemoryIntegerNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedMemoryIntegerNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedMemoryCfgNI_checkCalls hE h

theorem lowerCheckedMemoryExtLoadNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedMemoryExtLoadNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedMemoryExtLoadNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedMemoryIntegerNI_checkCalls hE h

theorem lowerCheckedMemoryStoreNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedMemoryStoreNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedMemoryStoreNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedMemoryExtLoadNI_checkCalls hE h

theorem lowerCheckedMemoryStoreCfgNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedMemoryStoreCfgNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedMemoryStoreCfgNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedMemoryStoreNI_checkCalls hE h

theorem lowerCheckedMemoryLoadStoreNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedMemoryLoadStoreNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedMemoryLoadStoreNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedMemoryStoreCfgNI_checkCalls hE h

theorem lowerCheckedMemoryCapturedCopyNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedMemoryCapturedCopyNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedMemoryCapturedCopyNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedMemoryLoadStoreNI_checkCalls hE h

theorem lowerCheckedMemorySinkExtNI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedMemorySinkExtNI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedMemorySinkExtNI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact checkCalls_of_semanticNI (attempt_ok hv)
  · exact lowerCheckedMemoryCapturedCopyNI_checkCalls hE h

theorem lowerCheckedVoidCallABI_checkCalls (hE : Compile.functionE f = true)
    (h : lowerCheckedVoidCallABI f true = .ok vc) : SemanticABI.checkCalls f vc = true := by
  unfold lowerCheckedVoidCallABI at h
  dsimp only at h
  split at h
  · rename_i v hv
    cases h
    exact attempt_ok hv
  · exact lowerCheckedMemorySinkExtNI_checkCalls hE h

/-! ## What the allocator receives -/

/-- A lowering of the file driver (`compileFileWithLowering`'s `lower`) whose output with
verification on, for a function of subset E, is the cleanup stage `Stock.Arithmetic.stageF` (the
stage `CompiledSemanticReturnPins.of_checks_calls` prepares) of a raw lowering that
`SemanticABI.checkCalls` accepts. -/
def CallsRoute (L : Clif.Function → Bool → Bool → Except String VCode) : Prop :=
  ∀ {f : Clif.Function} {cleanup : Bool} {code : VCode}, Compile.functionE f = true →
    L f true cleanup = .ok code →
      ∃ vc, SemanticABI.checkCalls f vc = true ∧ code = Stock.Arithmetic.stageF cleanup f vc

/-- A Stock route: its wrapper's lowering, then `stageV`. -/
theorem callsRoute_stageV {lc : Clif.Function → Bool → Except String VCode}
    (calls : ∀ {f : Clif.Function} {vc : VCode}, Compile.functionE f = true → lc f true = .ok vc →
      SemanticABI.checkCalls f vc = true) :
    CallsRoute fun f verify cleanup => (lc f verify).map (Stock.Arithmetic.stageV verify cleanup f) := by
  intro f cleanup code hE h
  cases hl : lc f true with
  | error e => simp [hl, Except.map] at h
  | ok vc =>
    simp only [hl, Except.map, Except.ok.injEq] at h
    exact ⟨vc, calls hE hl, h ▸ Stock.Arithmetic.stageV_true cleanup f vc⟩

theorem lowerForAllocation_callsRoute : CallsRoute lowerForAllocation := by
  intro f cleanup code hE h
  rw [lowerForAllocation_verified] at h
  cases hl : lowerChecked f true with
  | error e => simp [hl, Except.map] at h
  | ok vc =>
    simp only [hl, Except.map, Except.ok.injEq] at h
    exact ⟨vc, lowerChecked_checkCalls hE hl, h.symm⟩

theorem lowerForAllocationProductionWith_callsRoute (lower : Clif.Function → Except String VCode) :
    CallsRoute (lowerForAllocationProductionWith lower) := by
  intro f cleanup code hE h
  unfold lowerForAllocationProductionWith at h
  cases hl : lowerCheckedProductionWith lower f true with
  | error e => simp [hl, Except.map] at h
  | ok vc =>
    simp only [hl, Except.map, Except.ok.injEq] at h
    refine ⟨vc, lowerCheckedProductionWith_checkCalls hE hl, ?_⟩
    rw [← h, cleanupStageChecked_true (fun _ => lowerCheckedProductionWith_lowerCheck hl hE)]
    rfl

theorem lowerForAllocationArithmeticNI_callsRoute : CallsRoute lowerForAllocationArithmeticNI :=
  callsRoute_stageV lowerCheckedArithmeticNI_checkCalls
theorem lowerForAllocationMixedNI_callsRoute : CallsRoute lowerForAllocationMixedNI :=
  callsRoute_stageV lowerCheckedMixedNI_checkCalls
theorem lowerForAllocationLogicalNI_callsRoute : CallsRoute lowerForAllocationLogicalNI :=
  callsRoute_stageV lowerCheckedLogicalNI_checkCalls
theorem lowerForAllocationScalarNI_callsRoute : CallsRoute lowerForAllocationScalarNI :=
  callsRoute_stageV lowerCheckedScalarNI_checkCalls
theorem lowerForAllocationTwoBlockNI_callsRoute : CallsRoute lowerForAllocationTwoBlockNI :=
  callsRoute_stageV lowerCheckedTwoBlockNI_checkCalls
theorem lowerForAllocationTwoBlockEntryNI_callsRoute : CallsRoute lowerForAllocationTwoBlockEntryNI :=
  callsRoute_stageV lowerCheckedTwoBlockEntryNI_checkCalls
theorem lowerForAllocationLinearCfgNI_callsRoute : CallsRoute lowerForAllocationLinearCfgNI :=
  callsRoute_stageV lowerCheckedLinearCfgNI_checkCalls
theorem lowerForAllocationForwardCfgNI_callsRoute : CallsRoute lowerForAllocationForwardCfgNI :=
  callsRoute_stageV lowerCheckedForwardCfgNI_checkCalls
theorem lowerForAllocationConditionalCfgNI_callsRoute : CallsRoute lowerForAllocationConditionalCfgNI :=
  callsRoute_stageV lowerCheckedConditionalCfgNI_checkCalls
theorem lowerForAllocationConditionalForwardCfgNI_callsRoute :
    CallsRoute lowerForAllocationConditionalForwardCfgNI :=
  callsRoute_stageV lowerCheckedConditionalForwardCfgNI_checkCalls
theorem lowerForAllocationParameterCfgNI_callsRoute : CallsRoute lowerForAllocationParameterCfgNI :=
  callsRoute_stageV lowerCheckedParameterCfgNI_checkCalls
theorem lowerForAllocationMemoryNI_callsRoute : CallsRoute lowerForAllocationMemoryNI :=
  callsRoute_stageV lowerCheckedMemoryNI_checkCalls
theorem lowerForAllocationMemoryCfgNI_callsRoute : CallsRoute lowerForAllocationMemoryCfgNI :=
  callsRoute_stageV lowerCheckedMemoryCfgNI_checkCalls
theorem lowerForAllocationMemoryIntegerNI_callsRoute : CallsRoute lowerForAllocationMemoryIntegerNI :=
  callsRoute_stageV lowerCheckedMemoryIntegerNI_checkCalls
theorem lowerForAllocationMemoryExtLoadNI_callsRoute : CallsRoute lowerForAllocationMemoryExtLoadNI :=
  callsRoute_stageV lowerCheckedMemoryExtLoadNI_checkCalls
theorem lowerForAllocationMemoryStoreNI_callsRoute : CallsRoute lowerForAllocationMemoryStoreNI :=
  callsRoute_stageV lowerCheckedMemoryStoreNI_checkCalls
theorem lowerForAllocationMemoryStoreCfgNI_callsRoute : CallsRoute lowerForAllocationMemoryStoreCfgNI :=
  callsRoute_stageV lowerCheckedMemoryStoreCfgNI_checkCalls
theorem lowerForAllocationMemoryLoadStoreNI_callsRoute : CallsRoute lowerForAllocationMemoryLoadStoreNI :=
  callsRoute_stageV lowerCheckedMemoryLoadStoreNI_checkCalls
theorem lowerForAllocationMemoryCapturedCopyNI_callsRoute :
    CallsRoute lowerForAllocationMemoryCapturedCopyNI :=
  callsRoute_stageV lowerCheckedMemoryCapturedCopyNI_checkCalls
theorem lowerForAllocationMemorySinkExtNI_callsRoute : CallsRoute lowerForAllocationMemorySinkExtNI :=
  callsRoute_stageV lowerCheckedMemorySinkExtNI_checkCalls
theorem lowerForAllocationVoidCallABI_callsRoute : CallsRoute lowerForAllocationVoidCallABI :=
  callsRoute_stageV lowerCheckedVoidCallABI_checkCalls

/-- `compileFileWithLowering`'s `verify` argument for the function `f` named `name`. -/
def verifyOf (pre : List (String × String)) (name : String) (f : Clif.Function) : Bool :=
  !((unverifiedReason? f).isSome || (pre.lookup name).isSome || (overBudget? f).isSome)

/-- `compileFileWithLowering`'s per-function lowering, in file order. -/
def loweredOf {code : Type} (lower : Clif.Function → Bool → Bool → Except String code)
    (pf : Clif.ParsedFile) (pre : List (String × String)) (cleanup : Bool) :
    Array (String × Except String (Clif.Function × code)) :=
  pf.funcs.toArray.map fun p => (p.name, match p.func with
    | .error e => .error e.toString
    | .ok f => (lower f (verifyOf pre p.name f) cleanup).map (f, ·))

/-- **The allocator receives the lowered code** of `loweredOf`, once, before anything else runs:
the code of a function `f` named `name` is `lower f (verifyOf pre name f) cleanup`'s. -/
theorem compileFileWithLowering_alloc {code : Type} {m : Type → Type} [Monad m]
    (lower : Clif.Function → Bool → Bool → Except String code) (rulesOf : code → Array Isle.RuleId)
    (alloc : Array code → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (pre : List (String × String)) (cleanup : Bool) :
    ∃ rest, compileFileWithLowering lower rulesOf alloc pf pre cleanup =
      alloc ((loweredOf lower pf pre cleanup).filterMap fun e => e.2.toOption.map (·.2)) >>= rest :=
  ⟨_, rfl⟩

theorem mem_loweredOf {code : Type} {lower : Clif.Function → Bool → Bool → Except String code}
    {pf : Clif.ParsedFile} {pre : List (String × String)} {cleanup : Bool} {p : Clif.ParsedFunction}
    {f : Clif.Function} (hp : p ∈ pf.funcs) (hf : p.func = .ok f) :
    (p.name, (lower f (verifyOf pre p.name f) cleanup).map (f, ·)) ∈ (loweredOf lower pf pre cleanup).toList := by
  simp only [loweredOf, Array.toList_map, List.mem_map]
  exact ⟨p, by simpa using hp, by simp [hf]⟩

/-! ## The runs of the file driver -/

/-- A monad whose runs return values (`Ret x a`: a run of `x` returns `a`): a run of `pure a`
returns `a`, and a run of `x >>= f` returns what a run of `f a` returns, for an `a` some run of
`x` returns. `lean-backend` runs the file driver in `IO` (`EIO IO.Error`, an `EST`; instance
below): there `Ret x a` says that `x`, run from some state, ends with `.ok a`. -/
class RunsReturn (m : Type → Type) [Monad m] where
  Ret {α : Type} : m α → α → Prop
  ret_pure {α : Type} {a b : α} : Ret (pure a) b → b = a
  ret_bind {α β : Type} {x : m α} {f : α → m β} {b : β} : Ret (x >>= f) b → ∃ a, Ret x a ∧ Ret (f a) b

instance : RunsReturn Id where
  Ret x a := x.run = a
  ret_pure h := h.symm
  ret_bind h := ⟨_, rfl, h⟩

instance (ε σ : Type) : RunsReturn (EST ε σ) where
  Ret x a := ∃ s s', x s = .ok a s'
  ret_pure := by
    rintro α a b ⟨s, s', h⟩
    cases h
    rfl
  ret_bind := by
    rintro α β x f b ⟨s, s', h⟩
    change EST.bind x f s = _ at h
    unfold EST.bind at h
    split at h
    · rename_i a s₁ hx
      exact ⟨a, ⟨s, s₁, hx⟩, ⟨s₁, s', h⟩⟩
    · cases h

/-- `IO`'s instance: `lean-backend`'s monad. -/
instance (ε : Type) : RunsReturn (EIO ε) where
  Ret x a := ∃ s s', x s = .ok a s'
  ret_pure := by
    rintro α a b ⟨s, s', h⟩
    cases h
    rfl
  ret_bind := by
    rintro α β x f b ⟨s, s', h⟩
    change EST.bind x f s = _ at h
    unfold EST.bind at h
    split at h
    · rename_i a s₁ hx
      exact ⟨a, ⟨s, s₁, hx⟩, ⟨s₁, s', h⟩⟩
    · cases h

section Runs
variable {m : Type → Type} [Monad m] (alloc : Array VCode → m (Array (Except String AFunc)))
  (pf : Clif.ParsedFile) (pre : List (String × String)) (cleanup : Bool)

/-- The file drivers built from `compileFileWithLowering L` runs of lowerings `L` with
`CallsRoute L`: one run, a run retried with another driver when it fails (`unsupported`
functions or a failed layout), and a choice between two drivers. -/
inductive RunsRoutes : m FileAsm → Prop where
  | attempt {L : Clif.Function → Bool → Bool → Except String VCode} : CallsRoute L →
      RunsRoutes (compileFileWithLowering L VCode.rulesFired alloc pf pre cleanup)
  | retry {L : Clif.Function → Bool → Bool → Except String VCode} {next : m FileAsm} : CallsRoute L →
      RunsRoutes next →
      RunsRoutes (compileFileWithLowering L VCode.rulesFired alloc pf pre cleanup >>= fun attempt =>
        if (!attempt.unsupported.isEmpty || !attempt.layout.isOk) = true then next else pure attempt)
  | cond {b : Bool} {x y : m FileAsm} : RunsRoutes x → RunsRoutes y →
      RunsRoutes (if b = true then x else y)

variable {alloc pf pre cleanup}

/-- **A run of such a driver returns what a run of `compileFileWithLowering L` returns**, for an
`L` with `CallsRoute L`. -/
theorem RunsRoutes.ret [RunsReturn m] {x : m FileAsm} (h : RunsRoutes alloc pf pre cleanup x)
    {fa : FileAsm} (run : RunsReturn.Ret x fa) :
    ∃ L, CallsRoute L ∧ RunsReturn.Ret (compileFileWithLowering L VCode.rulesFired alloc pf pre cleanup) fa := by
  induction h with
  | attempt hL => exact ⟨_, hL, run⟩
  | retry hL _ ih =>
    obtain ⟨a, ran, rest⟩ := RunsReturn.ret_bind run
    split at rest
    · exact ih rest
    · exact RunsReturn.ret_pure rest ▸ ⟨_, hL, ran⟩
  | cond _ _ ihx ihy =>
    split at run
    · exact ihx run
    · exact ihy run

/-- One Stock wrapper `compileFileXWhen`: disabled, the previous wrapper disabled; no eligible
function, the previous wrapper; else its route, retried with the previous wrapper. -/
theorem RunsRoutes.wrapper {L : Clif.Function → Bool → Bool → Except String VCode}
    {prev : Bool → m FileAsm} (hL : CallsRoute L)
    (hprev : ∀ e, RunsRoutes alloc pf pre cleanup (prev e)) (enabled eligible : Bool) :
    RunsRoutes alloc pf pre cleanup
      (if (!enabled) = true then prev false
      else if (!eligible) = true then prev true
      else compileFileWithLowering L VCode.rulesFired alloc pf pre cleanup >>= fun attempt =>
        if (!attempt.unsupported.isEmpty || !attempt.layout.isOk) = true then prev true
        else pure attempt) :=
  .cond (hprev false) (.cond (hprev true) (.retry hL (hprev true)))

theorem compileFileWith_runsRoutes :
    RunsRoutes alloc pf pre cleanup (compileFileWith alloc pf pre cleanup) :=
  .attempt lowerForAllocation_callsRoute

theorem compileFileScalarWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileScalarWhen enabled alloc pf pre cleanup) := by
  unfold compileFileScalarWhen compileFileProductionWith
  exact .cond (.cond compileFileWith_runsRoutes
    (.retry (lowerForAllocationProductionWith_callsRoute _) compileFileWith_runsRoutes))
    compileFileWith_runsRoutes

theorem compileFileArithmeticNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileArithmeticNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationArithmeticNI_callsRoute compileFileScalarWhen_runsRoutes enabled _
theorem compileFileMixedNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileMixedNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationMixedNI_callsRoute compileFileArithmeticNIWhen_runsRoutes enabled _
theorem compileFileLogicalNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileLogicalNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationLogicalNI_callsRoute compileFileMixedNIWhen_runsRoutes enabled _
theorem compileFileScalarNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileScalarNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationScalarNI_callsRoute compileFileLogicalNIWhen_runsRoutes enabled _
theorem compileFileTwoBlockNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileTwoBlockNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationTwoBlockNI_callsRoute compileFileScalarNIWhen_runsRoutes enabled _
theorem compileFileTwoBlockEntryNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileTwoBlockEntryNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationTwoBlockEntryNI_callsRoute compileFileTwoBlockNIWhen_runsRoutes enabled _
theorem compileFileLinearCfgNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileLinearCfgNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationLinearCfgNI_callsRoute compileFileTwoBlockEntryNIWhen_runsRoutes enabled _
theorem compileFileForwardCfgNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileForwardCfgNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationForwardCfgNI_callsRoute compileFileLinearCfgNIWhen_runsRoutes enabled _
theorem compileFileConditionalCfgNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileConditionalCfgNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationConditionalCfgNI_callsRoute compileFileForwardCfgNIWhen_runsRoutes enabled _
theorem compileFileConditionalForwardCfgNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileConditionalForwardCfgNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationConditionalForwardCfgNI_callsRoute
    compileFileConditionalCfgNIWhen_runsRoutes enabled _
theorem compileFileParameterCfgNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileParameterCfgNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationParameterCfgNI_callsRoute
    compileFileConditionalForwardCfgNIWhen_runsRoutes enabled _
theorem compileFileMemoryNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileMemoryNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationMemoryNI_callsRoute compileFileParameterCfgNIWhen_runsRoutes enabled _
theorem compileFileMemoryCfgNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileMemoryCfgNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationMemoryCfgNI_callsRoute compileFileMemoryNIWhen_runsRoutes enabled _
theorem compileFileMemoryIntegerNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileMemoryIntegerNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationMemoryIntegerNI_callsRoute compileFileMemoryCfgNIWhen_runsRoutes enabled _
theorem compileFileMemoryExtLoadNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileMemoryExtLoadNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationMemoryExtLoadNI_callsRoute compileFileMemoryIntegerNIWhen_runsRoutes enabled _
theorem compileFileMemoryStoreNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileMemoryStoreNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationMemoryStoreNI_callsRoute compileFileMemoryExtLoadNIWhen_runsRoutes enabled _
theorem compileFileMemoryStoreCfgNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileMemoryStoreCfgNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationMemoryStoreCfgNI_callsRoute compileFileMemoryStoreNIWhen_runsRoutes enabled _
theorem compileFileMemoryLoadStoreNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileMemoryLoadStoreNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationMemoryLoadStoreNI_callsRoute compileFileMemoryStoreCfgNIWhen_runsRoutes
    enabled _
theorem compileFileMemoryCapturedCopyNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileMemoryCapturedCopyNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationMemoryCapturedCopyNI_callsRoute compileFileMemoryLoadStoreNIWhen_runsRoutes
    enabled _
theorem compileFileMemorySinkExtNIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileMemorySinkExtNIWhen enabled alloc pf pre cleanup) :=
  .wrapper lowerForAllocationMemorySinkExtNI_callsRoute compileFileMemoryCapturedCopyNIWhen_runsRoutes
    enabled _

theorem compileFileVoidCallABIWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileVoidCallABIWhen enabled alloc pf pre cleanup) := by
  unfold compileFileVoidCallABIWhen finishFileVoidCallABI
  exact .cond (compileFileMemorySinkExtNIWhen_runsRoutes false)
    (.cond (compileFileMemorySinkExtNIWhen_runsRoutes true)
      (.cond (compileFileMemorySinkExtNIWhen_runsRoutes true)
        (.retry lowerForAllocationVoidCallABI_callsRoute (compileFileMemorySinkExtNIWhen_runsRoutes true))))

/-- **The Stock file driver** (`lean-backend`'s, enabled or not) only runs
`compileFileWithLowering L` for the 23 lowerings `L` above, each with `CallsRoute L`. -/
theorem compileFileReturnPinWhen_runsRoutes (enabled : Bool) :
    RunsRoutes alloc pf pre cleanup (compileFileReturnPinWhen enabled alloc pf pre cleanup) := by
  unfold compileFileReturnPinWhen
  exact .cond (compileFileMemorySinkExtNIWhen_runsRoutes enabled)
    (compileFileVoidCallABIWhen_runsRoutes enabled)

theorem filterMap_any_false {α β : Type} {l : List α} {g : α → Option (String × β)} {name : String}
    {e : α} {r : β} (he : e ∈ l) (hg : g e = some (name, r))
    (h : (l.filterMap g).any (·.1 == name) = false) : False := by
  have := List.any_eq_false.mp h _ (List.mem_filterMap.mpr ⟨e, he, hg⟩)
  simp at this

/-- **A function `compileFileWithLowering` reports compiled, neither unverified nor
unvalidated, was lowered with verification on**: if its lowering gave code (else the name is
another function's), `verifyOf` is `true`. -/
theorem compileFileWithLowering_verify [RunsReturn m]
    {L : Clif.Function → Bool → Bool → Except String VCode} {fa : FileAsm}
    (run : RunsReturn.Ret (compileFileWithLowering L VCode.rulesFired alloc pf pre cleanup) fa)
    {p : Clif.ParsedFunction} {f : Clif.Function} (hp : p ∈ pf.funcs) (hf : p.func = .ok f)
    (compiled : fa.funcs.any (·.name == p.name) = true)
    (verified : fa.unverified.any (·.1 == p.name) = false)
    (validated : fa.unvalidated.any (·.1 == p.name) = false)
    {code : VCode} (lowered : L f (verifyOf pre p.name f) cleanup = .ok code) :
    verifyOf pre p.name f = true := by
  have entry := mem_loweredOf (lower := L) (pre := pre) (cleanup := cleanup) hp hf
  rw [lowered] at entry
  change (p.name, Except.ok (f, code)) ∈ _ at entry
  unfold compileFileWithLowering at run
  obtain ⟨_, -, run⟩ := RunsReturn.ret_bind run
  obtain ⟨_, -, run⟩ := RunsReturn.ret_bind run
  obtain ⟨_, -, run⟩ := RunsReturn.ret_bind run
  have := RunsReturn.ret_pure run
  subst this
  dsimp only at compiled verified validated
  cases hv : verifyOf pre p.name f
  · exfalso
    cases hl : pre.lookup p.name with
    | some r => exact filterMap_any_false (r := r) entry (by simp [compiled, hl]) verified
    | none =>
      cases hu : unverifiedReason? f with
      | some r =>
        exact filterMap_any_false (r := r) entry (by simp [compiled, hl, hu]) verified
      | none =>
        cases hb : overBudget? f with
        | none => simp [verifyOf, hl, hu, hb] at hv
        | some b =>
          exact filterMap_any_false (r := b) entry (by
            simp only [compiled, verified, hb, Bool.true_and, Bool.not_false, ↓reduceIte,
              Option.map_some]) validated
  · rfl

/-- **The Stock path's `checkCalls` premise, from `lean-backend`'s own run** (#1101): a run of the
file driver `compileFileReturnPinWhen` (in `IO`, or any monad with `RunsReturn`) that returns `fa`
returned it from one run of `compileFileWithLowering L` for a lowering `L` with `CallsRoute L`;
for a function `p` of the file (subset E) that `fa` reports compiled and neither unverified nor
unvalidated, the code that run handed the allocator for `p` (`compileFileWithLowering_alloc`:
`L f (verifyOf pre p.name f) cleanup`) is the cleanup stage `stageF cleanup f vc` of a lowering
`vc` with `SemanticABI.checkCalls f vc = true`. -/
theorem compileFileReturnPinWhen_checkCalls [RunsReturn m] (enabled : Bool) {fa : FileAsm}
    (run : RunsReturn.Ret (compileFileReturnPinWhen enabled alloc pf pre cleanup) fa)
    {p : Clif.ParsedFunction} {f : Clif.Function} (hp : p ∈ pf.funcs) (hf : p.func = .ok f)
    (hE : Compile.functionE f = true)
    (compiled : fa.funcs.any (·.name == p.name) = true)
    (verified : fa.unverified.any (·.1 == p.name) = false)
    (validated : fa.unvalidated.any (·.1 == p.name) = false) :
    ∃ L, CallsRoute L ∧
      RunsReturn.Ret (compileFileWithLowering L VCode.rulesFired alloc pf pre cleanup) fa ∧
      ∀ code, L f (verifyOf pre p.name f) cleanup = .ok code →
        verifyOf pre p.name f = true ∧
        ∃ vc, SemanticABI.checkCalls f vc = true ∧ code = Stock.Arithmetic.stageF cleanup f vc := by
  obtain ⟨L, hL, ran⟩ := (compileFileReturnPinWhen_runsRoutes enabled).ret run
  refine ⟨L, hL, ran, fun code lowered => ?_⟩
  have on := compileFileWithLowering_verify ran hp hf compiled verified validated lowered
  rw [on] at lowered
  exact ⟨on, hL hE lowered⟩

end Runs

end Backend
