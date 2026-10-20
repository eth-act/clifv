import FVTest.E2E.FloatFinalT
import FV.E2E.LinkScopeT
import FV.E2E.CompiledEitherT

/-!
Non-vacuity of the typed store typing, world/non-interference and input-scope layer (S11e5 Stage
C, slice 7), on `FloatFinalT`'s `fW` (float data movement between integer parameters and return)
and `fMv` (float parameters, return and block parameters):

* store typing: `buildCtx`'s contexts of `fW`/`fMv` are `StoresTyped` (`storesTyped_of_buildCtx`),
  and a float store of an integer value (`fBadStore`) fails `storeTypedB` and `fnScopeTB`;
* `TermIntPos` of `fMv`'s terminators (`termIntPos_of_functionET`; its `brif` condition);
* the typed artifact contracts `CompiledEitherT` (legacy and dead-cleanup) of `fW`;
* `fnScopeTB fW` and its consequences: `InSubsetT` (`inSubsetT_of_fnScopeT`), `LowerScopeT`
  (`lowerScopeT_of`), `CompiledAT`/`CompiledT` from the pipeline's results
  (`compiledAT_of_fnScopeT`, `compiledT_of_fnScopeT`) — the per-function premises of
  `backend_correct_finalT_scope`, `backend_correct_worldT`, `backend_correct_world_niT`;
* integer specialization: `lowerScopeTB_of_lowerScopeB` on a subset-E function.
Checks by `native_decide` (witness only). `lake build FVTest.E2E.FloatLinkT`.
-/

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill E2E E2E.LinkCheck

namespace FloatLinkT

open FloatDriverT FloatFinalT

-- store typing and the typed input scope
#guard (buildCtx fW).toBool && (buildCtx fMv).toBool
#guard fnScopeTB fW && !fnScopeTB fBadStore && !Compile.storeTypedB fBadStore
#guard Compile.functionET fBadStore

/-- **Witness**: `buildCtx`'s contexts of `fW` are store-typed. -/
theorem storesTyped_w : ∀ ctx ranges st0, buildCtx fW = .ok (ctx, ranges, st0) →
    StoresTyped ctx :=
  fun _ _ _ hb => storesTyped_of_buildCtx (by native_decide) hb

/-- **Witness**: … and so are `fMv`'s (two float stores of float values). -/
theorem storesTyped_mv : ∀ ctx ranges st0, buildCtx fMv = .ok (ctx, ranges, st0) →
    StoresTyped ctx :=
  fun _ _ _ hb => storesTyped_of_buildCtx (by native_decide) hb

/-- **Witness**: the integer-position operands of `fMv`'s terminators (the `brif` condition)
are in integer positions of `buildCtx`'s context. -/
theorem termIntPos_mv : ∀ ctx ranges st0, buildCtx fMv = .ok (ctx, ranges, st0) →
    ∀ B ∈ fMv.blocks, TermIntPos ctx B.term :=
  fun _ _ _ hb _ hB => termIntPos_of_functionET (by native_decide) hb hB

/-- **Witness**: the typed artifact contract of `fW`, legacy route. -/
theorem compiledEitherT_legacy_w :
    CompiledEitherT fW 0 (vcOf fW) (vcpOf fW) (rfOf fW) (afOf fW) (faOf fW) (fbOf fW) :=
  .legacy compiledT_w

/-- **Witness**: the typed artifact contract of `fW`, dead-cleanup route. -/
theorem compiledEitherT_cleanup_w : CompiledEitherT fW 0 (vcOf fW) (vcpcOf fW)
    (spillAlloc (vcpcOf fW)) (afcOf fW) (facOf fW) (fbcOf fW) :=
  .cleanup compiledCleanupT_w

theorem fnScopeTB_w : fnScopeTB fW = true := by native_decide

/-- **Witness**: `fnScopeTB` gives `fW`'s typed subset. -/
theorem inSubsetT_scope_w (p : Clif.Program) : InSubsetT p.bare fW :=
  inSubsetT_of_fnScopeT fnScopeTB_w p

/-- **Witness**: `lowerScopeTB` decides `fW`'s `LowerScopeT`. -/
theorem lowerScopeT_w : LowerScopeT fW := lowerScopeT_of (by native_decide)

/-- **Witness**: `fnScopeTB` and the pipeline's results give `fW`'s `CompiledAT` (the allocation
of the spill fallback, no allocator answer). -/
theorem compiledAT_scope_w :
    CompiledAT fW 0 (vcOf fW) (vcpOf fW) (allocResult (vcpOf fW) (.error "no allocator"))
      (afOf fW) (faOf fW) (fbOf fW) :=
  compiledAT_of_fnScopeT fnScopeTB_w lowerFunction_w prepare_w rfl alloc_w emit_w layout_w

/-- **Witness**: … and `CompiledT` with `checkAlloc`'s verdict (the world theorems' form). -/
theorem compiledT_scope_w :
    CompiledT fW 0 (vcOf fW) (vcpOf fW) (rfOf fW) (afOf fW) (faOf fW) (fbOf fW) :=
  compiledT_of_fnScopeT fnScopeTB_w lowerFunction_w prepare_w checkAlloc_w alloc_w emit_w layout_w

/-- A subset-E function (integer `iadd` of its parameters). -/
def fInt : Clif.Function := fnOfText
  "function %i(i64, i64) -> i64 {
block0(v0: i64, v1: i64):
    v2 = iadd v0, v1
    return v2
}
"

#guard Compile.functionE fInt && lowerScopeB fInt

/-- **Witness** (integer specialization): `lowerScopeB` implies `lowerScopeTB`. -/
theorem lowerScopeTB_int : lowerScopeTB fInt = true :=
  lowerScopeTB_of_lowerScopeB (by native_decide)

end FloatLinkT
