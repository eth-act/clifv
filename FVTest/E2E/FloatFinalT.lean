import FV.E2E.FinalDirectT
import FV.E2E.DeadCleanupT
import FV.Backend.Proof.LowerDecide
import FVTest.Backend.FloatDriverT

/-!
Non-vacuity of the typed final theorem's structural premises (S11e5 Stage C, slice 7): the
function `fW` moves `f64` values (a float `load`, an `f64const`, a float `select`, a float
`store`, a `bitcast` to an integer) between integer parameters and an integer return. It is
outside subset E and inside the typed scope (`InSubsetT`), and the whole pipeline — typed
lowering validator `lowerCheckT`, `prepare` + `prepCheck`, the spill allocation accepted by
`checkAlloc`, `lowerRFunc` (with its control-form check), emission and layout — succeeds
(`CompiledT`, hence `CompiledAT`); the prepared code's forms are covered (`FormsCovered`). These
are the premises of `backend_correct_finalT`/`_exT` besides the typed M4 families
(`TypedRules`) and the run/link contracts.

`fMv` (float parameters and a float return) is in `InSubsetT`, and since slice 5 widened
`ctlInstOk` (float `Args`/`Rets` in v0–v7) its whole pipeline succeeds as well (`compiledT_mv`,
`compiledAT_mv`, `formsCovered_mv`); the integer check `ctlCheckInt` rejects it. Checks by
`native_decide` (witness only).
`lake build FVTest.E2E.FloatFinalT`.
With no answer from the untrusted allocator, slice 6's typed spill chain and
`CompiledAT.of_lowerT` give `CompiledAT` for `fW` without the validator premises
(`compiledAT_of_lowerT_w`: the pipeline side of `backend_correct_finalT_alloc`).
-/

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill E2E

namespace FloatFinalT

open FloatDriverT

/-- Float data movement between integer parameters and an integer return. -/
def fW : Clif.Function := fnOfText
  "function %w(i64, i8) -> i64 {
block0(v0: i64, v1: i8):
    v2 = load.f64 v0
    v3 = f64const 0x1.0p-2
    v4 = select v1, v2, v3
    store v4, v0+8
    v5 = bitcast.i64 v4
    return v5
}
"

/-- `prepare`'s output on the lowering (`default` if it fails). -/
def vcpOf (f : Clif.Function) : VCode :=
  match Backend.prepare (vcOf f) with
  | .ok vcp => vcp
  | .error _ => default

/-- The spill allocation of the prepared code. -/
def rfOf (f : Clif.Function) : RFunc := spillAlloc (vcpOf f)

def afOf (f : Clif.Function) : AFunc :=
  match lowerRFunc (vcpOf f) (rfOf f) with
  | .ok af => af
  | .error _ => default

def faOf (f : Clif.Function) : FnAsm :=
  match emitFunc 0 (afOf f) with
  | .ok fa => fa
  | .error _ => default

def fbOf (f : Clif.Function) : FnBin :=
  match (faOf f).layout with
  | .ok fb => fb
  | .error _ => default

-- `fW` is outside subset E, inside the typed scope; its pipeline succeeds
#guard !Compile.functionE fW && Compile.functionET fW
#guard (lowerFunction fW).toBool && !lowerCheck fW (vcOf fW) && lowerCheckT fW (vcOf fW)
#guard (vcOf fW).blocks.any fun vb => vb.insts.any (· matches .fpuLoad ..)
#guard (lowerRFunc (vcpOf fW) (rfOf fW)).toBool && (emitFunc 0 (afOf fW)).toBool &&
  (faOf fW).layout.toBool
-- the float stores of `fW` and `fMv` store float values (`InSubsetT.storeTyped`)
#guard Compile.storeTypedB fW && Compile.storeTypedB fMv

/-- `fW` with its float `store` storing the integer parameter `v0`: the CLIF verifier rejects
it, and so does `Compile.storeTypedB`. -/
def fBadStore : Clif.Function :=
  { fW with blocks := fW.blocks.map fun b => { b with body := b.body.map fun s =>
      match s.inst with
      | .store op ty fl _ q off => { s with inst := .store op ty fl 0 q off }
      | _ => s } }

#guard fBadStore.blocks.any fun b => b.body.any fun s => s.inst matches .store _ .f64 _ 0 _ _
#guard !Compile.storeTypedB fBadStore

-- `fMv` passes the validators, `checkAlloc` and, since slice 5 widened `ctlInstOk` (float
-- `Args`/`Rets` in v0–v7), `lowerRFunc`'s `ctlCheck`; the integer check `ctlCheckInt` rejects it
#guard lowerCheckT fMv (vcOf fMv) && (checkAlloc (vcpOf fMv) (rfOf fMv)).isOk &&
  (lowerRFunc (vcpOf fMv) (rfOf fMv)).toBool && ctlCheck (vcpOf fMv) (rfOf fMv) &&
  !ctlCheckInt (vcpOf fMv) (rfOf fMv)

theorem lowerFunction_w : lowerFunction fW = .ok (vcOf fW) := by
  have hok : (lowerFunction fW).toBool = true := by native_decide
  unfold vcOf
  cases h : lowerFunction fW with
  | error e => rw [h] at hok; cases hok
  | ok vc => rfl

theorem prepare_w : Backend.prepare (vcOf fW) = .ok (vcpOf fW) := by
  have hok : (Backend.prepare (vcOf fW)).toBool = true := by native_decide
  unfold vcpOf
  cases h : Backend.prepare (vcOf fW) with
  | error e => rw [h] at hok; cases hok
  | ok vcp => rfl

theorem alloc_w : lowerRFunc (vcpOf fW) (rfOf fW) = .ok (afOf fW) := by
  have hok : (lowerRFunc (vcpOf fW) (rfOf fW)).toBool = true := by native_decide
  unfold afOf
  cases h : lowerRFunc (vcpOf fW) (rfOf fW) with
  | error e => rw [h] at hok; cases hok
  | ok af => rfl

theorem emit_w : emitFunc 0 (afOf fW) = .ok (faOf fW) := by
  have hok : (emitFunc 0 (afOf fW)).toBool = true := by native_decide
  unfold faOf
  cases h : emitFunc 0 (afOf fW) with
  | error e => rw [h] at hok; cases hok
  | ok fa => rfl

theorem layout_w : (faOf fW).layout = .ok (fbOf fW) := by
  have hok : (faOf fW).layout.toBool = true := by native_decide
  unfold fbOf
  cases h : (faOf fW).layout with
  | error e => rw [h] at hok; cases hok
  | ok fb => rfl

theorem checkAlloc_w : checkAlloc (vcpOf fW) (rfOf fW) = .ok () := by
  have hok : (checkAlloc (vcpOf fW) (rfOf fW)).isOk = true := by native_decide
  cases h : checkAlloc (vcpOf fW) (rfOf fW) with
  | error e => rw [h] at hok; cases hok
  | ok u => rfl

/-- **Witness** (slice 5): the typed compiled-code premise holds for `fMv` (float parameters, a
float return, float block parameters): its float `Args`/`Rets` pass the widened `ctlCheck`. -/
theorem compiledT_mv :
    CompiledT fMv 0 (vcOf fMv) (vcpOf fMv) (rfOf fMv) (afOf fMv) (faOf fMv) (fbOf fMv) := by
  refine ⟨?_, by native_decide, ?_, by native_decide, ?_, ?_, ?_, ?_⟩
  · have hok : (lowerFunction fMv).toBool = true := by native_decide
    unfold vcOf
    cases h : lowerFunction fMv with
    | error e => rw [h] at hok; cases hok
    | ok vc => rfl
  · have hok : (Backend.prepare (vcOf fMv)).toBool = true := by native_decide
    unfold vcpOf
    cases h : Backend.prepare (vcOf fMv) with
    | error e => rw [h] at hok; cases hok
    | ok vcp => rfl
  · have hok : (checkAlloc (vcpOf fMv) (rfOf fMv)).isOk = true := by native_decide
    cases h : checkAlloc (vcpOf fMv) (rfOf fMv) with
    | error e => rw [h] at hok; cases hok
    | ok u => rfl
  · have hok : (lowerRFunc (vcpOf fMv) (rfOf fMv)).toBool = true := by native_decide
    unfold afOf
    cases h : lowerRFunc (vcpOf fMv) (rfOf fMv) with
    | error e => rw [h] at hok; cases hok
    | ok af => rfl
  · have hok : (emitFunc 0 (afOf fMv)).toBool = true := by native_decide
    unfold faOf
    cases h : emitFunc 0 (afOf fMv) with
    | error e => rw [h] at hok; cases hok
    | ok fa => rfl
  · have hok : (faOf fMv).layout.toBool = true := by native_decide
    unfold fbOf
    cases h : (faOf fMv).layout with
    | error e => rw [h] at hok; cases hok
    | ok fb => rfl

/-- **Witness** (slice 5): … and so the `AllocChecked` form, the compiled-code premise of
`backend_correct_final_exT` for a function with float parameters and a float return. -/
theorem compiledAT_mv :
    CompiledAT fMv 0 (vcOf fMv) (vcpOf fMv) (rfOf fMv) (afOf fMv) (faOf fMv) (fbOf fMv) :=
  compiledT_mv.toA

/-- **Witness** (slice 5): the prepared code's straight-line forms of `fMv` are covered. -/
theorem formsCovered_mv : FormsCovered ⟨(faOf fMv).k, (afOf fMv).slotBase⟩ (vcpOf fMv) :=
  (formsCoveredB_iff _ _).mp (by native_decide)

/-- **Witness**: `fW` is in the typed theorem's subset (outside subset E). -/
theorem inSubsetT_w (p : Clif.Program) : InSubsetT p fW := by
  have hnc : fW.blocks.all (fun B => B.body.all fun st => !(st.inst matches .call ..)) = true := by
    native_decide
  have hnt : fW.blocks.all (fun B => !B.term.isTry) = true := by native_decide
  have habi : (sigAbiOk fW.sig && fW.externs.all (sigAbiOk ·.2.sig)) = true := by native_decide
  have hind : _root_.Backend.indSigs fW = [] := by native_decide
  simp only [Bool.and_eq_true, List.all_eq_true] at habi
  refine ⟨by native_decide, fun B hB st hst fn args hi _ _ => ?_, fun B hB fn args et ht _ _ => ?_,
    ⟨habi.1, fun e he => habi.2 e he⟩, by rw [hind]; simp, by native_decide⟩
  · have := List.all_eq_true.mp (List.all_eq_true.mp hnc B hB) st hst
    rw [hi] at this; cases this
  · have := List.all_eq_true.mp hnt B hB
    rw [ht] at this; cases this

/-- **Witness**: the typed compiled-code premise holds for `fW` (the spill allocation, accepted
by `checkAlloc`). -/
theorem compiledT_w :
    CompiledT fW 0 (vcOf fW) (vcpOf fW) (rfOf fW) (afOf fW) (faOf fW) (fbOf fW) :=
  ⟨lowerFunction_w, by native_decide, prepare_w, by native_decide, checkAlloc_w, alloc_w, emit_w,
    layout_w⟩

/-- **Witness**: … and so the `AllocChecked` form. -/
theorem compiledAT_w :
    CompiledAT fW 0 (vcOf fW) (vcpOf fW) (rfOf fW) (afOf fW) (faOf fW) (fbOf fW) :=
  compiledT_w.toA

/-- **Witness**: the prepared code's straight-line forms are covered (`hcov`). -/
theorem formsCovered_w : FormsCovered ⟨(faOf fW).k, (afOf fW).slotBase⟩ (vcpOf fW) :=
  (formsCoveredB_iff _ _).mp (by native_decide)

/-- **Witness**: the typed lowering obligations of `fW` (from `lowerCheckT`). -/
theorem loweringObligationsT_w : LoweringObligationsT fW (vcOf fW) :=
  loweringObligationsT_of_check compiledT_w.lowerOk

/-- **Witness**: `fMv` (float parameters, a float return) is in the typed subset too. -/
theorem inSubsetT_mv (p : Clif.Program) : InSubsetT p fMv := by
  have hnc : fMv.blocks.all (fun B => B.body.all fun st => !(st.inst matches .call ..)) = true := by
    native_decide
  have hnt : fMv.blocks.all (fun B => !B.term.isTry) = true := by native_decide
  have habi : (sigAbiOk fMv.sig && fMv.externs.all (sigAbiOk ·.2.sig)) = true := by native_decide
  have hind : _root_.Backend.indSigs fMv = [] := by native_decide
  simp only [Bool.and_eq_true, List.all_eq_true] at habi
  refine ⟨functionET_mv, fun B hB st hst fn args hi _ _ => ?_, fun B hB fn args et ht _ _ => ?_,
    ⟨habi.1, fun e he => habi.2 e he⟩, by rw [hind]; simp, by native_decide⟩
  · have := List.all_eq_true.mp (List.all_eq_true.mp hnc B hB) st hst
    rw [hi] at this; cases this
  · have := List.all_eq_true.mp hnt B hB
    rw [ht] at this; cases this

/-- `fW` is in the typed lowering's input conditions. -/
theorem scopeT_w : LowerScopeT fW where
  subsetT := by native_decide
  nonempty := by native_decide
  noEntryPred := by native_decide
  ctxFacts := by
    intro ctx ranges st0 hb
    have h : (match buildCtx fW with
        | .ok (c, _, _) => brIdxOk fW c && ctxOkT fW c
        | .error _ => false) = true := by native_decide
    rw [hb] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1, (ctxOkT_sound h.2).addr64⟩
  tryRet := by
    have h : fW.blocks.all (fun B => !B.term.isTry) = true := by native_decide
    intro B hB et ht
    have := List.all_eq_true.mp h B hB
    rcases ht with ⟨fn, args, he⟩ | ⟨c, args, he⟩ <;> rw [he] at this <;> cases this
  stackLayout := by
    have h : fW.blocks.all (fun B => B.body.all fun st => !(st.inst matches .call ..)) = true := by
      native_decide
    have h2 : fW.blocks.all (fun B => !B.term.isTry) = true := by native_decide
    refine ⟨fun B hB st hst fn args e hi _ => ?_, fun B hB fn args et e ht _ => ?_⟩
    · have := List.all_eq_true.mp (List.all_eq_true.mp h B hB) st hst
      rw [hi] at this; cases this
    · have := List.all_eq_true.mp h2 B hB
      rw [ht] at this; cases this

/-- **Witness** (direct route): with no answer from the untrusted allocator, slice 6's typed
spill chain makes the lowered allocation `AllocChecked` under the decided premises, and
`CompiledAT.of_lowerT` gives `CompiledAT` without the validator premises — the premises of
`backend_correct_finalT_alloc` on the pipeline's side. -/
theorem compiledAT_of_lowerT_w :
    CompiledAT fW 0 (vcOf fW) (vcpOf fW) (allocResult (vcpOf fW) (.error "no allocator"))
      (afOf fW) (faOf fW) (fbOf fW) := by
  have hch := allocChecked_allocResultT (dominated_of (by native_decide)) scopeT_w
    (Spill.arityOk_of (by native_decide)) (by native_decide)
    (resClassOk_of_resClassOkB (by native_decide)) lowerFunction_w prepare_w
    (ctlSpill_of_ctlSpillB (by native_decide)) ((formsCoveredB_iff _ _).mp (by native_decide))
    (by native_decide) (.error "no allocator")
  exact CompiledAT.of_lowerT (dominated_of (by native_decide)) scopeT_w lowerFunction_w prepare_w
    hch alloc_w emit_w layout_w

/-! ### The dead-cleanup route (`prune`, then `prepare`) -/

def vcpcOf (f : Clif.Function) : VCode :=
  match Backend.prepare (cleanupStage f (vcOf f)) with
  | .ok vcp => vcp
  | .error _ => default

def afcOf (f : Clif.Function) : AFunc :=
  match lowerRFunc (vcpcOf f) (spillAlloc (vcpcOf f)) with
  | .ok af => af
  | .error _ => default

def facOf (f : Clif.Function) : FnAsm :=
  match emitFunc 0 (afcOf f) with
  | .ok fa => fa
  | .error _ => default

def fbcOf (f : Clif.Function) : FnBin :=
  match (facOf f).layout with
  | .ok fb => fb
  | .error _ => default

/-- **Witness**: the typed dead-cleanup compiled-code premise holds for `fW` (the shipped
`--lean-link` route: lowering, `prune`, `prepare`, the spill allocation). -/
theorem compiledCleanupT_w : CompiledCleanupT fW 0 (vcOf fW) (vcpcOf fW)
    (spillAlloc (vcpcOf fW)) (afcOf fW) (facOf fW) (fbcOf fW) := by
  have h1 : (Backend.prepare (cleanupStage fW (vcOf fW))).toBool = true := by native_decide
  have h2 : (lowerRFunc (vcpcOf fW) (spillAlloc (vcpcOf fW))).toBool = true := by native_decide
  have h3 : (emitFunc 0 (afcOf fW)).toBool = true := by native_decide
  have h4 : (facOf fW).layout.toBool = true := by native_decide
  have h5 : (checkAlloc (vcpcOf fW) (spillAlloc (vcpcOf fW))).isOk = true := by native_decide
  refine ⟨lowerFunction_w, by native_decide, ?_, by native_decide, ?_, ?_, ?_, ?_⟩
  · unfold vcpcOf
    cases h : Backend.prepare (cleanupStage fW (vcOf fW)) with
    | error e => rw [h] at h1; cases h1
    | ok vcp => rfl
  · cases h : checkAlloc (vcpcOf fW) (spillAlloc (vcpcOf fW)) with
    | error e => rw [h] at h5; cases h5
    | ok u => rfl
  · unfold afcOf
    cases h : lowerRFunc (vcpcOf fW) (spillAlloc (vcpcOf fW)) with
    | error e => rw [h] at h2; cases h2
    | ok af => rfl
  · unfold facOf
    cases h : emitFunc 0 (afcOf fW) with
    | error e => rw [h] at h3; cases h3
    | ok fa => rfl
  · unfold fbcOf
    cases h : (facOf fW).layout with
    | error e => rw [h] at h4; cases h4
    | ok fb => rfl

end FloatFinalT
