import FV.Backend.Proof.DriverCheckTy

/-!
Non-vacuity of the typed movement scope and the typed driver model (S11e5 Stage C, slices 1-2):
float data-movement functions outside subset E (float parameters and returns, float `load`/
`store`, `f32const`/`f64const`, float `select`, `bitcast`, float block parameters, float branch
arguments through edge blocks, stack-passed `f64`/`f32` parameters) are in `Compile.functionET`
and `LowerScopeT`, so `buildCtx_typed` gives `ctxOkT`/`CtxInvT`/`InstScopeT` for their contexts;
their lowering passes the typed validator `lowerCheckT` (so `loweringT_of_check` gives
`LowerShapeT` and `Cert`) and fails the integer `lowerCheck`. Checks by `native_decide`
(witness only). `lake build FVTest.Backend.FloatDriverT`.
-/

open Backend Backend.Proof Backend.Proof.Driver

namespace FloatDriverT

/-- The first function of a CLIF text. -/
def fnOfText (src : String) : Clif.Function :=
  match (Clif.parseFile src).funcs with
  | p :: _ => match p.func with
    | .ok f => f
    | .error _ => default
  | [] => default

/-- `lowerFunction`'s VCode (`default` if it fails). -/
def vcOf (f : Clif.Function) : VCode :=
  match lowerFunction f with
  | .ok vc => vc
  | .error _ => default

/-- Float movement: parameters, loads/stores, constants, `select`, `bitcast`, block parameters,
`brif` arguments (edge blocks) and the return. -/
def fMv : Clif.Function := fnOfText
  "function %mv(f64, i64, f32, i8) -> f64 {
block0(v0: f64, v1: i64, v2: f32, v3: i8):
    v4 = load.f64 v1
    store v2, v1+8
    v5 = f32const 0x1.0p0
    store v5, v1+12
    v6 = select v3, v0, v4
    v7 = bitcast.i64 v6
    v8 = bitcast.f64 v7
    v9 = f64const 0x1.0p-2
    brif v3, block1(v8), block1(v9)
block1(v10: f64):
    jump block2(v10)
block2(v11: f64):
    return v11
}
"

/-- Stack-passed float parameters (the ninth `f64` and an `f32`: `ldr d`/`ldr s`). -/
def fStk : Clif.Function := fnOfText
  "function %stk(i64, f64, f64, f64, f64, f64, f64, f64, f64, f64, f32) -> f64 {
block0(v0: i64, v1: f64, v2: f64, v3: f64, v4: f64, v5: f64, v6: f64, v7: f64, v8: f64, v9: f64, v10: f32):
    store v10, v0+0
    return v9
}
"

-- outside subset E, inside the typed scope
#guard !Compile.functionE fMv && !Compile.functionE fStk
-- the typed scope keeps integer operations integer and rejects literal-pool `f64` constants
#guard !Compile.functionET (fnOfText
  "function %bad(f64) -> f64 {\nblock0(v0: f64):\n    v1 = iadd v0, v0\n    return v1\n}\n")
#guard !Compile.functionET (fnOfText
  "function %bad2(f32, i64) -> f32 {\nblock0(v0: f32, v1: i64):\n    v2 = load.f32 v0\n    return v2\n}\n")
#guard !Compile.functionET (fnOfText
  "function %pool() -> f64 {\nblock0:\n    v0 = f64const 0x1.123456789abcdp0\n    return v0\n}\n")
#guard Compile.functionET (fnOfText
  "function %nopool() -> f64 {\nblock0:\n    v0 = f64const 0x1.0p0\n    return v0\n}\n")

theorem functionET_mv : Compile.functionET fMv = true := by native_decide
theorem functionET_stk : Compile.functionET fStk = true := by native_decide

/-- `fMv` is in the typed lowering's input conditions. -/
theorem scopeT_mv : LowerScopeT fMv where
  subsetT := functionET_mv
  nonempty := by native_decide
  noEntryPred := by native_decide
  ctxFacts := by
    intro ctx ranges st0 hb
    have h : (match buildCtx fMv with
        | .ok (c, _, _) => brIdxOk fMv c && ctxOkT fMv c
        | .error _ => false) = true := by native_decide
    rw [hb] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1, (ctxOkT_sound h.2).addr64⟩
  tryRet := by
    have h : fMv.blocks.all (fun B => !B.term.isTry) = true := by native_decide
    intro B hB et ht
    have := List.all_eq_true.mp h B hB
    rcases ht with ⟨fn, args, he⟩ | ⟨c, args, he⟩ <;> rw [he] at this <;> cases this
  stackLayout := by
    have h : fMv.blocks.all (fun B => B.body.all fun st => !(st.inst matches .call ..) ) = true := by
      native_decide
    have h2 : fMv.blocks.all (fun B => !B.term.isTry) = true := by native_decide
    refine ⟨fun B hB st hst fn args e hi _ => ?_, fun B hB fn args et e ht _ => ?_⟩
    · have := List.all_eq_true.mp (List.all_eq_true.mp h B hB) st hst
      rw [hi] at this; cases this
    · have := List.all_eq_true.mp h2 B hB
      rw [ht] at this; cases this
  indStackLayout := by
    have h : (Backend.indSigs fMv).all (fun s => stackLayoutOk s) = true := by native_decide
    exact fun s hs => List.all_eq_true.mp h s hs

/-- **Slice 1 witness**: `buildCtx_typed` on a float-movement function outside subset E. -/
theorem buildCtx_typed_mv : ∃ ctx ranges st0, buildCtx fMv = .ok (ctx, ranges, st0) ∧
    ctxOkT fMv ctx = true ∧ CtxInvT fMv ctx ∧ InstScopeT ctx := by
  have hok : (buildCtx fMv).toBool = true := by native_decide
  cases hb : buildCtx fMv with
  | error e => rw [hb] at hok; cases hok
  | ok r =>
    obtain ⟨ctx, ranges, st0⟩ := r
    exact ⟨ctx, ranges, st0, rfl, buildCtx_typed scopeT_mv hb⟩

-- the lowerings succeed, carry float vregs, `ldr d`/`ldr s` stack-argument loads and float edge
-- arguments, and the typed validator accepts them where the integer one does not
#guard (lowerFunction fMv).toBool && (lowerFunction fStk).toBool
#guard (vcOf fMv).blocks.any fun vb => vb.insts.any fun
  | .args ps => ps.any fun (r, p) => r == .vreg 0 .float && p == .v 0
  | _ => false
#guard (vcOf fMv).blocks.any fun vb => vb.branchArgs.any (·.homeCls == .float)
#guard ((vcOf fStk).blocks[0]!.insts.filter (· matches .fpuLoad ..)).size == 2
#guard lowerCheckT fMv (vcOf fMv) && !lowerCheck fMv (vcOf fMv)
#guard lowerCheckT fStk (vcOf fStk) && !lowerCheck fStk (vcOf fStk)

theorem lowerFunction_mv : lowerFunction fMv = .ok (vcOf fMv) := by
  have hok : (lowerFunction fMv).toBool = true := by native_decide
  unfold vcOf
  cases h : lowerFunction fMv with
  | error e => rw [h] at hok; cases hok
  | ok vc => rfl

/-- **Slice 2 witness**: the typed validator accepts the float-movement lowering, so the typed
shape and the certificate hold for it. -/
theorem loweringT_mv : ∃ ctx st0 R gn bl A, LowerShapeT fMv (vcOf fMv) ctx st0 R gn bl ∧
    Cert fMv ctx st0 gn bl A ∧ ∀ B ∈ fMv.blocks, BrIdxTyped ctx B.term :=
  loweringT_of_check (by native_decide)

/-- **Slice 2 witness** (stack-passed float parameters). -/
theorem loweringT_stk : ∃ ctx st0 R gn bl A, LowerShapeT fStk (vcOf fStk) ctx st0 R gn bl ∧
    Cert fStk ctx st0 gn bl A ∧ ∀ B ∈ fStk.blocks, BrIdxTyped ctx B.term :=
  loweringT_of_check (by native_decide)

/-- The entry registers of the typed lowering include v registers. -/
theorem entryRegsT_mv : ∀ l ∈ locsOf fMv.sig, ∀ r, l = .reg r →
    (∃ n, r = .x n ∧ n ≤ 8) ∨ (∃ n, r = .v n ∧ n ≤ 7) :=
  entryRegsT_of_check (by native_decide : lowerCheckT fMv (vcOf fMv) = true)

end FloatDriverT
