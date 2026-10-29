module

public import FV.Backend.Proof.DriverCheckT

@[expose] public section

/-!
Non-vacuity of the float-capable context invariant `CtxInvT` (S11e4, #238): the contexts
`buildCtx` makes for a `select.f32` and a `load.f32`/`store.f64` function pass the Boolean check
`ctxOkT` (by `native_decide`, witness only), so `ctxOkT_sound` gives `CtxInvT` for them; they hold
the float instructions, and the ISLE `lower` term fires the float `select` root
(`rule_lower_2267`, id 971) and the float load/store roots (`rule_lower_2625`/`2750`, ids
1047/1074) on them. `lake build FVTest.Backend.FloatCtxT`.
-/

open Backend Backend.Proof Backend.Proof.Driver Isle.Aarch64

/-- The first function of a CLIF text. -/
def fnOfText (src : String) : Clif.Function :=
  match (Clif.parseFile src).funcs with
  | p :: _ => match p.func with
    | .ok f => f
    | .error _ => default
  | [] => default

/-- `buildCtx`'s context and initial lowering state of a function (an empty context if it fails). -/
def ctxStOf (f : Clif.Function) : Ctx × LState :=
  match buildCtx f with
  | .ok (ctx, _, st) => (ctx, st)
  | .error _ => ({ func := f, insts := #[], valTy := #[], valDef := #[], valReg := #[], slotOff := [] },
      default)

def fSel : Clif.Function := fnOfText
  "function %s(i8, f32, f32) -> f32 {\nblock0(v0: i8, v1: f32, v2: f32):\n    v3 = select v0, v1, v2\n    return v3\n}\n"

def fMem : Clif.Function := fnOfText
  "function %m(i64, f64) -> f32 {\nblock0(v0: i64, v1: f64):\n    v2 = load.f32 v0+8\n    store v1, v0\n    return v2\n}\n"

/-- The lowering trace of instruction `ii` (the ids of the rules that fired), or `[]`. -/
def lowerTrace (f : Clif.Function) (ii : Nat) : List Isle.RuleId :=
  let (ctx, st) := ctxStOf f
  match runTerm ctx "lower" [.inst ii] st with
  | .ok (some (.regsVec _), _, tr) => tr
  | _ => []

-- `buildCtx` succeeds and the instructions are the float ones
#guard (buildCtx fSel).toBool && (buildCtx fMem).toBool
#guard (ctxStOf fSel).1.insts[0]?.bind (·.clif) == some (.select .f32 0 1 2)
#guard ((ctxStOf fMem).1.insts[0]?.bind (·.clif)).any fun | .load _ .f32 _ 0 8 => true | _ => false
#guard ((ctxStOf fMem).1.insts[1]?.bind (·.clif)).any fun | .store _ .f64 _ 1 0 0 => true | _ => false
-- the float values have float vregs
#guard (ctxStOf fSel).1.valueReg? 1 == some (.vreg 1 .float)
#guard (ctxStOf fMem).1.valueReg? 2 == some (.vreg 2 .float)
-- `lower` fires the float roots on them
#guard rule_lower_2267.id == 971 && (lowerTrace fSel 0).contains 971
#guard rule_lower_2625.id == 1047 && (lowerTrace fMem 0).contains 1047
#guard rule_lower_2750.id == 1074 && (lowerTrace fMem 1).contains 1074

/-- **`CtxInvT` holds for the `select.f32` context.** -/
theorem ctxInvT_select_f32 : CtxInvT fSel (ctxStOf fSel).1 :=
  ctxOkT_sound (by native_decide)

/-- **`CtxInvT` holds for the `load.f32`/`store.f64` context.** -/
theorem ctxInvT_load_store_f : CtxInvT fMem (ctxStOf fMem).1 :=
  ctxOkT_sound (by native_decide)

-- the check rejects a context whose float value is in an integer position (the address of the
-- load re-typed as `f64`)
#guard !ctxOkT fMem { (ctxStOf fMem).1 with valTy := (ctxStOf fMem).1.valTy.set! 0 (some (.float 64)) }
