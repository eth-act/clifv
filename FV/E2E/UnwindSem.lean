import FV.E2E.RegLevelDriverSem

/-!
# The instruction semantics with unwinding (S10e, #232)

`docs/plans/unwinding.md`, "The exceptional edge in the per-function theorem". Additive: `csem`
and every theorem about it are unchanged.

* `XRaise`: the callees' exceptional results, `ExtSem.call`'s counterpart: `raise d uses w =
  some (obj, w')`: the callee of `bl d` (`d = some name`) / `blr` (`none`) called with `uses`
  from world `w` raised the exception object `obj`, and `w'` is the world after the unwinder
  restored our call (the callee's frame and every frame below it unwound).
* `csemU F ctx X XR`: `csem F ctx X`, except at a call whose callee raises:
  - a plain `call` ends the activation: control outcome `.halt` (a frame exit; the observables
    tell it from a trap by its instruction, `VUnwFrom`), the defs' values unconstrained (0);
  - a `tryCall` of a supported shape (`tryUOk`) continues at its first handler (`.goto 0`, the
    landing pad of the emitted call-site entry, S10c), the defs holding the payload Rust's
    personality installs: x0 := the exception object, x1 := 0 (`payloadOuts`). The supported
    shape: the first handler is a `tag 0` (cleanup) or `tag 1` (catch-all) handler — the
    handlers `Backend.callSites` emits a landing pad for —, the exceptional ABI restores the
    callee-saved registers (`clobberAll = false`), and every def of the call is in x0 or x1
    (at most two ABI returns: the defs are then exactly the payload registers,
    `gen_try_call_rets`, so the handler edges keep no def the unwinder leaves unconstrained;
    every `try_call` of the fv-demo, survey and deps crates has at most two returns and a
    first `tag0` handler).
* `driverSem_csemU`: the driver's facts (`DriverSem`) hold for `csemU` as for `csem`.
-/

namespace Backend.Proof

open Backend Backend.Proof.Driver

/-- **The callees' exceptional results** (`ExtSem.call`'s counterpart). -/
structure XRaise where
  raise : Option String → List CV → Arm.ArmState → Option (BitVec 64 × Arm.ArmState)

/-- No callee raises. -/
def XRaise.none : XRaise := ⟨fun _ _ _ => Option.none⟩

/-- The callee descriptor of a call (`ExtSem.call`'s first argument): the symbol of `bl`, `none`
for `blr`. -/
def callDest (info : CallInfo) : Option String :=
  match info.dest with
  | .sym n => some n
  | .reg _ => none

/-- The values a landing pad finds in the defs of the call (one per def, in def order): the
exception object in x0, Rust's selector 0 in x1. -/
def payloadOuts (info : CallInfo) (obj : BitVec 64) : List CV :=
  info.defs.map fun (r, _) => if r = .x 0 then ofX obj else ofX 0

/-- The first handler is a `tag 0` / `tag 1` handler. -/
def firstHandlerOk : List TryHandler → Bool
  | .tag 0 _ :: _ | .tag 1 _ :: _ => true
  | _ => false

/-- **The `try_call` shapes whose exceptional edge is covered**: first handler `tag 0`/`tag 1`,
callee-saved registers restored by the unwinder, every def in x0 or x1. -/
def tryUOk (info : CallInfo) (ti : TryInfo) : Bool :=
  firstHandlerOk ti.handlers && !ti.clobberAll && info.defs.all fun (r, _) => r == .x 0 || r == .x 1

/-- **The concrete instruction semantics with unwinding.** -/
noncomputable def csemU (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (XR : XRaise) :
    ISem CV Arm.ArmState := fun i uses w =>
  match i with
  | .call info =>
    match XR.raise (callDest info) uses w with
    | some (_, w') => some (info.defs.map (fun _ => ofX 0), w', .halt)
    | Option.none => csem F ctx X i uses w
  | .tryCall info ti =>
    match XR.raise (callDest info) uses w with
    | some (obj, w') => if tryUOk info ti then some (payloadOuts info obj, w', .goto 0) else Option.none
    | Option.none => csem F ctx X i uses w
  | _ => csem F ctx X i uses w

/-- `csemU` is `csem` on every instruction but `call`/`tryCall`. -/
theorem csemU_of_not_call {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}
    {i : MInst} (hc : ∀ info, i ≠ .call info) (ht : ∀ info ti, i ≠ .tryCall info ti) :
    csemU F ctx X XR i = csem F ctx X i := by
  funext uses w
  cases i with
  | call info => exact absurd rfl (hc info)
  | tryCall info ti => exact absurd rfl (ht info ti)
  | _ => rfl

/-- Where no callee raises, `csemU` is `csem`. -/
theorem csemU_none (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    csemU F ctx X XRaise.none = csem F ctx X := by
  funext i uses w
  cases i <;> rfl

/-- A call whose callee raises ends the activation. -/
theorem csemU_call_raise {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}
    {info : CallInfo} {uses : List CV} {w : Arm.ArmState} {obj : BitVec 64} {w' : Arm.ArmState}
    (h : XR.raise (callDest info) uses w = some (obj, w')) :
    csemU F ctx X XR (.call info) uses w = some (info.defs.map (fun _ => ofX 0), w', .halt) := by
  simp only [csemU, h]

/-- A supported `try_call` whose callee raises continues at its first handler with the
payload. -/
theorem csemU_try_raise {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}
    {info : CallInfo} {ti : TryInfo} {uses : List CV} {w : Arm.ArmState} {obj : BitVec 64}
    {w' : Arm.ArmState} (h : XR.raise (callDest info) uses w = some (obj, w'))
    (hok : tryUOk info ti = true) :
    csemU F ctx X XR (.tryCall info ti) uses w = some (payloadOuts info obj, w', .goto 0) := by
  simp only [csemU, h, hok, ite_true]

/-- A call whose callee does not raise steps as in `csem`. -/
theorem csemU_noRaise {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}
    {i : MInst} {uses : List CV} {w : Arm.ArmState}
    (h : ∀ info, (i = .call info ∨ ∃ ti, i = .tryCall info ti) →
      XR.raise (callDest info) uses w = Option.none) :
    csemU F ctx X XR i uses w = csem F ctx X i uses w := by
  cases i with
  | call info => simp only [csemU, h info (.inl rfl)]
  | tryCall info ti => simp only [csemU, h info (.inr ⟨ti, rfl⟩)]
  | _ => rfl

/-- `csemU` of a call depends on its callee descriptor, its defs' registers and `csem`. -/
theorem csemU_call_congr {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}
    {info info' : CallInfo} (hd : callDest info' = callDest info)
    (hf : info'.defs.map Prod.fst = info.defs.map Prod.fst)
    (hc : csem F ctx X (.call info') = csem F ctx X (.call info)) :
    csemU F ctx X XR (.call info') = csemU F ctx X XR (.call info) := by
  have hl : info'.defs.length = info.defs.length := by
    simpa using congrArg List.length hf
  funext uses w
  simp only [csemU, hd]
  split
  · simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    exact List.ext_getElem (by simp [hl]) (by simp)
  · rw [hc]

theorem payloadOuts_congr {info info' : CallInfo}
    (hf : info'.defs.map Prod.fst = info.defs.map Prod.fst) (obj : BitVec 64) :
    payloadOuts info' obj = payloadOuts info obj := by
  have : ∀ i : CallInfo, payloadOuts i obj =
      (i.defs.map Prod.fst).map (fun r => if r = .x 0 then ofX obj else ofX 0) := by
    intro i; simp [payloadOuts, List.map_map, Function.comp_def]
  rw [this, this, hf]

theorem tryUOk_congr {info info' : CallInfo} (ti : TryInfo)
    (hf : info'.defs.map Prod.fst = info.defs.map Prod.fst) :
    tryUOk info' ti = tryUOk info ti := by
  have : ∀ i : CallInfo, tryUOk i ti = (firstHandlerOk ti.handlers && !ti.clobberAll &&
      (i.defs.map Prod.fst).all fun r => r == .x 0 || r == .x 1) := by
    intro i; simp [tryUOk, List.all_map, Function.comp_def]
  rw [this, this, hf]

/-- `csemU` of a `tryCall` depends on its callee descriptor, its defs' registers, its
`tryUOk` and `csem`. -/
theorem csemU_try_congr {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}
    {info info' : CallInfo} {ti ti' : TryInfo} (hd : callDest info' = callDest info)
    (hf : info'.defs.map Prod.fst = info.defs.map Prod.fst)
    (ht : tryUOk info ti' = tryUOk info ti)
    (hc : csem F ctx X (.tryCall info' ti') = csem F ctx X (.tryCall info ti)) :
    csemU F ctx X XR (.tryCall info' ti') = csemU F ctx X XR (.tryCall info ti) := by
  funext uses w
  simp only [csemU, hd, payloadOuts_congr hf, tryUOk_congr ti' hf, ht]
  split
  · rfl
  · rw [hc]

/-- **`DriverSem` for `csemU`.** -/
theorem driverSem_csemU (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (XR : XRaise) :
    DriverSem (csemU F ctx X XR) where
  args := fun _ _ => rfl
  jump := fun _ _ => rfl
  rename := by
    intro g gn hg i
    have hc := (driverSem_csem F ctx X).rename g gn hg i
    cases i with
    | call info =>
      obtain ⟨dest, us, ds⟩ := info
      exact csemU_call_congr (by cases dest <;> rfl)
        (by simp [List.map_map, Function.comp_def]) hc
    | tryCall info ti =>
      obtain ⟨dest, us, ds⟩ := info
      exact csemU_try_congr (by cases dest <;> rfl)
        (by simp [List.map_map, Function.comp_def]) rfl hc
    | _ =>
      rw [csemU_of_not_call (by intro _ h; simp [MInst.mapRegs] at h)
          (by intro _ _ h; simp [MInst.mapRegs] at h),
        csemU_of_not_call (by intro _ h; cases h) (by intro _ _ h; cases h)]
      exact hc
  retarget := by
    intro i ls i' h
    have hc := (driverSem_csem F ctx X).retarget i ls i' h
    rcases setTargets_cases h with ⟨l, l', rfl, rfl⟩ | ⟨t, e, t', e', k, rfl, rfl⟩ |
      ⟨kd, t, e, t', e', rn, bit, rfl, rfl⟩ | ⟨d, ts, d', ts', r, t1, t2, rfl, rfl, hlen⟩ |
      ⟨info, ti, ti', rfl, rfl, hlen, hrets⟩
    · rfl
    · rfl
    · rfl
    · rw [csemU_of_not_call (by intro _ h; cases h) (by intro _ _ h; cases h),
        csemU_of_not_call (by intro _ h; cases h) (by intro _ _ h; cases h)]
      exact hc
    · have hti : tryUOk info ti' = tryUOk info ti := by
        simp only [MInst.setTargets] at h
        split at h
        · rename_i hl
          simp only [Option.some.injEq, MInst.tryCall.injEq] at h
          obtain ⟨-, rfl⟩ := h
          obtain ⟨c, hs, cl, r⟩ := ti
          simp only [beq_iff_eq] at hl
          cases hs with
          | nil => rfl
          | cons hd hs =>
            cases ls with
            | nil => simp at hl
            | cons l ls =>
              cases hd with
              | tag n l' => rcases n with _ | _ | n <;> rfl
              | default l' => rfl
        · cases h
      exact csemU_try_congr rfl rfl hti hc

/-! ## Non-vacuity -/

namespace UnwindSemWitness

/-- A `try_call` of `f` (x0 ← v0) with two results, a `tag 0` handler at block 1 and the
continuation at block 2. -/
def info : CallInfo := ⟨.sym "f", [(.vreg 0 .int, .x 0)], [(.x 0, .vreg 1 .int), (.x 1, .vreg 2 .int)]⟩
def ti : TryInfo := { continuation := 2, handlers := [.tag 0 1], rets := 2 }

/-- The callee raises object 77 from every world. -/
def XR : XRaise := ⟨fun _ _ w => some (77, w)⟩

theorem tryUOk_ok : tryUOk info ti = true := by decide

/-- The raising callee: the `try_call` continues at its handler with x0 = 77, x1 = 0. -/
theorem caught (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (w : Arm.ArmState) (uses : List CV) :
    csemU F ctx X XR (.tryCall info ti) uses w = some ([ofX 77, ofX 0], w, .goto 0) := by
  rw [csemU_try_raise (obj := 77) (w' := w) rfl tryUOk_ok]
  rfl

/-- A plain call of the raising callee ends the activation. -/
theorem exits (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (w : Arm.ArmState) (uses : List CV) :
    csemU F ctx X XR (.call info) uses w = some ([ofX 0, ofX 0], w, .halt) := by
  rw [csemU_call_raise (obj := 77) (w' := w) rfl]
  rfl

/-- A first `default` handler is not covered: no outcome. -/
theorem default_uncovered (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (w : Arm.ArmState)
    (uses : List CV) :
    csemU F ctx X XR (.tryCall info { ti with handlers := [.default 1] }) uses w = Option.none := by
  simp [csemU, XR, tryUOk, firstHandlerOk]

end UnwindSemWitness

end Backend.Proof
