module

import FV.E2E.RegLevelDriverSem
public import FV.Backend.Proof.RegallocCSem
import FV.Backend.Proof.IselInterp
public import FV.Backend.Proof.LowerContract
import FV.Arm.MinTheory

public section

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
    callee-saved registers (`clobberAll = false`), every def of the call is in x0 or x1
    (at most two ABI returns: the defs are then exactly the payload registers,
    `gen_try_call_rets`, so the handler edges keep no def the unwinder leaves unconstrained;
    every `try_call` of the fv-demo, survey and deps crates has at most two returns and a
    first `tag0` handler), and each of x0, x1 is clobbered by the call or a def's register
    (`payloadRegOk`: the allocated code keeps nothing live there, which the unwinder overwrites).
* `driverSem_csemU`: the driver's facts (`DriverSem`) hold for `csemU` as for `csem`.
-/

namespace Backend.Proof

open Backend Backend.Proof.Driver

/-- **The callees' exceptional results** (`ExtSem.call`'s counterpart). -/
structure XRaise where
  raise : Option String → List CV → Arm.ArmState → Option (BitVec 64 × Arm.ArmState)

/-- No callee raises. -/
@[expose] def XRaise.none : XRaise := ⟨fun _ _ _ => Option.none⟩

/-- The callee descriptor of a call (`ExtSem.call`'s first argument): the symbol of `bl`, `none`
for `blr`. -/
@[expose] def callDest (info : CallInfo) : Option String :=
  match info.dest with
  | .sym n => some n
  | .reg _ => none

/-- The constraints of the def operands of `i`, in operand order (`[]` if its operand view
fails). -/
@[expose] def defCons (i : MInst) : List Constraint :=
  match i.operands with
  | .ok ops => (ops.toList.filter Operand.isDef).map (·.con)
  | .error _ => []

/-- The values a landing pad finds in the defs of the call `i` (one per def operand, in operand
order): the exception object in x0, Rust's selector 0 in x1. -/
@[expose] def payloadOuts (i : MInst) (obj : BitVec 64) : List CV :=
  (defCons i).map fun c => if c = .fixed (.x 0) then ofX obj else ofX 0

/-- The first handler is a `tag 0` / `tag 1` handler. -/
@[expose] def firstHandlerOk : List TryHandler → Bool
  | .tag 0 _ :: _ | .tag 1 _ :: _ => true
  | _ => false

/-- After unwinding, register `r` (x0 or x1: the machine has x0 := the object, x1 := 0) holds
nothing the allocated code keeps live across the call: it is clobbered by the call or a def
operand's fixed register. -/
@[expose] def payloadRegOk (info : CallInfo) (ti : TryInfo) (r : Reg) : Bool :=
  (MInst.tryCall info ti).clobbers.contains r || (defCons (.call info)).contains (.fixed r)

/-- **The `try_call` shapes whose exceptional edge is covered**: first handler `tag 0`/`tag 1`,
callee-saved registers restored by the unwinder, every def operand fixed to x0 or x1, and each
of x0, x1 clobbered or a def's register (`payloadRegOk`). -/
@[expose] def tryUOk (info : CallInfo) (ti : TryInfo) : Bool :=
  firstHandlerOk ti.handlers && !ti.clobberAll &&
    (defCons (.call info)).all (fun c => c == .fixed (.x 0) || c == .fixed (.x 1)) &&
    payloadRegOk info ti (.x 0) && payloadRegOk info ti (.x 1)

/-- **The concrete instruction semantics with unwinding.** -/
@[expose] noncomputable def csemU (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (XR : XRaise) :
    ISem CV Arm.ArmState := fun i uses w =>
  match i with
  | .call info =>
    match XR.raise (callDest info) uses w with
    | some (_, w') => some ((defCons (.call info)).map (fun _ => ofX 0), w', .halt)
    | Option.none => csem F ctx X i uses w
  | .tryCall info ti =>
    match XR.raise (callDest info) uses w with
    | some (obj, w') =>
      if tryUOk info ti then some (payloadOuts (.call info) obj, w', .goto 0) else Option.none
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
    csemU F ctx X XR (.call info) uses w =
      some ((defCons (.call info)).map (fun _ => ofX 0), w', .halt) := by
  simp only [csemU, h]

/-- A supported `try_call` whose callee raises continues at its first handler with the
payload. -/
theorem csemU_try_raise {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}
    {info : CallInfo} {ti : TryInfo} {uses : List CV} {w : Arm.ArmState} {obj : BitVec 64}
    {w' : Arm.ArmState} (h : XR.raise (callDest info) uses w = some (obj, w'))
    (hok : tryUOk info ti = true) :
    csemU F ctx X XR (.tryCall info ti) uses w = some (payloadOuts (.call info) obj, w', .goto 0) := by
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

/-- `csemU` of a call depends on its callee descriptor, its def operands' constraints and
`csem`. -/
theorem csemU_call_congr {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}
    {info info' : CallInfo} (hd : callDest info' = callDest info)
    (hf : defCons (.call info') = defCons (.call info))
    (hc : csem F ctx X (.call info') = csem F ctx X (.call info)) :
    csemU F ctx X XR (.call info') = csemU F ctx X XR (.call info) := by
  funext uses w
  simp only [csemU, hd, hf]
  split
  · rfl
  · rw [hc]

/-- `csemU` of a `tryCall` depends on its callee descriptor, its def operands' constraints,
its clobbers, its `tryUOk` and `csem`. -/
theorem csemU_try_congr {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}
    {info info' : CallInfo} {ti ti' : TryInfo} (hd : callDest info' = callDest info)
    (hf : defCons (.call info') = defCons (.call info))
    (hcl : (MInst.tryCall info' ti').clobbers = (MInst.tryCall info ti').clobbers)
    (ht : tryUOk info ti' = tryUOk info ti)
    (hc : csem F ctx X (.tryCall info' ti') = csem F ctx X (.tryCall info ti)) :
    csemU F ctx X XR (.tryCall info' ti') = csemU F ctx X XR (.tryCall info ti) := by
  have hu : tryUOk info' ti' = tryUOk info ti' := by simp only [tryUOk, payloadRegOk, hf, hcl]
  funext uses w
  simp only [csemU, hd, payloadOuts, hf, hu, ht]
  split
  · rfl
  · rw [hc]

/-- Renaming the vregs keeps the def operands' constraints. -/
theorem defCons_mapRegs {g : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming g gn) (i : MInst) :
    defCons (i.mapRegs g) = defCons i := by
  unfold defCons
  rw [operands_mapRegs hg]
  cases i.operands with
  | error e => rfl
  | ok ops =>
    simp only [Except.map]
    simp [List.filter_map, Function.comp_def, Operand.isDef, rnOp]
    rfl

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
      exact csemU_call_congr (by cases dest <;> rfl) (defCons_mapRegs hg (.call ⟨dest, us, ds⟩)) hc
    | tryCall info ti =>
      obtain ⟨dest, us, ds⟩ := info
      exact csemU_try_congr (by cases dest <;> rfl) (defCons_mapRegs hg (.call ⟨dest, us, ds⟩))
        (by simp [MInst.clobbers, List.any_map, Function.comp_def]) rfl hc
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
      exact csemU_try_congr rfl rfl rfl hti hc

/-! ## Non-vacuity -/

namespace UnwindSemWitness

/-- A `try_call` of `f` (x0 ← v0) with two results, a `tag 0` handler at block 1 and the
continuation at block 2. -/
@[expose] def info : CallInfo := ⟨.sym "f", [(.vreg 0 .int, .x 0)], [(.x 0, .vreg 1 .int), (.x 1, .vreg 2 .int)]⟩
@[expose] def ti : TryInfo := { continuation := 2, handlers := [.tag 0 1], rets := 2 }

/-- The callee raises object 77 from every world. -/
@[expose] def XR : XRaise := ⟨fun _ _ w => some (77, w)⟩

theorem tryUOk_ok : tryUOk info ti = true := by decide

/-- A `try_call` with one result (x0): x1 is a clobber (`payloadRegOk`'s first case). -/
def info1 : CallInfo := ⟨.sym "f", [(.vreg 0 .int, .x 0)], [(.x 0, .vreg 1 .int)]⟩

theorem tryUOk_one : tryUOk info1 { ti with rets := 1 } = true := by decide

theorem payloadReg_x1_clobbered : (MInst.tryCall info1 { ti with rets := 1 }).clobbers.contains (.x 1) = true ∧
    (defCons (.call info1)).contains (.fixed (.x 1)) = false := by decide

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
