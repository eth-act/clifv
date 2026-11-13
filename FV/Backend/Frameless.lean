import FV.Backend.StackAlloc

/-!
# Frameless leaves: Cranelift's `preserve_frame_pointers=false` (#1028)

`lowerRFunc` gives every function a frame (`AFunc.frame = true`: `stp x29, x30, [sp, #-16]!`,
`mov x29, sp` … `ldp x29, x30, [sp], #16`). Cranelift sets one up only when it needs one or
`preserve_frame_pointers` is set: `compute_frame_layout`, `cranelift/codegen/src/isa/aarch64/abi.rs:1265-1278`
at the pinned wasmtime commit (`46c23a87`):

```
needs_linkage_frame = preserve_frame_pointers || incoming_args_size > 0
  || tail_args_size > incoming_args_size || clobber_size > 0
  || fixed_frame_storage_size > 0 || outgoing_args_size > 0
setup_area_size = if needs_linkage_frame || function_calls == Regular { 16 } else { 0 }
```

`frameRequired vc af` states that decision on the compiler's objects (`vc` the VCode handed to
the allocator, `af` the allocated function): a frame size or a slot area (`fixed_frame_storage_size`,
`clobber_size`: `frameSize` counts the callee-saved area), a call (`function_calls`, and the
outgoing arguments), an incoming stack argument (`incoming_args_size`: the loads from
`fpOffset`/`incomingArg`, in `vc` because allocation may drop an unused one), or a use of `x29`/`x30`.
`frameless pfp vc af` drops the frame exactly when `pfp` (`preserve_frame_pointers`) is off and
no frame is required. It changes nothing else: `prologue` then emits no line and `epilogueRet`
only `ret` (`ainstLines`). The comparison checks the decision against stock's bytes on every
filetest (`scripts/stock-compiler-compare.py`).
-/

namespace Backend

/-- An instruction that needs the frame: a call (or the TLS descriptor call), an access to the
incoming arguments or through the frame pointer, or a use or def of `x29`/`x30`. -/
def touchesFrame (m : MInst) : Bool :=
  (m.uses ++ m.defs).any (fun r => r == .x 29 || r == .x 30) ||
  match m with
  | .call .. | .tryCall .. | .elfTlsGetAddr .. => true
  | .load _ _ (.fpOffset _) _ | .store _ _ (.fpOffset _) _ | .loadAddr _ (.fpOffset _)
  | .load _ _ (.incomingArg _) _ | .store _ _ (.incomingArg _) _
  | .loadAddr _ (.incomingArg _) | .fpuLoad _ _ (.fpOffset _) _ | .fpuStore _ _ (.fpOffset _) _
  | .fpuLoad _ _ (.incomingArg _) _ | .fpuStore _ _ (.incomingArg _) _ => true
  | _ => false

/-- The allocated function's part of the decision: no frame size, no slot area, no callee saves,
and no instruction that touches the frame. Only this part matters for the correctness of a
frameless function (the end-to-end theorems' premise); the rest of `frameRequired` only makes the
compiler keep more frames, as stock does. -/
def leafB (af : AFunc) : Bool :=
  af.frameSize == 0 && af.slotBase == 0 && af.saves.isEmpty &&
    af.blocks.all (fun (_, code) => code.all fun | .inst m => !touchesFrame m | _ => true)

/-- **Stock's frame decision** (`abi.rs:1265-1278`, see the module doc) without
`preserve_frame_pointers`: the function needs a frame. -/
def frameRequired (vc : VCode) (af : AFunc) : Bool :=
  !leafB af || vc.blocks.any (fun b => b.insts.any touchesFrame)

/-- **`preserve_frame_pointers`** (`pfp`): with it, or when the function needs a frame, `af`
unchanged; otherwise `af` without its frame. -/
def frameless (pfp : Bool) (vc : VCode) (af : AFunc) : AFunc :=
  if pfp || frameRequired vc af then af else { af with frame := false }

/-- With `preserve_frame_pointers` the allocated function is unchanged. -/
@[simp] theorem frameless_true (vc : VCode) (af : AFunc) : frameless true vc af = af := by
  simp [frameless]

/-- `frameless` gives `af` or `af` without its frame, and only a leaf (`leafB`) loses it. -/
theorem frameless_cases (pfp : Bool) (vc : VCode) (af : AFunc) :
    frameless pfp vc af = af ∨ (frameless pfp vc af = { af with frame := false } ∧ leafB af = true) := by
  unfold frameless
  by_cases h : (pfp || frameRequired vc af) = true
  · exact .inl (by simp [h])
  · refine .inr ⟨by simp [h], ?_⟩
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, frameRequired] at h
    simpa using h.2.1

end Backend
