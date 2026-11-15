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

/-- **Stock's frame decision** (`abi.rs:1265-1278`, see the module doc) without
`preserve_frame_pointers`: the function needs a frame. -/
def frameRequired (vc : VCode) (af : AFunc) : Bool :=
  af.frameSize != 0 || af.slotBase != 0 || !af.saves.isEmpty ||
    af.blocks.any (fun (_, code) => code.any fun | .inst m => touchesFrame m | _ => false) ||
    vc.blocks.any (fun b => b.insts.any touchesFrame)

/-- **`preserve_frame_pointers`** (`pfp`): with it, or when the function needs a frame, `af`
unchanged; otherwise `af` without its frame. -/
def frameless (pfp : Bool) (vc : VCode) (af : AFunc) : AFunc :=
  if pfp || frameRequired vc af then af else { af with frame := false }

/-- With `preserve_frame_pointers` the allocated function is unchanged. -/
@[simp] theorem frameless_true (vc : VCode) (af : AFunc) : frameless true vc af = af := by
  simp [frameless]

/-- A function `frameless` leaves without a frame had one only because the compiler always sets one
up: the setting is off and the function needs none. -/
theorem frameless_frame_false {pfp : Bool} {vc : VCode} {af : AFunc} (haf : af.frame = true)
    (h : (frameless pfp vc af).frame = false) :
    pfp = false ∧ frameRequired vc af = false := by
  unfold frameless at h
  cases pfp <;> cases hr : frameRequired vc af <;> simp_all

end Backend
