import FV.Opt.Basic

/-!
# Zero-filled stack slots (SEM1, #537, `docs/plans/uninit.md` design B)

`Opt.zeroSlots f`: `f` with every byte of every explicit stack slot set to zero at the head of
its entry block, before its first instruction:

```
v_z64 = iconst.i64 0   v_z32 = iconst.i32 0   v_z16 = iconst.i16 0   v_z8 = iconst.i8 0
v_a   = stack_addr.i64 ssN
store notrap v_zW, v_a+off      -- one per 8/4/2/1-byte piece of the slot, largest first
```

`Clif.run` of `zeroSlots f` reads `0` where `f` reads a slot byte nobody wrote (on which `f`'s
run is `stuck`); otherwise the runs agree (the added statements only write slot bytes).
The fresh values are numbered above `Opt.maxValue f`.
-/

namespace Opt

open Clif

/-- The `(width, offset)` pieces covering `size` bytes, 8/4/2/1 bytes, largest first. -/
def zeroPieces (size : Nat) : List (Ty × Nat) :=
  let n8 := size / 8
  let r8 := size % 8
  let p8 := (List.range n8).map fun i => (Ty.i64, 8 * i)
  let o4 := 8 * n8
  let p4 := if r8 ≥ 4 then [(Ty.i32, o4)] else []
  let o2 := o4 + (if r8 ≥ 4 then 4 else 0)
  let r4 := r8 % 4
  let p2 := if r4 ≥ 2 then [(Ty.i16, o2)] else []
  let o1 := o2 + (if r4 ≥ 2 then 2 else 0)
  let p1 := if r4 % 2 = 1 then [(Ty.i8, o1)] else []
  p8 ++ p4 ++ p2 ++ p1

/-- The value holding zero of width `ty` (the four fresh constants `z`, `z+1`, `z+2`, `z+3`). -/
def zeroVal (z : ValueId) : Ty → ValueId
  | .i64 => z | .i32 => z + 1 | .i16 => z + 2 | _ => z + 3

/-- The statements zero-filling the slots `slots`; fresh values from `z`. -/
def zeroStmts (slots : List (SlotId × StackSlot)) (z : ValueId) : List Stmt :=
  let consts : List Stmt :=
    [{ results := [z], inst := .iconst .i64 0 }, { results := [z + 1], inst := .iconst .i32 0 },
     { results := [z + 2], inst := .iconst .i16 0 }, { results := [z + 3], inst := .iconst .i8 0 }]
  let perSlot : List Stmt := (slots.zipIdx).flatMap fun ((id, sl), k) =>
    let a := z + 4 + k
    { results := [a], inst := .stackAddr .i64 id 0 } ::
      (zeroPieces sl.size).map fun (ty, off) =>
        { inst := .store .store ty { trapCode := none } (zeroVal z ty) a off }
  consts ++ perSlot

/-- **`f` with zero-filled stack slots**: `zeroStmts` at the head of the entry block (unchanged
without slots or blocks). -/
def zeroSlots (f : Function) : Function :=
  if f.slots.isEmpty then f else
  match f.blocks with
  | [] => f
  | b :: bs => { f with blocks := { b with body := zeroStmts f.slots (maxValue f + 1) ++ b.body } :: bs }

end Opt
