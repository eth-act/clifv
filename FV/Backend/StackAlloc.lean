import FV.Backend.Isel

/-!
# Stack-slot "register allocation" and frame layout (PLAN.md M4)

Every virtual register lives in its own frame slot. Around each instruction, the vregs it
reads are loaded into scratch registers, the instruction runs on the scratch registers, and
the vregs it writes are stored back. No value stays in a register across instructions.

**Scratch registers.** Integer vregs use `x9..x15`, float/vector vregs `v16..v31`
(caller-saved temporaries of AAPCS64 that are never argument, return, or callee-saved
registers). `x16`/`x17` stay reserved as address temporaries, as in Cranelift
(`spilltmp_reg`, `tmp2_reg`): large slot offsets are materialised in `x16`. The spill code is
`ldr`/`str` plus, for large offsets, `movz`/`movk`, none of which touch NZCV, so flags set by
one instruction are still valid in the next (`cmp` then `b.cond`, `cmp` then `JTSequence`).
Because nothing is live in a register between instructions, no callee-saved register is ever
written and none is saved.

**Frame layout** (addresses grow upwards; `sp` is 16-byte aligned at every instruction):

```
  fp + 16 + off     incoming stack arguments (AAPCS64: from the caller's sp upwards)
  fp + 8            saved lr (x30)
  fp                saved fp (x29)                         <- x29
  ...               padding to 16
  sp + spill + ...  vreg slots: float/vector vregs (16 bytes, 16-aligned), then int (8)
  sp + outgoing     explicit CLIF stack slots (`slotLayout`, Cranelift's order and alignment)
  sp                outgoing stack arguments of calls (max over all calls) <- sp
```

Prologue `stp x29, x30, [sp, #-16]!; mov x29, sp; sub sp, sp, #size`; epilogue
`mov sp, x29; ldp x29, x30, [sp], #16; ret`.

**Special instructions.** `args` stores the argument registers into the parameters' slots;
`rets` loads the return registers from slots, then runs the epilogue; `call` loads argument
registers (and, for `blr`, the target into `x9`) from slots, calls, and stores the return
registers; `movK` (whose `rd` and `rn` are tied) loads `rn` into `rd`'s scratch register.
Terminators have no stores after them (their only defs, the `JTSequence` temporaries, are
dead).
-/

namespace Backend

/-- An instruction after allocation. `inst` holds only real registers. -/
inductive AInst where
  | inst (m : MInst)
  /-- `stp x29, x30, [sp, #-16]!; mov x29, sp; sub sp, sp, #frameSize` -/
  | prologue
  /-- `mov sp, x29; ldp x29, x30, [sp], #16; ret` -/
  | epilogueRet
  deriving Repr, Inhabited, BEq

/-- An allocated function. -/
structure AFunc where
  name : String
  frameSize : Nat
  /-- `(label, code)` in emission order; the first block is the entry. -/
  blocks : Array (Label × Array AInst)
  /-- Offset of the explicit stack-slot region from `sp` (= the outgoing area size). -/
  slotBase : Nat
  /-- `false`: no frame at all (a leaf function with an empty frame that never addresses
  `fp`): `prologue` emits nothing and `epilogueRet` only `ret`, as Cranelift does when
  `preserve_frame_pointers` is off. -/
  frame : Bool := true
  deriving Inhabited

/-- Frame layout: slot offset (from `sp`) of every vreg, and the frame size. -/
structure Frame where
  outgoing : Nat
  vregOff : Array Nat
  size : Nat
  deriving Inhabited

def Frame.compute (vc : VCode) : Frame :=
  let outgoing := vc.outgoing
  let spillStart := alignTo (outgoing + vc.slotBytes) 16
  let nf := (vc.classes.filter (· == .float)).size
  let floatEnd := spillStart + 16 * nf
  -- assign in vreg order: floats in the float area, ints after it
  let (offs, _, intEnd) := vc.classes.foldl (init := (#[], spillStart, floatEnd))
    fun (acc, fo, io) cls => match cls with
      | .float => (acc.push fo, fo + 16, io)
      | .int => (acc.push io, fo, io + 8)
  { outgoing, vregOff := offs, size := alignTo intEnd 16 }

def intScratch : List Reg := [.x 9, .x 10, .x 11, .x 12, .x 13, .x 14, .x 15]
def floatScratch : List Reg := (List.range 16).map fun i => .v (16 + i)

/-- Spill load/store of a vreg's slot. -/
def slotLoad (cls : RegClass) (r : Reg) (off : Nat) : MInst :=
  match cls with
  | .int => .load .uload64 r (.spOffset off) trustedFlags
  | .float => .load .fpuLoad128 r (.spOffset off) trustedFlags

def slotStore (cls : RegClass) (r : Reg) (off : Nat) : MInst :=
  match cls with
  | .int => .store .store64 r (.spOffset off) trustedFlags
  | .float => .store .fpuStore128 r (.spOffset off) trustedFlags

section
variable (fr : Frame)

def Frame.slotOf (r : Reg) : Except String (RegClass × Nat) :=
  match r with
  | .vreg n cls => match fr.vregOff[n]? with
    | some off => pure (cls, off)
    | none => throw s!"vreg {n} has no slot"
  | _ => throw "not a virtual register"

/-- Assign scratch registers to the distinct vregs of `regs`. -/
def assignScratch (regs : List Reg) : Except String (List (Reg × Reg)) := do
  let vs := (regs.filter Reg.isVirtual).eraseDups
  let (asg, _, _) ← vs.foldlM (init := (([] : List (Reg × Reg)), intScratch, floatScratch))
    fun (acc, ints, floats) r => match r with
      | .vreg _ .int => match ints with
        | s :: rest => pure (acc ++ [(r, s)], rest, floats)
        | [] => throw "out of integer scratch registers"
      | .vreg _ .float => match floats with
        | s :: rest => pure (acc ++ [(r, s)], ints, rest)
        | [] => throw "out of float scratch registers"
      | _ => pure (acc, ints, floats)
  pure asg

/-- Loads of `pairs` (vreg ↦ register). -/
def Frame.loads (pairs : List (Reg × Reg)) : Except String (List AInst) :=
  pairs.mapM fun (v, p) => do
    let (cls, off) ← fr.slotOf v
    pure (.inst (slotLoad cls p off))

def Frame.stores (pairs : List (Reg × Reg)) : Except String (List AInst) :=
  pairs.mapM fun (v, p) => do
    let (cls, off) ← fr.slotOf v
    pure (.inst (slotStore cls p off))

/-- Allocate one instruction. -/
def Frame.allocInst (m : MInst) : Except String (List AInst) := do
  let virt (ps : List (Reg × Reg)) := ps.filter (·.1.isVirtual)
  match m with
  -- the LL/SC pseudo-instructions write fixed registers (x24–x28); the stack-slot
  -- allocator has no fixed-register support (`Constraint.fixed`), so a function using
  -- them keeps cg_clif's code (regalloc2, the default, handles them)
  | .atomicRmwLoop .. | .atomicCasLoop .. => throw s!"atomic loop with the stack-slot allocator"
  | .args ds =>
    fr.stores (virt ds)
  | .rets us =>
    let ls ← fr.loads (virt us)
    let reals := (us.filter (!·.1.isVirtual)).map fun (r, p) => AInst.inst (.mov .size64 p r)
    pure (ls ++ reals ++ [.epilogueRet])
  | .call info =>
    let argLoads ← fr.loads (virt info.uses)
    let (dest, destLoads) ← match info.dest with
      | .reg r@(.vreg ..) => do pure (CallDest.reg (.x 9), ← fr.loads [(r, .x 9)])
      | d => pure (d, [])
    let retStores ← fr.stores ((info.defs.map fun (p, v) => (v, p)).filter (·.1.isVirtual))
    pure (argLoads ++ destLoads ++ [.inst (.call ⟨dest, info.uses.map (fun (_, p) => (p, p)),
      info.defs.map (fun (p, _) => (p, p))⟩)] ++ retStores)
  | .movK rd rn imm sz =>
    match rd, rn with
    | .vreg .., _ =>
      let s := Reg.x 9
      let pre ← if rn.isVirtual then fr.loads [(rn, s)] else pure [.inst (.mov .size64 s rn)]
      let post ← fr.stores [(rd, s)]
      pure (pre ++ [.inst (.movK s s imm sz)] ++ post)
    | _, _ => if rd == rn then pure [.inst m] else throw "movK with distinct real registers"
  | _ =>
    let asg ← assignScratch (m.uses ++ m.defs)
    let f (r : Reg) : Reg := (asg.lookup r).getD r
    let used := asg.filter fun (v, _) => m.uses.contains v
    let defd := asg.filter fun (v, _) => m.defs.contains v
    let ls ← fr.loads used
    let ss ← if m.isTerm then pure [] else fr.stores defd
    pure (ls ++ [.inst (m.mapRegs f)] ++ ss)

end

/-- Block arguments as moves (the stack-slot allocator has no block parameters): before a
`jump` with arguments, every argument is copied into a fresh temporary, then every temporary
into the target's parameter (a parallel copy, safe when arguments and parameters overlap). -/
def lowerBlockArgs (vc : VCode) : Except String VCode := do
  let mut classes := vc.classes
  let mut blocks : Array VBlock := #[]
  for b in vc.blocks do
    if b.branchArgs.isEmpty then
      blocks := blocks.push b
      continue
    let some (.jump tl) := b.insts.back? | throw s!"block {b.label}: arguments without a jump"
    let some tb := vc.blocks.find? (·.label == tl) | throw s!"unknown block {tl}"
    if tb.params.size != b.branchArgs.size then throw s!"block {tl}: argument count"
    let mut first : Array MInst := #[]
    let mut second : Array MInst := #[]
    for (a, p) in b.branchArgs.zip tb.params do
      let cls := match p with
        | .vreg _ c => c
        | _ => .int
      let t := Reg.vreg classes.size cls
      classes := classes.push cls
      first := first.push (.mov .size64 t a)
      second := second.push (.mov .size64 p t)
    blocks := blocks.push { b with insts := b.insts.pop ++ first ++ second ++ #[.jump tl],
                                   branchArgs := #[] }
  pure { vc with blocks, classes }

/-- Allocate a function. -/
def allocate (vc : VCode) : Except String AFunc := do
  let vc ← lowerBlockArgs vc
  let fr := Frame.compute vc
  let blocks ← vc.blocks.mapIdxM fun i b => do
    let code ← b.insts.toList.flatMapM fr.allocInst
    let code := if i == 0 then AInst.prologue :: code else code
    pure (b.label, code.toArray)
  pure { name := vc.name, frameSize := fr.size, blocks, slotBase := vc.outgoing }

end Backend
