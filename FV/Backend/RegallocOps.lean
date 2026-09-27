import FV.Backend.StackAlloc

/-!
# Register-allocation operands and machine environment (M6)

The regalloc2 view of the backend's `MInst`s, transcribed from Cranelift 0.136.1
(`cranelift/codegen/src/`):

* **Operands** (`MInst.visitOperands`, `MInst.operands`): the register occurrences of an
  instruction in the order and with the kind/position/constraint of
  `isa/aarch64/inst/mod.rs` `aarch64_get_operands`, collected as `machinst/reg.rs`
  `OperandVisitorImpl` does: a real register in a plain operand is `reg_fixed_nonallocatable`
  (no operand; it must not be allocatable), `reg_use` = use/early/reg, `reg_def` =
  def/late/reg, `reg_early_def` = def/early/reg, `reg_fixed_use`/`reg_fixed_def` =
  fixed-register use (early) / def (late), `reg_reuse_def` = def/late/reuse.
  The same traversal substitutes the allocation (`MInst.assign`), so the operand list and
  the substitution cannot disagree about positions.
* **Clobbers** (`MInst.clobbers`): a call clobbers `DEFAULT_AAPCS_CLOBBERS`
  (`isa/aarch64/abi.rs`: x0–x17, v0–v31) minus the registers of its return values
  (`machinst/abi.rs` `gen_call_info` "Remove retval regs from clobbers").
* **Terminators** (`MInst.isRet`, `MInst.isBranch`, `MInst.targets`): `VCode::is_ret` (a
  `Rets`, or a trap `Udf` ending a block) and `is_branch` (`Jump`, `CondBr`,
  `TestBitAndBranch`, `JTSequence`).
* **Machine environment** (`aarch64Env`): `isa/aarch64/abi.rs` `create_reg_env(false)`
  (no pinned register): preferred x0–x15, v0–v7 and v16–v31; non-preferred x19–x28 (x21
  included because `enable_pinned_reg` is off), v8–v15; no scratch registers, no fixed stack
  slots. x16/x17 (spill temporaries), x18 (platform), x29 (fp), x30 (lr), sp/xzr are not
  allocatable.
* **CFG preparation** (`prepare`): drop blocks unreachable from the entry (as Cranelift's
  `BlockLoweringOrder` does) and split every critical edge with an edge block holding a
  `jump` (Cranelift splits all critical edges; regalloc2 requires it, `cfg.rs`).

Everything here is total.
-/

namespace Backend

inductive OpKind where
  | use | def
  deriving DecidableEq, Repr, Inhabited

inductive OpPos where
  | early | late
  deriving DecidableEq, Repr, Inhabited

/-- regalloc2 `OperandConstraint` (the variants this backend produces, plus `any`/`stack`). -/
inductive Constraint where
  | any | reg | stack
  | fixed (r : Reg)
  | reuse (idx : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- How a register occurrence is collected (`OperandVisitorImpl` method). -/
structure OpSpec where
  kind : OpKind
  pos : OpPos
  con : Constraint
  deriving DecidableEq, Repr, Inhabited

/-- A regalloc2 operand: vreg (number and class), kind, position, constraint. -/
structure Operand where
  vreg : Nat
  cls : RegClass
  kind : OpKind
  pos : OpPos
  con : Constraint
  deriving DecidableEq, Repr, Inhabited

namespace OpSpec
/-- `reg_use` -/
def use : OpSpec := ⟨.use, .early, .reg⟩
/-- `reg_def` -/
def def_ : OpSpec := ⟨.def, .late, .reg⟩
/-- `reg_early_def` -/
def earlyDef : OpSpec := ⟨.def, .early, .reg⟩
/-- `reg_fixed_use` -/
def fixedUse (p : Reg) : OpSpec := ⟨.use, .early, .fixed p⟩
/-- `reg_fixed_def` -/
def fixedDef (p : Reg) : OpSpec := ⟨.def, .late, .fixed p⟩
/-- `reg_reuse_def` -/
def reuseDef (i : Nat) : OpSpec := ⟨.def, .late, .reuse i⟩
end OpSpec

/-! ## Machine environment -/

/-- regalloc2 `MachineEnv` (int and float classes; the vector class is empty on aarch64). -/
structure MachineEnv where
  preferredInt : List Reg
  preferredFloat : List Reg
  nonPreferredInt : List Reg
  nonPreferredFloat : List Reg
  deriving Repr, Inhabited

/-- `create_reg_env(enable_pinned_reg = false)`, `isa/aarch64/abi.rs`. -/
def aarch64Env : MachineEnv where
  preferredInt := (List.range 16).map .x
  preferredFloat := (List.range 8).map .v ++ (List.range 16).map (fun i => .v (16 + i))
  nonPreferredInt := [19, 20, 22, 23, 24, 25, 26, 27, 28, 21].map .x
  nonPreferredFloat := (List.range 8).map fun i => .v (8 + i)

/-- A stress-test environment (not Cranelift's): x0–x7 (needed by fixed constraints), x19,
x20, v0–v3 and v8. It forces spills, reloads and callee-saved registers on small functions, to
exercise that code and the checker; the checker's allocatable set stays `aarch64Env`'s, of
which this is a subset. -/
def smallEnv : MachineEnv where
  preferredInt := (List.range 8).map .x
  preferredFloat := (List.range 4).map .v
  nonPreferredInt := [.x 19, .x 20]
  nonPreferredFloat := [.v 8]

def MachineEnv.allocatable (e : MachineEnv) : List Reg :=
  e.preferredInt ++ e.nonPreferredInt ++ e.preferredFloat ++ e.nonPreferredFloat

/-- Is `r` an allocatable register of `aarch64Env`? -/
def Reg.allocatable (r : Reg) : Bool := aarch64Env.allocatable.contains r

/-- The class of a real register (`x` = int, `v` = float). -/
def Reg.realClass? : Reg → Option RegClass
  | .x _ => some .int
  | .v _ => some .float
  | _ => none

/-- AAPCS64 callee-saved registers that the allocator may use (`is_reg_saved_in_prologue`):
x19–x28 and v8–v15 (only their low 64 bits are callee-saved; the frame saves all 128). -/
def calleeSaved : List Reg := (List.range 10).map (fun i => .x (19 + i)) ++ (List.range 8).map (fun i => .v (8 + i))

/-- `DEFAULT_AAPCS_CLOBBERS`: x0–x17, v0–v31. -/
def defaultAapcsClobbers : List Reg := (List.range 18).map .x ++ (List.range 32).map .v

/-! ## Operands -/

section
variable {m : Type → Type} [Monad m] (f : OpSpec → Reg → m Reg)

/-- `memarg_operands`: every register of an addressing mode is a `reg_use`. -/
def AMode.visit : AMode → m AMode
  | .regReg a b => do let a ← f .use a; let b ← f .use b; pure (.regReg a b)
  | .regScaled a b => do let a ← f .use a; let b ← f .use b; pure (.regScaled a b)
  | .regScaledExtended a b e => do
    let a ← f .use a; let b ← f .use b; pure (.regScaledExtended a b e)
  | .regExtended a b e => do let a ← f .use a; let b ← f .use b; pure (.regExtended a b e)
  | .unscaled a i => do pure (.unscaled (← f .use a) i)
  | .unsignedOffset a i => do pure (.unsignedOffset (← f .use a) i)
  | .regOffset a i => do pure (.regOffset (← f .use a) i)
  | am => pure am

def CondBrKind.visit : CondBrKind → m CondBrKind
  | .zero r s => do pure (.zero (← f .use r) s)
  | .notZero r s => do pure (.notZero (← f .use r) s)
  | .cond c => pure (.cond c)

/-- Visit the register occurrences of an instruction in `aarch64_get_operands` order, with
their operand spec; `f` returns the register to put in their place. -/
def MInst.visitOperands : MInst → m MInst
  | .aluRRR op s rd rn rm => do
    let rd ← f .def_ rd; let rn ← f .use rn; let rm ← f .use rm; pure (.aluRRR op s rd rn rm)
  | .aluRRRR op s rd rn rm ra => do
    let rd ← f .def_ rd; let rn ← f .use rn; let rm ← f .use rm; let ra ← f .use ra
    pure (.aluRRRR op s rd rn rm ra)
  | .aluRRImm12 op s rd rn i => do
    let rd ← f .def_ rd; let rn ← f .use rn; pure (.aluRRImm12 op s rd rn i)
  | .aluRRImmLogic op s rd rn i => do
    let rd ← f .def_ rd; let rn ← f .use rn; pure (.aluRRImmLogic op s rd rn i)
  | .aluRRImmShift op s rd rn i => do
    let rd ← f .def_ rd; let rn ← f .use rn; pure (.aluRRImmShift op s rd rn i)
  | .aluRRRShift op s rd rn rm sh => do
    let rd ← f .def_ rd; let rn ← f .use rn; let rm ← f .use rm
    pure (.aluRRRShift op s rd rn rm sh)
  | .aluRRRExtend op s rd rn rm e => do
    let rd ← f .def_ rd; let rn ← f .use rn; let rm ← f .use rm
    pure (.aluRRRExtend op s rd rn rm e)
  | .bitRR op s rd rn => do let rd ← f .def_ rd; let rn ← f .use rn; pure (.bitRR op s rd rn)
  | .load op rd mem fl => do
    let rd ← f .def_ rd; let mem ← AMode.visit f mem; pure (.load op rd mem fl)
  | .store op rd mem fl => do
    let rd ← f .use rd; let mem ← AMode.visit f mem; pure (.store op rd mem fl)
  | .mov s rd rm => do let rd ← f .def_ rd; let rm ← f .use rm; pure (.mov s rd rm)
  | .movWide op rd i s => do pure (.movWide op (← f .def_ rd) i s)
  | .movK rd rn i s => do
    -- `reg_use(rn); reg_reuse_def(rd, 0)`
    let rn ← f .use rn; let rd ← f (.reuseDef 0) rd; pure (.movK rd rn i s)
  | .extend rd rn sg a b => do
    let rd ← f .def_ rd; let rn ← f .use rn; pure (.extend rd rn sg a b)
  | .bitfieldMove s op rd rn a b => do
    let rd ← f .def_ rd; let rn ← f .use rn; pure (.bitfieldMove s op rd rn a b)
  | .cset rd c => do pure (.cset (← f .def_ rd) c)
  | .csel rd rn rm c => do
    -- `mod.rs:453`: `reg_def(rd); reg_use(rn); reg_use(rm)`
    let rd ← f .def_ rd; let rn ← f .use rn; let rm ← f .use rm; pure (.csel rd rn rm c)
  | .ccmp s rn rm n c => do let rn ← f .use rn; let rm ← f .use rm; pure (.ccmp s rn rm n c)
  | .ccmpImm s rn i n c => do pure (.ccmpImm s (← f .use rn) i n c)
  | .movToFpu rd rn s => do let rd ← f .def_ rd; let rn ← f .use rn; pure (.movToFpu rd rn s)
  | .movFromVec rd rn i s => do
    let rd ← f .def_ rd; let rn ← f .use rn; pure (.movFromVec rd rn i s)
  | .vecMisc op rd rn s => do let rd ← f .def_ rd; let rn ← f .use rn; pure (.vecMisc op rd rn s)
  | .vecLanes op rd rn s => do
    let rd ← f .def_ rd; let rn ← f .use rn; pure (.vecLanes op rd rn s)
  | .vecRRR op rd rn rm s => do
    let rd ← f .def_ rd; let rn ← f .use rn; let rm ← f .use rm; pure (.vecRRR op rd rn rm s)
  | .call info => do
    -- `CallInd`: `reg_use(dest)` first; then fixed uses, fixed defs (clobbers separately)
    let dest ← match info.dest with
      | .reg r => do pure (CallDest.reg (← f .use r))
      | d => pure d
    let uses ← info.uses.mapM fun (v, p) => do pure ((← f (.fixedUse p) v), p)
    let defs ← info.defs.mapM fun (p, v) => do pure (p, (← f (.fixedDef p) v))
    pure (.call ⟨dest, uses, defs⟩)
  | .args ds => do pure (.args (← ds.mapM fun (v, p) => do pure ((← f (.fixedDef p) v), p)))
  | .rets us => do pure (.rets (← us.mapM fun (v, p) => do pure ((← f (.fixedUse p) v), p)))
  | .jump l => pure (.jump l)
  | .condBr a b k => do pure (.condBr a b (← CondBrKind.visit f k))
  | .testBitAndBranch k a b rn bit => do pure (.testBitAndBranch k a b (← f .use rn) bit)
  | .trapIf k c => do pure (.trapIf (← CondBrKind.visit f k) c)
  | .udf c => pure (.udf c)
  | .jtSequence d ts ridx t1 t2 => do
    let ridx ← f .use ridx; let t1 ← f .earlyDef t1; let t2 ← f .earlyDef t2
    pure (.jtSequence d ts ridx t1 t2)
  | .loadExtNameGot rd n => do pure (.loadExtNameGot (← f .def_ rd) n)
  | .loadExtNameNear rd n o => do pure (.loadExtNameNear (← f .def_ rd) n o)
  | .loadAddr rd mem => do
    let rd ← f .def_ rd; let mem ← AMode.visit f mem; pure (.loadAddr rd mem)
  | .emitIsland n => pure (.emitIsland n)

end

/-- The regalloc2 operands of an instruction. A real register in an operand position is
Cranelift's `reg_fixed_nonallocatable` (no operand) and must not be allocatable. -/
def MInst.operands (i : MInst) : Except String (Array Operand) := do
  let collect (s : OpSpec) (r : Reg) : StateT (Array Operand) (Except String) Reg := do
    match r with
    | .vreg n cls => modify (·.push ⟨n, cls, s.kind, s.pos, s.con⟩); pure r
    | _ =>
      if r.allocatable then throw s!"allocatable real register {repr r} as an operand"
      else pure r
  let (_, ops) ← (MInst.visitOperands collect i).run #[]
  pure ops

/-- Substitute the allocation: the `k`-th vreg occurrence (the `k`-th operand) becomes
`regs[k]`; real registers stay. -/
def MInst.assign (i : MInst) (regs : Array Reg) : Except String MInst := do
  let put (_ : OpSpec) (r : Reg) : StateT Nat (Except String) Reg := do
    match r with
    | .vreg .. =>
      let k ← get
      set (k + 1)
      match regs[k]? with
      | some p => pure p
      | none => throw "fewer allocations than operands"
    | _ => pure r
  let (i', k) ← (MInst.visitOperands put i).run 0
  if k != regs.size then throw "more allocations than operands"
  pure i'

/-- Registers clobbered by the instruction (`inst_clobbers`). -/
def MInst.clobbers : MInst → List Reg
  | .call info => defaultAapcsClobbers.filter fun r => !(info.defs.any (·.1 == r))
  | _ => []

/-- `VCode::is_ret`: `Rets`, or a block-ending trap. -/
def MInst.isRet : MInst → Bool
  | .rets _ | .udf _ => true
  | _ => false

/-- `VCode::is_branch` (`MachTerminator::Branch`). -/
def MInst.isBranch : MInst → Bool
  | .jump _ | .condBr .. | .testBitAndBranch .. | .jtSequence .. => true
  | _ => false

/-- Successor labels of a branch, in successor order (`JTSequence`: default, then table). -/
def MInst.targets : MInst → List Label
  | .jump l => [l]
  | .condBr t e _ | .testBitAndBranch _ t e _ _ => [t, e]
  | .jtSequence d ts _ _ _ => d :: ts
  | _ => []

/-- Replace the successor labels (same count as `targets`). -/
def MInst.setTargets (i : MInst) (ls : List Label) : Option MInst :=
  match i, ls with
  | .jump _, [l] => some (.jump l)
  | .condBr _ _ k, [t, e] => some (.condBr t e k)
  | .testBitAndBranch k _ _ rn bit, [t, e] => some (.testBitAndBranch k t e rn bit)
  | .jtSequence _ ts ridx t1 t2, d :: ts' =>
    if ts'.length == ts.length then some (.jtSequence d ts' ridx t1 t2) else none
  | _, _ => none

/-! ## CFG -/

/-- Successor block indices (by label) and predecessor lists (one entry per edge) of every
block. Every block must end in a terminator. -/
def VCode.cfg (vc : VCode) : Except String (Array (Array Nat) × Array (Array Nat)) := do
  let idxOf (l : Label) : Except String Nat :=
    match vc.blocks.findIdx? (·.label == l) with
    | some i => pure i
    | none => throw s!"branch to unknown block {l}"
  let succs ← vc.blocks.mapM fun b => do
    let some t := b.insts.back? | throw s!"block {b.label} is empty"
    if !(t.isBranch || t.isRet) then throw s!"block {b.label} does not end in a terminator"
    t.targets.toArray.mapM idxOf
  let mut preds : Array (Array Nat) := Array.replicate vc.blocks.size #[]
  for (ss, i) in succs.zipIdx do
    for s in ss do
      preds := preds.modify s (·.push i)
  pure (succs, preds)

/-- Blocks reachable from the entry (block 0), by a fuel-bounded worklist. -/
def reachable (succs : Array (Array Nat)) : Array Bool := Id.run do
  let mut seen := Array.replicate succs.size false
  if succs.size == 0 then return seen
  seen := seen.set! 0 true
  let mut work : List Nat := [0]
  for _ in [0:succs.size + 1] do
    match work with
    | [] => break
    | b :: rest =>
      work := rest
      for s in succs[b]!.toList do
        if !seen[s]! then
          seen := seen.set! s true
          work := s :: work
  return seen

/-- Reverse postorder of the blocks reachable from block 0 (depth-first, successors in
order; fuel-bounded by the number of edges and blocks). -/
def rpo (succs : Array (Array Nat)) : Array Nat := Id.run do
  if succs.size == 0 then return #[]
  let mut seen := (Array.replicate succs.size false).set! 0 true
  let mut post : Array Nat := #[]
  -- stack of (block, index of the next successor to visit)
  let mut stack : List (Nat × Nat) := [(0, 0)]
  let fuel := succs.foldl (fun n s => n + s.size + 1) 1
  for _ in [0:fuel] do
    match stack with
    | [] => break
    | (b, i) :: rest =>
      match succs[b]![i]? with
      | some s =>
        stack := (b, i + 1) :: rest
        if !seen[s]! then
          seen := seen.set! s true
          stack := (s, 0) :: stack
      | none =>
        post := post.push b
        stack := rest
  return post.reverse

/-- Prepare VCode for regalloc2: drop unreachable blocks; split critical edges (an edge from a
block with several successor edges to a block with several predecessor edges) by an edge
block `jump target`; order the blocks in reverse postorder (Cranelift's
`BlockLoweringOrder` lowers in an RPO, and regalloc2's loop-depth estimate and checker assume
predecessors mostly come first). The entry block must not be a branch target (Cranelift's
verifier forbids it) and has no parameters. -/
def prepare (vc : VCode) : Except String VCode := do
  let (succs, _) ← vc.cfg
  let live := reachable succs
  let kept : Array VBlock := (vc.blocks.zip live).filterMap fun (b, l) => if l = true then some b else none
  let vc := { vc with blocks := kept }
  let (succs, preds) ← vc.cfg
  if !(preds[0]?.getD #[]).isEmpty then throw "the entry block is a branch target"
  if !(vc.blocks[0]?.map (fun (b : VBlock) => b.params.isEmpty)).getD true then throw "entry block has parameters"
  let mut next := (vc.blocks.foldl (fun m (b : VBlock) => max m b.label) 0) + 1
  let mut blocks : Array VBlock := #[]
  let mut edges : Array VBlock := #[]
  for (b, i) in vc.blocks.zipIdx do
    let ss := succs[i]!
    if ss.size < 2 then
      blocks := blocks.push b
      continue
    let some t := b.insts.back? | throw "empty block"
    let mut ls : Array Label := #[]
    for (s, l) in ss.zip t.targets.toArray do
      if preds[s]!.size > 1 then
        edges := edges.push { label := next, insts := #[.jump l] }
        ls := ls.push next
        next := next + 1
      else ls := ls.push l
    let some t' := t.setTargets ls.toList | throw "setTargets"
    blocks := blocks.push { b with insts := b.insts.pop.push t' }
  let vc := { vc with blocks := blocks ++ edges }
  let (succs, _) ← vc.cfg
  pure { vc with blocks := (rpo succs).map fun i => vc.blocks[i]! }

end Backend
