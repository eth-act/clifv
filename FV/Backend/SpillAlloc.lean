import FV.Backend.RegallocCheck

/-!
# The spill allocator: register allocation without regalloc2 (V4)

`spillAlloc vc` is the allocation of last resort: the backend uses it when the checker
`checkAlloc` rejects regalloc2's allocation (`allocResult`, `allocateRegalloc2`) or when it is
forced (`lean-backend --regalloc spill`). It is a total Lean function `VCode → RFunc`, so the
end-to-end theorem never depends on regalloc2: every allocation the backend lowers is either
regalloc2's, accepted by `checkAlloc`, or this one (`E2E.backend_correct_final_alloc`).

## Design (route (a1) of `docs/TO-PROVE.md` V4)

The output is an ordinary `RFunc`, so `checkAlloc`, its soundness proof `checkAlloc_sound` and
every downstream proof (`lowerRFunc`, emission, layout, `backend_correct_final`) apply
unchanged; only the checker's acceptance of this particular allocation has to be shown. (Route
(a2), a direct proof of `StackAlloc.allocate`, would need a second simulation proof from the
VCode to an `AFunc` with its own frame layout, `Args`/`Rets`/call conventions and none of the
existing M6 machinery; `StackAlloc` also rejects the LL/SC loops, `try_call` and `tls_value`.)

* **Homes.** Every vreg `v` of class `c` lives in spill slot `v` of class `c`
  (`Loc.stack v c`). The slots past `spillTmpBase vc` hold the branch arguments of a `jump`
  during the parallel copy into the target's parameters.
* **Callee-saved registers.** All of them (`calleeSaved`) get a save slot: the entry block
  starts with `reg r → save r`, every `Rets` is preceded by `save r → reg r`. So the scratch
  registers may include x19–x28, and the fixed x24–x28 of the LL/SC loops need no special
  case.
* **One instruction** (`spillInst`): each operand gets a register (`spillLocs`): a fixed
  operand its register; a reuse operand the register of the operand it reuses; every other
  operand the next unused register of its class from `spillPool` minus the instruction's fixed
  registers and clobbers (so scratch registers are pairwise distinct, distinct from the fixed
  ones, and survive the clobbers). Then: a load `slot v → reg` for each use, the instruction, a
  store `reg → slot v` for each def the checker keeps (`MInst.keptDefs`). A terminator has no
  stores after it (the checker forbids code after the terminator): the defs of a `try_call`
  that are live on an edge are stored at the start of the successor (`spillEntryStores`), which
  is its only predecessor's edge block (`prepare` splits critical edges).
* **Block arguments** (`spillArgMoves`): before the `jump` of a block with branch arguments,
  every argument is copied into a temporary slot (`spillTmpBase + i`), then every temporary into
  the target parameter's home: a parallel copy, safe when arguments and parameters overlap.
  Each copy goes through register x9 (int) or v16 (float) (`spillScratch`): memory-to-memory
  moves do not exist.

Nothing is live in a register between instructions, except a `try_call`'s results until the
successor's first items store them.

## What is proven

`E2E.backend_correct_final_alloc` (`FV/E2E/AllocDirect.lean`) composes this fallback with
regalloc2. The spill allocation's acceptance by `checkAlloc` on every function the pipeline
produces from in-scope input (`SpillAccepted`) is an explicit hypothesis there; `lean-e2e-check`
decides it on every in-scope function of the corpus and the runtests ("spill fallback" line).
-/

namespace Backend

/-- The home of vreg `v` of class `c`. -/
def spillHome (v : Nat) (c : RegClass) : Loc := .stack v c

/-- Scratch registers of a class, in allocation order: the caller-saved registers first, then
the callee-saved ones (all of which the spill allocation saves). -/
def spillPool : RegClass → List Reg
  | .int => (List.range 16).map .x ++ [19, 20, 21, 22, 23, 24, 25, 26, 27, 28].map .x
  | .float => (List.range 32).map .v

/-- The register a block argument is copied through. -/
def spillScratch : RegClass → Reg
  | .int => .x 9
  | .float => .v 16

/-- The fixed registers of an instruction's operands. -/
def fixedRegs (ops : Array Operand) : List Reg :=
  ops.toList.filterMap fun o => match o.con with
    | .fixed p => some p
    | _ => none

/-- The locations of an instruction's operands: fixed operands in their register, every other
non-reuse operand in a fresh register of its class (`spillPool` minus the fixed registers and the
clobbers), then every reuse operand in its reused operand's location. Running out of registers
gives an invalid location (`Loc.reg .sp`), which the checker rejects. -/
def spillLocs (ops : Array Operand) (clob : List Reg) : Array Loc :=
  let avoid := fixedRegs ops ++ clob
  let free (c : RegClass) := (spillPool c).filter fun r => !avoid.contains r
  let step := fun (st : Array Loc × List Reg × List Reg) (o : Operand) =>
    let (acc, is, fs) := st
    match o.con with
    | .fixed p => (acc.push (.reg p), is, fs)
    | .reuse _ => (acc.push (.reg .sp), is, fs)
    | _ => match o.cls with
      | .int => match is with
        | r :: rest => (acc.push (.reg r), rest, fs)
        | [] => (acc.push (.reg .sp), is, fs)
      | .float => match fs with
        | r :: rest => (acc.push (.reg r), is, rest)
        | [] => (acc.push (.reg .sp), is, fs)
  let base := (ops.foldl step (#[], free .int, free .float)).1
  (ops.zip base).map fun (o, l) => match o.con with
    | .reuse i => base[i]?.getD (.reg .sp)
    | _ => l

/-- The defs of an instruction (with their locations) whose values the checker keeps after it
(`MInst.keptDefs`). -/
def keptPairs (i : MInst) (pairs : List (Operand × Loc)) : List (Operand × Loc) :=
  let defs := pairs.filter (·.1.kind == .def)
  match i.keptDefs with
  | none => defs
  | some n => defs.take n

/-- Saves of every callee-saved register (start of the entry block). -/
def spillSaves : List RItem := calleeSaved.map fun r => .move (.reg r) (.save r)

/-- Restores of every callee-saved register (before a `Rets`). -/
def spillRestores : List RItem := calleeSaved.map fun r => .move (.save r) (.reg r)

/-- The items of instruction `k` (`i`): loads of its uses, the instruction, stores of its kept
defs (none after a terminator); restores before a `Rets`. -/
def spillInst (k : Nat) (i : MInst) : List RItem :=
  match i.operands with
  | .error _ => [.op k #[]]
  | .ok ops =>
    let locs := spillLocs ops i.clobbers
    let pairs := (ops.zip locs).toList
    let loads := (pairs.filter (·.1.kind == .use)).map fun (o, l) => RItem.move (spillHome o.vreg o.cls) l
    let stores := if i.isTerminator then [] else
      (keptPairs i pairs).map fun (o, l) => RItem.move l (spillHome o.vreg o.cls)
    let restores := match i with
      | .rets _ => spillRestores
      | _ => []
    restores ++ loads ++ [.op k locs] ++ stores

/-- The class of a register (`int` for a non-vreg). -/
def Reg.homeCls : Reg → RegClass
  | .vreg _ c => c
  | .v _ => .float
  | _ => .int

/-- The vreg number of a register (`0` for a real one). -/
def Reg.homeNum : Reg → Nat
  | .vreg n _ => n
  | _ => 0

/-- The first slot past every vreg home: the largest vreg number of operands, parameters and
branch arguments, plus one (at least the class table's size). -/
def spillTmpBase (vc : VCode) : Nat :=
  let regs (b : VBlock) : List Reg :=
    b.params.toList ++ b.branchArgs.toList ++ b.insts.toList.flatMap fun i =>
      match i.operands with
      | .ok ops => ops.toList.map fun o => Reg.vreg o.vreg o.cls
      | .error _ => []
  vc.blocks.foldl (fun m b => (regs b).foldl (fun m r => max m (r.homeNum + 1)) m) vc.classes.size

/-- The parallel copy of block `b`'s branch arguments into the parameters of its target `t`:
arguments into temporaries, then temporaries into the parameters' homes. -/
def spillArgMoves (tmp : Nat) (vb tb : VBlock) : List RItem :=
  let ps := (vb.branchArgs.toList.zip tb.params.toList).zipIdx
  let phase1 := ps.flatMap fun ((a, _), i) =>
    let c := a.homeCls
    [RItem.move (spillHome a.homeNum c) (.reg (spillScratch c)),
     .move (.reg (spillScratch c)) (spillHome (tmp + i) c)]
  let phase2 := ps.flatMap fun ((_, p), i) =>
    let c := p.homeCls
    [RItem.move (spillHome (tmp + i) c) (.reg (spillScratch c)),
     .move (.reg (spillScratch c)) (spillHome p.homeNum c)]
  phase1 ++ phase2

/-- The defs (with their locations) of block `b`'s terminator that are live on the edge to
successor number `j` and not stored yet: a `try_call`'s results (and, on a handler edge, its
payload), which live in their fixed registers. -/
def termEdgeDefs (vb : VBlock) (j : Nat) : List (Operand × Loc) :=
  match vb.insts.back? with
  | none => []
  | some i =>
    if !i.isTerminator then [] else
    match i.operands with
    | .error _ => []
    | .ok ops =>
      let kept := keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList
      match i.normalDead with
      | some (jn, n) => if j == jn then kept.take n else kept
      | none => kept

/-- Stores at the start of block `s` of the terminator defs live on the edge from its only
predecessor (none if `s` has several predecessors or none). -/
def spillEntryStores (vc : VCode) (succs preds : Array (Array Nat)) (s : Nat) : List RItem :=
  match preds[s]? with
  | some #[b] =>
    match vc.blocks[b]?, succs[b]? with
    | some vb, some ss =>
      match ss.toList.idxOf? s with
      | some j => (termEdgeDefs vb j).map fun (o, l) => RItem.move l (spillHome o.vreg o.cls)
      | none => []
    | _, _ => []
  | _ => []

/-- The spill allocation of a (prepared) VCode. -/
def spillAlloc (vc : VCode) : RFunc :=
  let (succs, preds) := match vc.cfg with
    | .ok sp => sp
    | .error _ => (#[], #[])
  let tmp := spillTmpBase vc
  let maxArgs := vc.blocks.foldl (fun m b => max m b.branchArgs.size) 0
  let blocks := vc.blocks.mapIdx fun bi vb =>
    let n := vb.insts.size
    let body := (vb.insts.toList.zipIdx).flatMap fun (i, k) =>
      let moves := if k + 1 == n && !vb.branchArgs.isEmpty then
        match succs[bi]? with
        | some #[t] => match vc.blocks[t]? with
          | some tb => spillArgMoves tmp vb tb
          | none => []
        | _ => []
      else []
      moves ++ spillInst k i
    let pre := (if bi == 0 then spillSaves else []) ++ spillEntryStores vc succs preds bi
    (pre ++ body).toArray
  { blocks, spillSlots := tmp + maxArgs, saved := calleeSaved }

/-- The allocation the backend lowers: regalloc2's (`ra`) if `checkAlloc` accepts it, else the
spill allocation. -/
def allocResult (vc : VCode) (ra : Except String RFunc) : RFunc :=
  match ra with
  | .ok rf => if (checkAlloc vc rf).isOk then rf else spillAlloc vc
  | .error _ => spillAlloc vc

end Backend
