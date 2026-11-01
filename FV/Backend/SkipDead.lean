import FV.Backend.Proof.DriverCheck
import FV.Backend.RegallocCheck

/-!
# Unused instructions are not lowered (Cranelift's skip)

Cranelift lowers each block bottom-up and does not lower an instruction without lowering side
effects none of whose results the code lowered so far uses (`machinst/lower.rs`
`lower_clif_block`, `is_any_inst_result_needed`). Examples: the `icmp` whose boolean a
`brif`/`select` rule recomputes from the compared values (`lower.isle`
`lower_branch (brif (maybe_uextend (icmp ...)))`), the `ishl` a `bor` rule folds into a shifted
operand, an `iconst` only a folded immediate uses.

`skipDead f vc` deletes the segments of such statements from `lowerFunction f`'s VCode `vc`:

* a statement is a candidate if it is `skippable` and its segment is not empty;
* a candidate is kept if a vreg its segment writes is read by kept code (code outside the
  candidates, the branch arguments, the kept candidates): a backward fixpoint, Cranelift's demand;
* the other candidates' segments are deleted (`deleteWith`, with the mask `skipMask`), and the
  result is accepted only if `deleteCheck` holds: no kept instruction or branch argument reads a
  vreg that a deleted instruction writes, every block keeps its last instruction, and the CFG is
  unchanged. Otherwise `skipDead` returns `vc`.

The proof (`FV/Backend/Proof/LowerSimSkip.lean`) is at the CLIF level: a deleted statement is pure,
so the driver simulation steps over it without running any code.
-/

namespace Backend.Proof.Driver
open Backend

/-- The statements whose lowering is left out when nothing reads their results: Cranelift's
instructions without lowering side effects (`has_lowering_side_effect`, `inst_predicates.rs`)
among the driver's pure, non-trapping ones (`pureInst` without the float operations, whose
conversions trap). -/
def skippable : Clif.Inst → Bool
  | .iconst .. | .unary .. | .binary .. | .icmp .. | .extend .. | .ireduce .. | .select ..
  | .stackAddr .. => true
  | _ => false

/-- The vregs an instruction reads (`vuseNums`). -/
def useNums (m : MInst) : List Nat :=
  match m.operands with
  | .ok ops => (ops.toList.filter (·.kind == .use)).map (·.vreg)
  | .error _ => []

/-- The vregs an instruction writes (`vdefs`). -/
def defNums (m : MInst) : List Nat :=
  match m.operands with
  | .ok ops => (ops.toList.filter (·.kind == .def)).map (·.vreg)
  | .error _ => []

/-! ## Deleting instructions -/

/-- The instructions of `ms` at the `true` positions of `mask`. -/
def maskKeep (mask : List Bool) (ms : List MInst) : List MInst :=
  (ms.zip mask).filterMap fun (m, k) => if k then some m else none

/-- `vc` with the instructions of every block `b` masked by `mask b`. -/
def deleteWith (vc : VCode) (mask : Nat → List Bool) : VCode :=
  { vc with blocks := vc.blocks.mapIdx fun b vb =>
      { vb with insts := (maskKeep (mask b) vb.insts.toList).toArray } }

/-- The vregs the deleted instructions write. -/
def deadDefs (vc : VCode) (mask : Nat → List Bool) : List Nat :=
  vc.blocks.toList.zipIdx.flatMap fun (vb, b) =>
    (vb.insts.toList.zip (mask b)).flatMap fun (m, k) => if k then [] else defNums m

/-- Both CFGs compute and are equal. -/
def cfgSame (vc vc' : VCode) : Bool :=
  match vc.cfg, vc'.cfg with
  | .ok x, .ok y => x == y
  | _, _ => false

/-- An instruction the deletion may remove: not the entry's `args` pseudo-instruction and not a
GOT load (the code of a `skippable` statement contains neither; the completeness facts of the
pipeline keep both in place). -/
def skipDel : MInst → Bool
  | .args _ | .loadExtNameGot .. => false
  | _ => true

/-- **The deletion check**: every mask fits its block and keeps the block's last instruction,
every deleted instruction is `skipDel`, no kept instruction and no branch argument reads a vreg a
deleted instruction writes, and the CFG is unchanged. -/
def deleteCheck (vc : VCode) (mask : Nat → List Bool) : Bool :=
  let dead := deadDefs vc mask
  (vc.blocks.toList.zipIdx.all fun (vb, b) =>
    (mask b).length == vb.insts.size &&
    (vb.insts.size == 0 || (mask b).getLast? == some true) &&
    ((vb.insts.toList.zip (mask b)).all fun (m, k) =>
      if k then (useNums m).all (!dead.contains ·) else skipDel m) &&
    vb.branchArgs.toList.all fun r => match vregNum r with
      | .ok n => !dead.contains n
      | .error _ => true) &&
  cfgSame (deleteWith vc mask) vc

/-! ## Which statements to skip -/

section
variable (f : Clif.Function) (R : Reg → Reg) (bl : List BLow) (vc : VCode)

/-- **The mask of block `b`**: the entry code, the segments of the statements not in `drop`, and
the terminator's code are kept; a block without a CLIF block (an edge block) is kept whole. -/
def skipMask (drop : Nat → Nat → Bool) (b : Nat) : List Bool :=
  match f.blocks[b]? with
  | some B =>
    List.replicate (pre f R b).length true ++
      ((List.range B.body.length).map fun j =>
        List.replicate (seg f R bl b j).length (!drop b j)).flatten ++
      List.replicate (tseg R bl b).length true
  | none => List.replicate ((vc.blocks[b]?.map (·.insts.size)).getD 0) true

/-- A statement that may be skipped: its block, index, the vregs its segment writes and reads. -/
structure SkipCand where
  b : Nat
  j : Nat
  defs : List Nat
  uses : List Nat

/-- The candidates, last block and last statement first (Cranelift's bottom-up order). -/
def skipCands : List SkipCand :=
  ((List.range f.blocks.length).flatMap fun b => match f.blocks[b]? with
    | some B => (List.range B.body.length).filterMap fun j =>
      let ms := seg f R bl b j
      match B.body[j]? with
      | some stm => if skippable stm.inst && !ms.isEmpty then
          some ⟨b, j, ms.flatMap defNums, ms.flatMap useNums⟩ else none
      | none => none
    | none => []).reverse

/-- The vregs the code outside the candidates reads: the entry code, the other statements'
segments, the terminators' code, the edge blocks, and every branch argument. -/
def fixedUses (cands : List SkipCand) : Std.HashSet Nat :=
  let cs : Std.HashSet (Nat × Nat) := Std.HashSet.ofList (cands.map fun c => (c.b, c.j))
  let isCand (b j : Nat) : Bool := cs.contains (b, j)
  let code : List MInst := (List.range vc.blocks.size).flatMap fun b =>
    match f.blocks[b]? with
    | some B => pre f R b ++ ((List.range B.body.length).flatMap fun j =>
        if isCand b j then [] else seg f R bl b j) ++ tseg R bl b
    | none => ((vc.blocks[b]?.map (·.insts.toList)).getD [])
  let args : List Nat := vc.blocks.toList.flatMap fun vb =>
    vb.branchArgs.toList.filterMap fun r => match vregNum r with
      | .ok n => some n
      | .error _ => none
  Std.HashSet.ofList (code.flatMap useNums ++ args)

/-- One pass over the pending candidates: a candidate whose segment writes a needed vreg is kept
and its reads become needed. Returns the needed set, the still pending candidates (in order) and
whether a candidate was kept. -/
def keepPass (need : Std.HashSet Nat) (cands : List SkipCand) :
    Std.HashSet Nat × List SkipCand × Bool :=
  let (need, rest, changed) := cands.foldl (fun (need, rest, changed) c =>
    if c.defs.any need.contains then (c.uses.foldl (·.insert ·) need, rest, true)
    else (need, c :: rest, changed)) (need, [], false)
  (need, rest.reverse, changed)

/-- Passes until no candidate is kept (at most one per candidate). -/
def keepFix : Nat → Std.HashSet Nat → List SkipCand → List SkipCand
  | 0, _, cands => cands
  | fuel + 1, need, cands =>
    let (need, rest, changed) := keepPass need cands
    if changed then keepFix fuel need rest else rest

/-- The statements to skip, as a set of `(b, j)` (built once by `skipDeadImpl`). -/
def skipDropSet : Std.HashSet (Nat × Nat) :=
  let cands := skipCands f R bl
  let dropped := keepFix (cands.length + 1) (fixedUses f R bl vc cands) cands
  Std.HashSet.ofList (dropped.map fun c => (c.b, c.j))

/-- The statements to skip, as a table `drop b j`. -/
def skipDrops : Nat → Nat → Bool :=
  fun b j => (skipDropSet f R bl vc).contains (b, j)

end
/-- `skipAt f drop b j`: `drop b j`, for a `skippable` statement. -/
def skipAt (f : Clif.Function) (drop : Nat → Nat → Bool) (b j : Nat) : Bool :=
  drop b j && match f.blocks[b]? with
    | some B => match B.body[j]? with
      | some stm => skippable stm.inst
      | none => false
    | none => false

/-- **The skip of unused statements** on `lowerFunction f`'s VCode `vc` (the lowering re-run as
`lowerCheck` runs it); `vc` itself if the lowering does not re-run or the deletion check fails. -/
def skipDead (f : Clif.Function) (vc : VCode) : VCode :=
  match buildCtx f with
  | .error _ => vc
  | .ok (ctx, _, st0) =>
    match lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => vc
    | some bl =>
      let R := renOf (gnAt (gnTable st0.nextVreg (aliasOf f bl)))
      let mask := skipMask f R bl vc (skipAt f (skipDrops f R bl vc))
      if deleteCheck vc mask then deleteWith vc mask else vc

/-- `skipDead` as the compiler runs it (`skipDead_eq_impl`, `@[csimp]`): the set of skipped
statements is built once. Lean compiles the function-valued `skipDrops` at its full arity, so in
`skipDead` every `drop b j` query rebuilt the candidates and the fixpoint: quadratic in the
statements, hours on corpus/clif-regress/large_frame.clif (9,000 statements in one block). -/
def skipDeadImpl (f : Clif.Function) (vc : VCode) : VCode :=
  match buildCtx f with
  | .error _ => vc
  | .ok (ctx, _, st0) =>
    match lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => vc
    | some bl =>
      let R := renOf (gnAt (gnTable st0.nextVreg (aliasOf f bl)))
      let tbl := skipDropSet f R bl vc
      let mask := skipMask f R bl vc (skipAt f fun b j => tbl.contains (b, j))
      if deleteCheck vc mask then deleteWith vc mask else vc

@[csimp] theorem skipDead_eq_impl : @skipDead = @skipDeadImpl := rfl

end Backend.Proof.Driver
